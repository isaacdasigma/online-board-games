const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const { Chess } = require('chess.js');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

// ==========================================
// 1. PERSISTENT SEQUENTIAL GUEST ACCOUNTS
// ==========================================
const GUEST_FILE = path.join(__dirname, 'guests.json');
let guestStore = { nextId: 1, users: {} };

if (fs.existsSync(GUEST_FILE)) {
  guestStore = JSON.parse(fs.readFileSync(GUEST_FILE, 'utf8'));
}

function saveGuests() {
  fs.writeFileSync(GUEST_FILE, JSON.stringify(guestStore, null, 2));
}

function authenticateGuest(token) {
  if (token && guestStore.users[token]) {
    return { token, username: guestStore.users[token].username };
  }
  const newToken = crypto.randomUUID();
  const username = `guest${guestStore.nextId++}`;
  guestStore.users[newToken] = { username, createdAt: Date.now() };
  saveGuests();
  return { token: newToken, username };
}

// ==========================================
// 2. MODULAR GAME ENGINES
// ==========================================
const GAMES = {
  // --- CONNECT 4 ---
  connect4: {
    init() {
      return {
        type: 'connect4',
        board: Array.from({ length: 6 }, () => Array(7).fill(0)),
        turn: 0,
        status: 'playing',
        winner: null
      };
    },
    getPublicState(s) {
      return { type: s.type, board: s.board, turn: s.turn, status: s.status, winner: s.winner };
    },
    makeMove(s, playerIndex, move) {
      if (s.status !== 'playing' || s.turn !== playerIndex) return { valid: false };
      const col = Number(move.col);
      if (col < 0 || col > 6) return { valid: false };

      let row = -1;
      for (let r = 5; r >= 0; r--) {
        if (s.board[r][col] === 0) { row = r; break; }
      }
      if (row === -1) return { valid: false };

      const piece = playerIndex + 1;
      s.board[row][col] = piece;

      if (this._checkWin(s.board, row, col, piece)) {
        s.status = 'finished';
        s.winner = playerIndex;
      } else if (s.board[0].every(cell => cell !== 0)) {
        s.status = 'finished';
        s.winner = 'draw';
      } else {
        s.turn = 1 - s.turn;
      }
      return { valid: true };
    },
    _checkWin(b, r, c, p) {
      const dirs = [[0,1],[1,0],[1,1],[1,-1]];
      for (const [dr, dc] of dirs) {
        let count = 1;
        for (const sign of [-1, 1]) {
          let nr = r + dr * sign, nc = c + dc * sign;
          while (nr >= 0 && nr < 6 && nc >= 0 && nc < 7 && b[nr][nc] === p) {
            count++; nr += dr * sign; nc += dc * sign;
          }
        }
        if (count >= 4) return true;
      }
      return false;
    },
    getBotMove(s, botIdx) {
      const validCols = [0,1,2,3,4,5,6].filter(c => s.board[0][c] === 0);
      // 1. Take winning move if available
      for (const c of validCols) {
        const copy = JSON.parse(JSON.stringify(s));
        this.makeMove(copy, botIdx, { col: c });
        if (copy.winner === botIdx) return { col: c };
      }
      // 2. Block opponent's winning move
      for (const c of validCols) {
        const copy = JSON.parse(JSON.stringify(s));
        copy.turn = 1 - botIdx;
        this.makeMove(copy, 1 - botIdx, { col: c });
        if (copy.winner === 1 - botIdx) return { col: c };
      }
      // 3. Prefer center column, else random
      if (validCols.includes(3) && Math.random() < 0.6) return { col: 3 };
      return { col: validCols[Math.floor(Math.random() * validCols.length)] };
    }
  },

  // --- CHECKERS ---
  checkers: {
    init() {
      const board = Array.from({ length: 8 }, () => Array(8).fill(null));
      for (let r = 0; r < 8; r++) {
        for (let c = 0; c < 8; c++) {
          if ((r + c) % 2 === 1) {
            if (r < 3) board[r][c] = { p: 1, k: false }; // Black (top)
            if (r > 4) board[r][c] = { p: 0, k: false }; // Red (bottom)
          }
        }
      }
      return { type: 'checkers', board, turn: 0, status: 'playing', winner: null };
    },
    getPublicState(s) {
      return { type: s.type, board: s.board, turn: s.turn, status: s.status, winner: s.winner };
    },
    _legalMoves(board, p) {
      const steps = [], jumps = [];
      for (let r = 0; r < 8; r++) {
        for (let c = 0; c < 8; c++) {
          const cell = board[r][c];
          if (!cell || cell.p !== p) continue;
          const dirs = cell.k ? [[-1,-1],[-1,1],[1,-1],[1,1]] : (p === 0 ? [[-1,-1],[-1,1]] : [[1,-1],[1,1]]);
          for (const [dr, dc] of dirs) {
            const nr = r + dr, nc = c + dc;
            if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
              if (!board[nr][nc]) {
                steps.push({ from: [r, c], to: [nr, nc] });
              } else if (board[nr][nc].p !== p) {
                const jr = r + dr * 2, jc = c + dc * 2;
                if (jr >= 0 && jr < 8 && jc >= 0 && jc < 8 && !board[jr][jc]) {
                  jumps.push({ from: [r, c], to: [jr, jc] });
                }
              }
            }
          }
        }
      }
      return jumps.length > 0 ? jumps : steps; // Mandatory jumps
    },
    makeMove(s, playerIndex, move) {
      if (s.status !== 'playing' || s.turn !== playerIndex || !move.from || !move.to) return { valid: false };
      const legal = this._legalMoves(s.board, playerIndex);
      const match = legal.find(m =>
        m.from[0] === move.from[0] && m.from[1] === move.from[1] &&
        m.to[0] === move.to[0] && m.to[1] === move.to[1]
      );
      if (!match) return { valid: false };

      const [r1, c1] = match.from;
      const [r2, c2] = match.to;
      const piece = s.board[r1][c1];
      s.board[r1][c1] = null;
      s.board[r2][c2] = piece;

      if (Math.abs(r2 - r1) === 2) {
        s.board[(r1 + r2) / 2][(c1 + c2) / 2] = null;
      }
      if ((playerIndex === 0 && r2 === 0) || (playerIndex === 1 && r2 === 7)) {
        piece.k = true;
      }

      s.turn = 1 - s.turn;
      if (this._legalMoves(s.board, s.turn).length === 0) {
        s.status = 'finished';
        s.winner = playerIndex;
      }
      return { valid: true };
    },
    getBotMove(s, botIdx) {
      const moves = this._legalMoves(s.board, botIdx);
      let bestMove = moves[0];
      let bestScore = -999;
      for (const m of moves) {
        const copy = JSON.parse(JSON.stringify(s));
        this.makeMove(copy, botIdx, m);
        let score = 0;
        for (let r = 0; r < 8; r++) {
          for (let c = 0; c < 8; c++) {
            const cell = copy.board[r][c];
            if (cell) score += (cell.p === botIdx ? 1 : -1) * (cell.k ? 1.5 : 1);
          }
        }
        score += Math.random() * 0.2;
        if (score > bestScore) { bestScore = score; bestMove = m; }
      }
      return bestMove;
    }
  },

  // --- CHESS ---
  chess: {
    init() {
      return { type: 'chess', chess: new Chess(), turn: 0, status: 'playing', winner: null };
    },
    getPublicState(s) {
      return {
        type: 'chess',
        board: s.chess.board(),
        turn: s.chess.turn() === 'w' ? 0 : 1,
        inCheck: s.chess.inCheck(),
        status: s.status,
        winner: s.winner
      };
    },
    makeMove(s, playerIndex, move) {
      if (s.status !== 'playing') return { valid: false };
      const expectedTurn = s.chess.turn() === 'w' ? 0 : 1;
      if (playerIndex !== expectedTurn) return { valid: false };

      try {
        const result = s.chess.move({ from: move.from, to: move.to, promotion: 'q' });
        if (!result) return { valid: false };
      } catch {
        return { valid: false };
      }

      if (s.chess.isGameOver()) {
        s.status = 'finished';
        s.winner = s.chess.isCheckmate() ? playerIndex : 'draw';
      } else {
        s.turn = 1 - s.turn;
      }
      return { valid: true };
    },
    getBotMove(s) {
      const vals = { p: 1, n: 3, b: 3, r: 5, q: 9, k: 0 };
      const moves = s.chess.moves({ verbose: true });
      let best = moves[0];
      let bestScore = -999;

      for (const m of moves) {
        s.chess.move(m);
        let score = 0;
        for (const row of s.chess.board()) {
          for (const sq of row) {
            if (sq) score += (sq.color === 'b' ? 1 : -1) * vals[sq.type];
          }
        }
        if (s.chess.isCheckmate()) score += 100;
        score += Math.random() * 0.15;
        s.chess.undo();
        if (score > bestScore) { bestScore = score; best = m; }
      }
      return { from: best.from, to: best.to };
    }
  }
};

// ==========================================
// 3. MULTIPLAYER ROOMS & WEBSOCKETS
// ==========================================
const rooms = {};

function makeRoomCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let code = '';
  for (let i = 0; i < 4; i++) code += chars[Math.floor(Math.random() * chars.length)];
  return rooms[code] ? makeRoomCode() : code;
}

function broadcastRoom(code) {
  const room = rooms[code];
  if (!room) return;
  io.to(code).emit('room_update', {
    code,
    players: room.players.map(p => p ? p.username : 'Waiting for friend...'),
    state: GAMES[room.gameType].getPublicState(room.state)
  });
}

function triggerBotIfNeeded(code) {
  const room = rooms[code];
  if (!room || room.state.status !== 'playing') return;
  const activePlayer = room.players[room.state.turn];
  if (activePlayer && activePlayer.isBot) {
    setTimeout(() => {
      if (!rooms[code] || rooms[code].state.status !== 'playing') return;
      const engine = GAMES[room.gameType];
      const botMove = engine.getBotMove(room.state, room.state.turn);
      if (botMove) {
        engine.makeMove(room.state, room.state.turn, botMove);
        broadcastRoom(code);
      }
    }, 600); // Human-like 600ms delay
  }
}

io.on('connection', (socket) => {
  let user = null;

  socket.on('auth', ({ token }) => {
    user = authenticateGuest(token);
    socket.emit('auth_ok', user);
  });

  socket.on('create_room', ({ gameType, vsBot }) => {
    if (!user || !GAMES[gameType]) return;
    const code = makeRoomCode();
    rooms[code] = {
      gameType,
      players: [
        { socketId: socket.id, username: user.username, isBot: false },
        vsBot ? { socketId: null, username: 'Bot', isBot: true } : null
      ],
      state: GAMES[gameType].init()
    };
    socket.join(code);
    socket.data.roomCode = code;
    socket.data.playerIndex = 0;
    broadcastRoom(code);
  });

  socket.on('join_room', ({ code }) => {
    if (!user) return;
    const cleanCode = String(code || '').trim().toUpperCase();
    const room = rooms[cleanCode];
    if (!room) return socket.emit('error_msg', 'Room not found.');
    if (room.players[1]) return socket.emit('error_msg', 'Room is already full.');

    room.players[1] = { socketId: socket.id, username: user.username, isBot: false };
    socket.join(cleanCode);
    socket.data.roomCode = cleanCode;
    socket.data.playerIndex = 1;
    broadcastRoom(cleanCode);
  });

  socket.on('make_move', (move) => {
    const code = socket.data.roomCode;
    const room = rooms[code];
    if (!room) return;
    if (!room.players[1]) return socket.emit('error_msg', 'Waiting for Player 2 to join!');

    const engine = GAMES[room.gameType];
    const res = engine.makeMove(room.state, socket.data.playerIndex, move);
    if (res.valid) {
      broadcastRoom(code);
      triggerBotIfNeeded(code);
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Server running on http://localhost:${PORT}`));
