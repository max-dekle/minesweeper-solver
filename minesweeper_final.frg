#lang forge

one sig StaticBoard {
  // 1 if a bomb, 0 otherwise
  bombs: pfunc Int -> Int -> Int,
  // 0 if borders no bombs, -1 if it's a bomb, otherwise number of bombs the tile borders
  tiles: pfunc Int -> Int -> Int
}

sig BoardState {
  // 0 if hidden, 1 if opened
  opened: pfunc Int -> Int -> Int
}

one sig Game {
  initialState: one BoardState,
  next: pfunc BoardState -> BoardState
}

pred inBounds[row, col: Int] {
  row >= 0 and row <= 3 and col >= 0 and col <= 3
}

pred wellformed[b: BoardState] {
  all row, col: Int | {
    not inBounds[row, col] => {
      no b.opened[row][col]
    } 
    inBounds[row, col] => {
      b.opened[row][col] = 0 or b.opened[row][col] = 1
    }
  }
}

pred initStatic {
  // set maximum number of bomb tiles (bombs are 1 in this board for ease of addition later)
  #{row, col: Int | StaticBoard.bombs[row][col] = 1} = 4
  #{row, col: Int | StaticBoard.bombs[row][col] = 0} = 12

  all row, col: Int | {
    // if not in bounds, don't put a bomb
    (not inBounds[row, col]) => {
      no StaticBoard.bombs[row][col]
      no StaticBoard.tiles[row][col]
    }

    // everything that's not a bomb gets assigned a number based on how many it's bordering
    StaticBoard.bombs[row][col] = 0 => {
      StaticBoard.tiles[row][col] = 
        add[
          StaticBoard.bombs[add[row, -1]][add[col, -1]],
          StaticBoard.bombs[add[row, -1]][col],
          StaticBoard.bombs[add[row, -1]][add[col, 1]],
          StaticBoard.bombs[row][add[col, -1]],
          StaticBoard.bombs[row][add[col, 1]],
          StaticBoard.bombs[add[row, 1]][add[col, -1]],
          StaticBoard.bombs[add[row, 1]][col],
          StaticBoard.bombs[add[row, 1]][add[col, 1]]
        ]
    } else {
      inBounds[row, col] => StaticBoard.tiles[row][col] = -1
    }
  }
}
pred unhideOne[first: BoardState] {

  one row, col: Int |  {
    first.opened[row][col] = 1
  }

  one row, col: Int |  {
    StaticBoard.tiles[row][col] = 0
    first.opened[row][col] = 1
  }
}

pred initBoard[b: BoardState] {
  // ensure wellformed
  wellformed[b]

  // open exactly one tile
  #{r, c: Int | b.opened[r][c] = 1} = 1

  unhideOne[b]

}

pred won[b: BoardState] {
  // no bombs are revealed and all non-bomb tiles are revealed
  all row, col: Int | inBounds[row, col] => {
    StaticBoard.tiles[row][col] = -1 => {
      b.opened[row][col] = 0 
    } else {
      some StaticBoard.tiles[row][col] => b.opened[row][col] = 1
    }
  }
}

pred hasLogicalMove[b: BoardState, r, c: Int] {
  ((StaticBoard.tiles[add[r, -1]][add[c, -1]] = 0 
  and b.opened[add[r, -1]][add[c, -1]] = 1)
  or
  (StaticBoard.tiles[add[r, -1]][c] = 0 and
  b.opened[add[r, -1]][c] = 1)
  or
  (StaticBoard.tiles[add[r, -1]][add[c, 1]] = 0
  and b.opened[add[r, -1]][add[c, 1]] = 1)
  or
  (StaticBoard.tiles[r][add[c, -1]] = 0
  and b.opened[r][add[c, -1]] = 1 )
  or
  (StaticBoard.tiles[r][add[c, 1]] = 0
  and b.opened[r][add[c, 1]] = 1 )
  or
  (StaticBoard.tiles[add[r, 1]][add[c, -1]] = 0
  and b.opened[add[r, 1]][add[c, -1]] = 1
  )
  or
  (StaticBoard.tiles[add[r, 1]][c] = 0
  and b.opened[add[r, 1]][c] = 1
  )
  or
  (StaticBoard.tiles[add[r, 1]][add[c, 1]] = 0
  and b.opened[add[r, 1]][add[c, 1]] = 1)
  )
}

pred openTile[pre, post: BoardState, row, col: Int] {
  all r, c: Int | inBounds[r,c] => {
    (r = row and c= col) implies (post.opened[row][col] = 1) else {
      post.opened[r][c] = pre.opened[r][c]
    }
  }
}

// if no move logically possible do nothing
pred doNothing[pre, post: BoardState] {
  all r, c: Int | {
    post.opened[r][c] = pre.opened[r][c]
  }
}

pred traces {
  initStatic

  initBoard[Game.initialState]
  no prev: BoardState | Game.next[prev] = Game.initialState

 -- Every transition is a valid move
  all b: BoardState | some Game.next[b] => {
    one r, c: Int | {
      hasLogicalMove[b, r, c]
      b.opened[r][c] = 0
      inBounds[r, c] 
      openTile[b, Game.next[b], r, c]
    }
  }

  some b: BoardState | won[b]
  all b: BoardState { wellformed[b] }
}

run {traces} for 4 Int, 12 BoardState for {next is linear}