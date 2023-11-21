#lang forge
open "minesweeper_final.frg"


pred allWellformed {
  all b: BoardState {
    wellformed[b]
  }
}

pred someNotWellFormed {
  some b: BoardState {
    not wellformed[b]
  }
}

test expect {
  // test0: {traces} for exactly 12 BoardState is sat
  // // test1: {traces} for exactly 1 BoardState is unsat
  // test2: {traces implies allWellformed} for exactly 12 BoardState is theorem
  // test3: {traces and someNotWellFormed} for exactly 12 BoardState is unsat
}

-- in any trace, allWellformed holds
// assert allWellformed is necessary for traces
// for exactly 12 BoardState, 5 Int
// for {next is linear}


test suite for wellformed {
    test expect {
        validWellformedTest : {
            some b: BoardState | {
              b.opened = 
                0->0->0 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->1->1 + 1->1->0 + 2->1->1 + 3->1->0
              + 0->2->0 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->1 + 1->3->0 + 2->3->0 + 3->3->0
              wellformed[b]
            }
        } is sat

        invalidCoordinatesWellformedTest : {
            some b: BoardState | {
              b.opened = 
                0->0->0 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->-1->1 + 1->1->0 + 2->1->1 + 3->1->0
              + 0->2->0 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->1 + 1->-3->0 + 2->3->0 + 3->3->0
              wellformed[b]
            }
        } is unsat

        invalidValuesWellformedTest : {
            some b: BoardState | {
              b.opened = 
                0->0->4 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->-1->1 + 1->1->0 + 2->1->1 + 3->1->0
              + 0->2->0 + 1->2->3 + 2->2->0 + 3->2->0
              + 0->3->1 + 1->-3->0 + 2->3->0 + 3->3->0
              wellformed[b]
            }
        } is unsat
    }
}

test suite for inBounds {
    test expect {
        invalidInBounds : { all row, col: Int | {inBounds[row,col]} } is unsat

        // negativeBounds : { some row, col : Int | row < 0 and col < 0 {inBounds[row, col]} } is unsat

        validInBounds : {inBounds[2,3]} is sat
    }
}

test suite for initStatic {
    test expect {
        validBoard : {
          one static: StaticBoard | {
            static.bombs = 
                0->0->0 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->1->1 + 1->1->0 + 2->1->0 + 3->1->0
              + 0->2->1 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->0 + 1->3->1 + 2->3->0 + 3->3->1
            static.tiles = 
                0->0->1 + 1->0->1 + 2->0->0 + 3->0->0
              + 0->1->-1 + 1->1->2 + 2->1->0 + 3->1->0
              + 0->2->-1 + 1->2->3 + 2->2->2 + 3->2->1
              + 0->3->2 + 1->3->-1 + 2->3->2 + 3->3->-1
            initStatic
          }
        } is sat

        invalidBoard : {
          one static: StaticBoard | {
            static.bombs = 
                0->0->0 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->1->1 + 1->1->0 + 2->1->0 + 3->1->0
              + 0->2->1 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->0 + 1->3->1 + 2->3->0 + 3->3->1
            static.tiles = 
                0->0->1 + 1->0->1 + 2->0->0 + 3->0->0
              + 0->1->-3 + 1->1->2 + 2->1->0 + 3->1->5
              + 0->2->-1 + 1->2->4 + 2->2->2 + 3->2->1
              + 0->3->2 + 1->3->-1 + 2->3->2 + 3->3->-1
            initStatic
          }
        } is unsat

        MoreThan4Board : {
          one static: StaticBoard | {
            static.bombs = 
                0->0->1 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->1->1 + 1->1->0 + 2->1->0 + 3->1->0
              + 0->2->1 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->1 + 1->3->1 + 2->3->0 + 3->3->1
            static.tiles = 
                0->0->1 + 1->0->1 + 2->0->0 + 3->0->0
              + 0->1->-3 + 1->1->2 + 2->1->0 + 3->1->5
              + 0->2->-1 + 1->2->4 + 2->2->2 + 3->2->1
              + 0->3->2 + 1->3->-1 + 2->3->2 + 3->3->-1
            initStatic
          }
        } is unsat
    }
}

test suite for hasLogicalMove {
    test expect {
        validMove : {
          one static: StaticBoard | {
            static.bombs = 
                0->0->0 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->1->1 + 1->1->0 + 2->1->0 + 3->1->0
              + 0->2->1 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->0 + 1->3->1 + 2->3->0 + 3->3->1
            static.tiles = 
                0->0->1 + 1->0->1 + 2->0->0 + 3->0->0
              + 0->1->-1 + 1->1->2 + 2->1->0 + 3->1->0
              + 0->2->-1 + 1->2->3 + 2->2->2 + 3->2->1
              + 0->3->2 + 1->3->-1 + 2->3->2 + 3->3->-1
          }
          some b: BoardState | {
              b.opened = 
                0->0->1 + 1->0->1 + 2->0->1 + 3->0->1
              + 0->1->0 + 1->1->1 + 2->1->1 + 3->1->1
              + 0->2->0 + 1->2->1 + 2->2->1 + 3->2->0
              + 0->3->1 + 1->3->0 + 2->3->1 + 3->3->0
          }
          hasLogicalMove
        } is sat

        invalidMove : {
          one static: StaticBoard | {
            static.bombs = 
                0->0->0 + 1->0->0 + 2->0->0 + 3->0->0
              + 0->1->1 + 1->1->0 + 2->1->0 + 3->1->0
              + 0->2->1 + 1->2->0 + 2->2->0 + 3->2->0
              + 0->3->0 + 1->3->1 + 2->3->0 + 3->3->1
            static.tiles = 
                0->0->1 + 1->0->1 + 2->0->0 + 3->0->0
              + 0->1->-1 + 1->1->2 + 2->1->0 + 3->1->0
              + 0->2->-1 + 1->2->3 + 2->2->2 + 3->2->1
              + 0->3->2 + 1->3->-1 + 2->3->2 + 3->3->-1
          }
          some b: BoardState | {
              b.opened = 
                0->0->1 + 1->0->1 + 2->0->1 + 3->0->1
              + 0->1->0 + 1->1->1 + 2->1->1 + 3->1->1
              + 0->2->0 + 1->2->1 + 2->2->1 + 3->2->1
              + 0->3->1 + 1->3->0 + 2->3->1 + 3->3->0
          }
          hasLogicalMove
          }
        } is unsat
}
