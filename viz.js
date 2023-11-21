// ---------------------------- CONSTANTS ----------------------------
// number of rows and columns
const BOARD_SIZE = 4
// pixel dimensions of a cell
const CELL_SIZE = 50
// the number colors, 1-8
const colors = ['#0000ff', '#008100', '#ff1300', '#000083', '#810500', '#2a9494', '#000000', '#808080']

// ----------------------- RENDERING FUNCTIONS -----------------------

// boardId: a string, like Board0
// idx: the index of the board
const drawBoard = (boardId, idx) => {
    const svgBoard = new Grid({
        grid_location: {x: 50, y: 50},
        cell_size: {x_size: CELL_SIZE, y_size: CELL_SIZE},
        grid_dimensions: {x_size: BOARD_SIZE, y_size: BOARD_SIZE}}
    )

    const board = instance.signature('Board').atom(boardId)

    const openedMap = {};

    board.join(instance.field('opened')).tuples().forEach((entry, _) => {
        const [y, x, val] = entry.toString().split(',').map((s) => parseInt(s))
        openedMap[`${x},${y}`] = val
    })

    board.join(instance.field('tiles')).tuples().forEach((entry, _) => {
        // idk why columns are first but sure
        const [y, x, val] = entry.toString().split(',').map((s) => parseInt(s))

        svgBoard.add({x: x, y: y}, openedMap[`${x},${y}`] === 0 ? renderCoveredTile() : renderTile(val))
    })

    stage.add(svgBoard)
}

// draw a grey square for a covered tile
const renderCoveredTile = () => {
    return new Rectangle({width: CELL_SIZE, height: CELL_SIZE, color: 'grey'})
}

// draw nothing, a number, or a bomb, depending on the tile
const renderTile = (val) => {
    switch (val) {
        case 0: return new TextBox({text:''})
        case -1: return new Circle({radius: CELL_SIZE / 3, color: 'black'})
        default: return new TextBox({text:val, color: colors[val - 1], fontSize: 0.5 * CELL_SIZE})
    }
}


// ---------------------------- MAIN CODE ----------------------------
const stage = new Stage();

// const boards = instance.signature('Board').atoms();

// for (let i = 0; i < boards.length; i++) {
//   const currBoard = instance.signature('Board').atom(`Board${i}`)

//   // instead do a currBoard.join(instance.field('next')).size() == 0 check i think
//   if (currBoard.join(instance.field('next')).size() == 1 && instance.field('next').join(currBoard).size() == 0) {

//   }
//   // for (let j = 0; j < boards.length; j++) {
//   //   if (i == j) continue

//   //   if 
//   // }
// }

// for (let i = 0; i < boards.length; i++) {

// }

drawBoard('Board0', 0)

stage.render(svg, document)