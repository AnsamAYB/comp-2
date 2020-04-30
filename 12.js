// CPCS 324 Algorithms & Data Structures 2
// Graph data structure starter - Final Project
// 2019, Dr. Muhammad Al-Hashimi


// -----------------------------------------------------------------------
// simple graph object with linked-list edge implementation and minimal fields
// extra vertex and edge member fields and methods to be added later as needed
//
var _v = [],
    _e = []; // note naming conventions in upload guide

// -----------------------------------------------------------------------
function main_graph() {

    var heap = new Heap();
    //operation sequence starting from Figure 6.11: 
    heap.insert(2, "a");
    heap.insert(9, "b");
    heap.insert(7, "c");
    heap.insert(6, "d");
    heap.insert(5, "e");
    heap.insert(8, "f");
    document.write(heap.show());
    heap.insert(10, "g");
    document.write(heap.show());
    heap.insert(15, "h");
    document.write(heap.show());
    //////////////////////////////////////
    // implementation of graph
    var g = new Graph();
    g.label = "Exercise 9.2: 1b (Levitin, 3rd edition)";
    g.readGraph(_v, _e);
    g.printGraph();

    //////////////////////////////////////
    // prim 1

    //output the MST
    document.write("<p>MST by first Prim <br>");

    g.Prim_1();
    for (var i = 0; i < g.MST.length; i++) {
        document.write("(", g.MST[i].v, ",", g.MST[i].u, ")");
        if (i == g.MST.length - 1) document.write(".<p>");
        else document.write(", ");
    }

    ///////////////////////////////////////
    //Prim 2

    //output the MST
    document.write("<br>MST by Prim2 (PQ-Heap): <br>");
    g.Prim_2();
    for (var n = 0; n < g.VT.length; n++) {
        if (g.VT[n].parent != null) {
            document.write("(", g.VT[n].parent, ",", g.VT[n].tree, ")");
            if (n == g.VT.length - 1) document.write(".<p>");
            else document.write(", ");
        } else if (g.VT[n].parent == null) {
            document.write("(-, ", g.VT[n].tree, "), ");
        }
    }
}

// -----------------------------------------------------------------------
// similar to starter 8
function Vertex(v) {
    //property fields

    this.label = v.label;

    this.visit = false;

    this.adjacent = new List();

    // --------------------
    // member methods

    this.adjacentByID = adjacentByIdImpl;

    this.incidentEdges = incidentEdgesImpl;

    this.vertexInfo = vertexInfoImpl;

    this.insertAdjacent = insertAdjacentImpl;
}

// -----------------------------------------------------------------------
// similar to starter 8
function Edge(vert_i, weight) {
    // --------------------
    // property fields

    this.target_v = vert_i;
    this.weight;

    if (weight == undefined) {
        this.weight = null;
    } else {
        this.weight = weight;
    }
}

// -----------------------------------------------------------------------
// similar to starter 8 (NO network methods)
function Graph() {
    // --------------------
    // property fields

    this.vert = [];

    this.nv = 0;

    this.ne = 0;

    this.connectedComp = 0;

    this.digraph = false;

    this.weighted = false;

    this.label = "";

    this.VT = []; //vertex tree
    this.MST = [];

    // --------------------
    // member methods

    this.readGraph = better_input;

    this.printGraph = printGraphImpl;

    this.addEdge = addEdgeImpl;

    this.listVerts = listVertsImpl;

    this.isConnected = isConnectedImpl;

    this.componentInfo = componentInfoImpl;

    this.Prim_2 = primImpl2;
    this.Prim_1 = primImpl1;
}

// -----------------------------------------------------------------------
// functions used by methods of Graph and ancillary objects

function make_graphImpl(n, m, w) {
    // feel free to change, if needed
    // parameter validations and checks: number of edges etc.
    var mmax = n * (n - 1);
    if (!this.digraph) mmax /= 2;
    if (m > mmax) {
        document.write("<p>ERROR: invalid number of edges for graph type</p>");
        return;
    }

    // create n vertex in v[] using id 0 to n-1 as label
    var v = [];
    for (var i = 0; i < n; i++) v[i] = {
        label: i.toString()
    };

    // if graph complete no need to generate random edges, just create mmax edges systematically

    // otherwise repreat create m distinct edges (graph loops not allowed)

    var e = [],
        wmin = 1,
        wmax = 50000,
        wsum = 0;

    var h = []; // quick-dirty n x n matrix to check previously generated edges,
    // m-entry hash table would be more efficient
    for (i = 0; i < n; i++) {
        h[i] = [];
        h[i][i] = 0; // no graph loops; 0 = blocked pair of vertices
    }

    for (i = 0; i < m; i++) {
        // generate vertices u, v randomly
        do {
            var u_i = random(0, n - 1),
                v_i = random(0, n - 1);
        } while (h[u_i][v_i] != undefined);

        h[u_i][v_i] = 0;
        h[v_i][u_i] = 0; // update matrix: block u,v; block v,u also if undirected

        // if (u,v) is distinct insert in e[] (generate random weight if w true)
        // otherwise repeat generate another u,v pair

        e[i] = {
            u: u_i,
            v: v_i
        };
        if (w) {
            e[i].w = random(wmin, wmax);
            wsum += e[i].w;
        }
    }

    // call graph reader method and set label, graph type depends on value of digraph property
    this.read_graph(v, e);
    this.label =
        "Generated " +
        n +
        " vertices, " +
        m +
        " random " +
        (!this.digraph ? "un" : "") +
        "directed edges (" +
        Math.round((m / mmax) * 100) +
        "%)" +
        (w ? ", ave weight = " + Math.round(wsum / m) : "");
}

function random(low, high) {
    return Math.floor(Math.random() * (high - low + 1)) + low;
}

// -----------------------------------------------------------------------
// begin student code section (NO network functions, only code related to this project)
// -----------------------------------------------------------------------

// Final M2 code here

// -----------------------------------------------------------------------
// paste your heap package here

function Heap() {
    // h[0] not used, heap initially empty

    this.h = [null]; // heap of integer keys
    this.h_item = [null]; // corresponding heap of data-items (any object)
    this.size = 0; // 1 smaller than array (also index of last child)

    // --------------------
    // PQ-required only; more could be added later when needed
    // the 2 basic shape maintaining operations heapify and reheapify simplify
    // processing functions

    this.isEmpty = heapisEmpty; // return true if heap empty
    this.deleteRoot = heapDeleteRoot; // return data-item in root
    this.insert = heapInsert; // insert data-item with key
    this.heapify = heapheapify; // make subtree heap; top-down heapify ("sink") used by .deleteRoot()
    this.reheapify = heapreheapify; // bottom-up reheapify ("swim") used by .insert()
    this.show = heapShow; // utility: return pretty formatted heap as string
    // ... etc

    // --------------------
    // student methods next; ; actual functions in student code section at end
}

// -----------------------------------------------------------------------
// functions used by methods of Heap() object

// note return interface for heapDeleteRoot() below
// use prefix 'heap' for implementing functions (see examples)
// if both key and item are needed, pass key before item
//

function heapShow() {
    // utility: return pretty formatted heap as string
    var n = this.size;
    var m = Math.floor(n / 2); // last parent node
    var k = this.h.slice(1, n + 1),
        a = this.h_item.slice(1, n + 1);
    var out =
        "<h2>Heap (size=" + n + "):</h2><p>Keys: " + k + "<br>Data: " + a + "</p>";
    for (var i = 1; i <= m; i++) {
        out += "<p>" + i + ": <b>" + this.h[i] + "(" + this.h_item[i] + ")</b><ul>";
        if (2 * i <= n) out += "<li>" + this.h[2 * i] + "</li>";
        if (2 * i + 1 <= n) out += "<li>" + this.h[2 * i + 1] + "</li>";
        out += "</ul></p>";
    }

    return out;
}

// -----------------------------------------------------------------------
// --- begin student code section ----------------------------------------
// -----------------------------------------------------------------------
//heap implementation-


function heapInsert(key, item) {
    this.size += 1; //increase the size as we're inserting
    this.h[this.size] = key;
    this.h_item[this.size] = item;
    this.reheapify(); // maintains the heap after the addition
}


function heapDeleteRoot() {
    if (this.isEmpty()) {
        return "The heap is empty";
    }
    // save root key and item pair
    else var root = [this.h[1], this.h_item[1]];

    // ... complete

    this.h_item[1] = this.h_item[this.size];

    //-------------------------------------------

    this.h[1] = this.h[this.size];
    // maintains the heap after the deletion
    this.heapify(1);
    this.size -= 1; //increase the size as we just deleted something

    return root;
}



function heapisEmpty() {
    return this.size == 0 ? true : false;
}


function heapheapify(key) {
    //find the largest between the root and children
    var leftChild = 2 * key; //the left childs index
    var rightChild = 2 * key + 1; //the right childs index
    var large = key; //considering the parent as the largest

    if (leftChild < this.size && this.h[leftChild] > this.h[large]) {
        large = leftChild;
    } else {
        large = key;
    }
    if (rightChild < this.size && this.h[rightChild] > this.h[large]) {
        large = rightChild;
    }
    // if a child has a larger value swap
    if (large != key) {
        //swap
        var itemTemp = this.h_item[key];
        this.h_item[key] = this.h_item[large];
        this.h_item[large] = itemTemp;
        //-------------------------------------------
        var temp = this.h[key];
        this.h[key] = this.h[large];
        this.h[large] = temp;
        //apply recurcively to confirm that the afected node is larger than it's children
        this.heapify(large);
    }
}


function heapreheapify() {
    var n = this.size;
    var m = Math.floor(n / 2); // last parent node

    for (var i = m; i >= 1; i--) {
        var key = i;
        var v = this.h[key];
        var v2 = this.h_item[key];
        var heap = false;
        while (!heap && 2 * key <= n) {
            var j = 2 * key;
            if (j < n) {
                //there are two children
                if (this.h[j] < this.h[j + 1]) {
                    ///////////////////
                    j += 1;
                }
            }
            if (v >= this.h[j]) {
                heap = true;
            } else {
                //  var itemTemp = this.h_item[key];
                this.h_item[key] = this.h_item[j];
                //    this.h_item[j] = itemTemp;
                //-------------------------------------------
                //  var temp = this.h[key];
                this.h[key] = this.h[j];
                //   this.h[j] = temp;
                //-------------------------------------------
                key = j;
            }
            this.h[key] = v;
            this.h_item[key] = v2;
        }
    }
}

// -----------------------------------------------------------------------
// paste your PQ package here (version with calls to heap methods only)



// Basic design decisions and implementation planning (objects & interfaces)
// initial requirements: to quickly support second Prim's algorithm, 
// implement minimum priority functionality

// design decisions:
// Implement PQ based on Heap
// Encapsulate the code of heap 

// Impact analysis:
// since the PQ is implemented based on heap the insert and delete now is O(log n)



function PQueue() {
    this.pq = new Heap(); // requirement: Heap implementation

    // specify (design) methods

    this.isEmpty = isEmptyImpl; // return true if queue empty
    this.deleteMin = deleteMinImpl; // remove/return item with minimum priority
    this.insert = insertImpl; //insert/update an item with priority
}

// -----------------------------------------------------------------------
// Priority queue node constructor (document using JSDOC comments)



function PQNode(item, key) {
    this.item = item;
    this.prior = key;

    // specify (design) methods
}

// -----------------------------------------------------------------------
// functions used by PQueue() object methods
// specify interface information (JSDOC comments)
// ....


function isEmptyImpl() {
    return this.pq.isEmpty();
}

//-------------------------------------------------------------------------



function deleteMinImpl() {
    var deletedItem = this.pq.deleteRoot();
    deletedItem[0] = deletedItem[0] * -1;
    return deletedItem;
}

//-------------------------------------------------------------------------



function insertImpl(key, item) {
    return this.pq.insert(key * -1, item);
}

// -----------------------------------------------------------------------
// published docs section (ref. assignment page)
// similar to starters 8 and 11
// *NO* JSDOC comments in this section
// -----------------------------------------------------------------------
// -----------------------------------------------------------------------
///////////////////////////INPUT/OUTPUT FUNCTIONS BELOW////////////////////
// -----------------------------------------------------------------------

function printGraphImpl() {
    document.write(
        "<p>GRAPH {",
        this.label,
        "} ",
        this.weighted ? "" : "Not ",
        "WEIGHTED - ",
        this.digraph ? "" : "UN",
        "DIRECTED - ",
        this.nv,
        " VERTICES, ",
        this.ne,
        " EDGES:</p>"
    );
    this.componentInfo();
    this.listVerts();

    ///////////////////////////////////////////////////////////////////////////////////////
}

function better_input(v, e) {
    this.nv = v.length;
    this.ne = e.length;

    for (var i = 0; i < this.nv; i++) {
        this.vert[i] = new Vertex(v[i]);
    }

    for (var j = 0; j < this.ne; j++) {
        this.addEdge(e[j].u, e[j].v, e[j].w);
    }

    if (!this.digraph) {
        this.ne = e.length * 2;
    }

    if (!(e[0].w == undefined)) {
        this.weighted = true;
    }
}

function listVertsImpl() {
    var i;
    for (i = 0; i < this.nv; i++) {
        document.write(" VERTEX: " + i + " ");
        document.write(this.vert[i].vertexInfo() + "<br>");
    }
}

function vertexInfoImpl() {
    return (
        " {" +
        this.label +
        "} - VISIT: " +
        this.visit +
        " - ADJACENCY: " +
        this.adjacentByID()
    );
}

function componentInfoImpl() {
    if (this.isConnected()) {
        document.write("CONNECTED<br><br>");
    } else if (this.isConnected() == false) {
        document.write("no connectivity info<br><br>");
    } else {
        document.write("UNCONNECTED<br><br>", this.connectedComp);
    }
}

function isConnectedImpl() {
    if (this.connectedComp == 1) {
        return true;
    } else {
        return false;
    }
}
// -----------------------------------------------------------------------
///////////////////////////////OTHER FUNCTIONS////////////////////////////
// -----------------------------------------------------------------------

function addEdgeImpl(u_i, v_i, weight) {
    var u = this.vert[u_i];
    var v = this.vert[v_i];

    u.insertAdjacent(v_i, weight);

    if (!this.digraph) {
        v.insertAdjacent(u_i, weight);
    }
}

function adjacentByIdImpl() {
    adjId = [];
    edgeAdjacent = this.adjacent.traverse();
    for (i = 0; i < edgeAdjacent.length; i++) {
        adjId[i] = edgeAdjacent[i].target_v;
    }
    return adjId;
}
// -----------------------------------------------------------------------

function isConnectedImpl() {
    //Test if graph is connected
    return this.connectedComp == 1;
}

function incidentEdgesImpl() {
    arr = this.adjacent.traverse();
    enodes = [];
    for (var i = 0; i < arr.length; i++) {
        enodes[i] = {
            adjVert_i: arr[i].target_v,
            edgeLabel: arr[i].label,
            edgeWeight: arr[i].weight
        };
    }
    return enodes;
}

// -----------------------------------------------------------------------

function insertAdjacentImpl(v_i, weight) {
    var e = new Edge(v_i, weight);

    return this.adjacent.insert(e);
}

// -----------------------------------------------------------------------
//{FINAL PROJECT} -Functions: {PRIM 1&2 - PQ based on Heap}

function primImpl2() {
    if (this.digraph == true) {
        return "NO PRIM";
    }

    // run Prim's algorithm in a graph , starting from vertex 0

    var Q = new PQueue(); //Initialize Q (Priority Queue)

    this.VT = []; //Initialize VT
    var parent; // penultimate or parent which is the edge connecting v to tree

    for (var i = 0; i < this.nv; i++) {
        //mark all the vertices as unvisited(visited vertices aren't visited again)
        this.vert[i].visit = false;
    }

    // we'll be starting with vertex 0  and greedily growing tree
    var edges = this.vert[0].incidentEdges();

    for (i = 0; i < edges.length; i++) {
        Q.insert(edges[i].edgeWeight, edges[i].adjVert_i);
    }

    // first element in the tree
    this.VT[0] = {
        tree: 0,
        parent: "-"
    };

    this.vert[0].visit = true;

    while (!Q.isEmpty()) {
        min = Q.deleteMin();

        //parent
        var edges = this.vert[min[1]].incidentEdges();

        for (var i = 0; i < edges.length; i++) {
            if (this.vert[edges[i].adjVert_i].visit) {
                if (edges[i].edgeWeight == min[0]) {
                    parent = edges[i].adjVert_i;
                    break;
                }
            }
        }
        //vertex tree update
        if (!this.vert[min[1]].visit) {
            this.VT[this.VT.length] = {
                tree: min[1],
                parent: parent
            };
            this.vert[min[1]].visit = true;

            //priority queue update
            for (var i = 0; i < edges.length; i++) {
                if (!this.vert[edges[i].adjVert_i].visit) {
                    Q.insert(edges[i].edgeWeight, edges[i].adjVert_i);
                }
            }
        }
    }
    return this.VT;
}



function primImpl1() {
    // perform Prim’s Algorithm to find Minimum Spanning tree of the graph
    var n;
    var Tree_vertex = [];

    // mark all vertices unvisited
    for (var m = 0; m < this.nv; m++) {
        this.vert[m].visit = false;
    }

    Tree_vertex[0] = 0; //initial by first vertext
    this.vert[0].visit = true; //mark visited
    this.MST[0] = {
        v: "-",
        u: Tree_vertex[0],
        w: "-"
    };
    var min = Infinity; // initial value

    for (var i = 1; i < this.nv; i++) {
        for (var j = 0; j < Tree_vertex.length; j++) {
            // get the incident Edge for the vertex in tree
            var incident_Edge = this.vert[Tree_vertex[j]].incidentEdges();

            for (var k = 0; k < incident_Edge.length; k++) {
                // check if the adjacent vertex with minimum weight and ( it is not visited >> not in tree)
                if (
                    !this.vert[incident_Edge[k].adjVert_i].visit &&
                    incident_Edge[k].edgeWeight < min
                ) {
                    // insert in MST
                    this.MST[i] = {
                        v: Tree_vertex[j],
                        u: incident_Edge[k].adjVert_i,
                        w: incident_Edge[k].edgeWeight
                    };
                    min = this.MST[i].w;
                }
            }
        }

        // insert adjacent Vertex with minimum weight to Tree_vertex
        n = this.MST.length;
        Tree_vertex[Tree_vertex.length] = this.MST[n - 1].u;

        // mark visited to insure it is now in Tree
        this.vert[this.MST[n - 1].u].visit = true;
        min = Infinity; //re-initial
    }
}

// -----------------------------------------------------------------------
//////////////////////////////////////////////////////////////////////////////