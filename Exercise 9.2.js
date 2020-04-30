// graph from Exercise 9.2 Q1b

var _v = [
    { label: "a" },	//Index = 0
    { label: "b" },	//Index = 1
    { label: "c" },	//Index = 2
    { label: "d" },	//Index = 3
    { label: "e" },	//Index = 4
    { label: "f" },	//Index = 5
    { label: "g" },	//Index = 6
    { label: "h" },	//Index = 7
    { label: "i" },	//Index = 8
    { label: "j" },	//Index = 9
    { label: "k" },	//Index = 10
    { label: "l" }	//Index = 11
    ];
    
    //There are 12 verticese and 20 edges
    var _e = [
    // a(0) --> b(1)
    { u: 0, v: 1, w: 3 },
    // a(0) --> c(2)
    { u: 0, v: 2, w: 5 },
    // a(0) --> d(3)
    { u: 0, v: 3, w: 4 },
    
    // b(1) --> e(4)
    { u: 1, v: 4, w: 3 },
    // b(1) --> f(5)
    { u: 1, v: 5, w: 6 },
    
    // c(2) --> d(3)
    { u: 2, v: 3, w: 2 },
    // c(2) --> g(6)
    { u: 2, v: 6, w: 4 },
    
    // d(3) --> e(4)
    { u: 3, v: 4, w: 1 },
    // d(3) --> h(7)
    { u: 3, v: 7, w: 5 },
    
    // e(4) --> f(5)
    { u: 4, v: 5, w: 2 },
    // e(4) --> i(8)
    { u: 4, v: 8, w: 4 },
    
    // f(5) --> j(9)
    { u: 5, v: 9, w: 5 },
    
    // g(6) --> h(7)
    { u: 6, v: 7, w: 3 },
    // g(6) --> k(10)
    { u: 6, v: 10, w: 6 },
    
    // h(7) --> k(10)
    { u: 7, v: 10, w: 7 },
    // h(7) --> i(8)
    { u: 7, v: 8, w: 6 },
    
    // i(8) --> j(9)
    { u: 8, v: 9, w: 3 },
    // i(8) --> l(11)
    { u: 8, v: 11, w: 5 },
    
    // j(9) --> l(11)
    { u: 9, v: 11, w: 9 },
    
    // k(10) --> l(11)
    { u: 10, v: 11, w: 8 },
    ];