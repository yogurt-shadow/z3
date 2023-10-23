(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :author |Thomas Sturm, CNRS France, http://science.thomas-sturm.de|)
(set-info :source |
Transmitted by: Thomas Sturm
Generated on: 20161105
Received on: 20161105
Generator: RedLog, http://www.redlog.eu/
Application: qualitative analysis of systems of ODE in physics, chemistry, and the life sciences
Publication: Algebraic Biology 2008, doi:10.1007/978-3-540-85101-1_15
Additional information:
All problems have the following form: a certain polynomial has a zero where all variables are positive.  Interval solutions for satisfiable problems is a valuable information.
|)
(set-info :series |MBO - Methylene Blue Oscillator System|)
(set-info :instance |E12E15|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= 
(+ (* 80 (* h1 h1 h1) (* h2 h2) h5 (* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1) 
(* h2 h2) h5 (* j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1) (* h2 h2) h5 (* j2 j2 j2 j2
)) (* 780 (* h1 h1 h1) (* h2 h2) h5 (* j2 j2 j2)) (* 444 (* h1 h1 h1) (* h2 h2) 
h5 (* j2 j2)) (* 132 (* h1 h1 h1) (* h2 h2) h5 j2) (* 16 (* h1 h1 h1) (* h2 h2) 
h5) (* 40 (* h1 h1 h1) (* h2 h2) h6 (* j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1) 
(* h2 h2) h6 (* j2 j2 j2 j2 j2)) (* 530 (* h1 h1 h1) (* h2 h2) h6 (* j2 j2 j2 j2
)) (* 616 (* h1 h1 h1) (* h2 h2) h6 (* j2 j2 j2)) (* 386 (* h1 h1 h1) (* h2 h2) 
h6 (* j2 j2)) (* 124 (* h1 h1 h1) (* h2 h2) h6 j2) (* 16 (* h1 h1 h1) (* h2 h2) 
h6) (* 120 (* h1 h1 h1) h2 h3 h4 (* j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1 h1) h2 
h3 h4 (* j2 j2 j2 j2 j2)) (* 982 (* h1 h1 h1) h2 h3 h4 (* j2 j2 j2 j2)) (* 944 
(* h1 h1 h1) h2 h3 h4 (* j2 j2 j2)) (* 502 (* h1 h1 h1) h2 h3 h4 (* j2 j2)) (* 
140 (* h1 h1 h1) h2 h3 h4 j2) (* 16 (* h1 h1 h1) h2 h3 h4) (* 360 (* h1 h1 h1) 
h2 h3 h5 (* j2 j2 j2 j2 j2 j2)) (* 1768 (* h1 h1 h1) h2 h3 h5 (* j2 j2 j2 j2 j2)
) (* 3474 (* h1 h1 h1) h2 h3 h5 (* j2 j2 j2 j2)) (* 3512 (* h1 h1 h1) h2 h3 h5 
(* j2 j2 j2)) (* 1934 (* h1 h1 h1) h2 h3 h5 (* j2 j2)) (* 552 (* h1 h1 h1) h2 h3
 h5 j2) (* 64 (* h1 h1 h1) h2 h3 h5) (* 260 (* h1 h1 h1) h2 h3 h6 (* j2 j2 j2 j2
 j2 j2)) (* 1328 (* h1 h1 h1) h2 h3 h6 (* j2 j2 j2 j2 j2)) (* 2741 (* h1 h1 h1) 
h2 h3 h6 (* j2 j2 j2 j2)) (* 2931 (* h1 h1 h1) h2 h3 h6 (* j2 j2 j2)) (* 1714 
(* h1 h1 h1) h2 h3 h6 (* j2 j2)) (* 520 (* h1 h1 h1) h2 h3 h6 j2) (* 64 (* h1 h1
 h1) h2 h3 h6) (* 100 (* h1 h1 h1) h2 h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 530 (* h1 
h1 h1) h2 h4 h5 (* j2 j2 j2 j2 j2)) (* 1140 (* h1 h1 h1) h2 h4 h5 (* j2 j2 j2 j2
)) (* 1274 (* h1 h1 h1) h2 h4 h5 (* j2 j2 j2)) (* 780 (* h1 h1 h1) h2 h4 h5 (* 
j2 j2)) (* 248 (* h1 h1 h1) h2 h4 h5 j2) (* 32 (* h1 h1 h1) h2 h4 h5) (* 30 (* 
h1 h1 h1) h2 h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 179 (* h1 h1 h1) h2 h4 h6 (* j2 j2 
j2 j2 j2)) (* 424 (* h1 h1 h1) h2 h4 h6 (* j2 j2 j2 j2)) (* 515 (* h1 h1 h1) h2 
h4 h6 (* j2 j2 j2)) (* 340 (* h1 h1 h1) h2 h4 h6 (* j2 j2)) (* 116 (* h1 h1 h1) 
h2 h4 h6 j2) (* 16 (* h1 h1 h1) h2 h4 h6) (* 80 (* h1 h1 h1) h2 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 444 (* h1 h1 h1) h2 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 994 (* 
h1 h1 h1) h2 (* h5 h5) (* j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 (* h5 h5) (* j2 
j2 j2)) (* 730 (* h1 h1 h1) h2 (* h5 h5) (* j2 j2)) (* 240 (* h1 h1 h1) h2 (* h5
 h5) j2) (* 32 (* h1 h1 h1) h2 (* h5 h5)) (* 100 (* h1 h1 h1) h2 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 620 (* h1 h1 h1) h2 h5 h6 (* j2 j2 j2 j2 j2)) (* 1527 (* h1 h1 
h1) h2 h5 h6 (* j2 j2 j2 j2)) (* 1921 (* h1 h1 h1) h2 h5 h6 (* j2 j2 j2)) (* 
1306 (* h1 h1 h1) h2 h5 h6 (* j2 j2)) (* 456 (* h1 h1 h1) h2 h5 h6 j2) (* 64 (* 
h1 h1 h1) h2 h5 h6) (* 40 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
252 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 636 (* h1 h1 h1) h2 (* h6 
h6) (* j2 j2 j2 j2)) (* 828 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2)) (* 588 (* h1
 h1 h1) h2 (* h6 h6) (* j2 j2)) (* 216 (* h1 h1 h1) h2 (* h6 h6) j2) (* 32 (* h1
 h1 h1) h2 (* h6 h6)) (* 300 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2 j2 j2 j2)) 
(* 1280 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2 j2 j2)) (* 2247 (* h1 h1 h1) (* h3
 h3) h4 (* j2 j2 j2 j2)) (* 2077 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2)) (* 1066
 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2)) (* 288 (* h1 h1 h1) (* h3 h3) h4 j2) (* 32
 (* h1 h1 h1) (* h3 h3) h4) (* 400 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2 j2 j2 
j2)) (* 2040 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 3996 (* h1 h1 h1) 
(* h3 h3) h5 (* j2 j2 j2 j2)) (* 3946 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2)) 
(* 2100 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2)) (* 576 (* h1 h1 h1) (* h3 h3) h5 j2
) (* 64 (* h1 h1 h1) (* h3 h3) h5) (* 400 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 
j2 j2 j2)) (* 1840 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 3476 (* h1 
h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 3448 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 
j2)) (* 1892 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 544 (* h1 h1 h1) (* h3 h3) 
h6 j2) (* 64 (* h1 h1 h1) (* h3 h3) h6) (* 90 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2
 j2 j2 j2 j2)) (* 417 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2 j2 j2 j2)) (* 796 (* h1
 h1 h1) h3 (* h4 h4) (* j2 j2 j2 j2)) (* 801 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2 
j2)) (* 448 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2)) (* 132 (* h1 h1 h1) h3 (* h4 h4
) j2) (* 16 (* h1 h1 h1) h3 (* h4 h4)) (* 240 (* h1 h1 h1) h3 h4 h5 (* j2 j2 j2 
j2 j2 j2)) (* 1232 (* h1 h1 h1) h3 h4 h5 (* j2 j2 j2 j2 j2)) (* 2552 (* h1 h1 h1
) h3 h4 h5 (* j2 j2 j2 j2)) (* 2746 (* h1 h1 h1) h3 h4 h5 (* j2 j2 j2)) (* 1626 
(* h1 h1 h1) h3 h4 h5 (* j2 j2)) (* 504 (* h1 h1 h1) h3 h4 h5 j2) (* 64 (* h1 h1
 h1) h3 h4 h5) (* 240 (* h1 h1 h1) h3 h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1192 (* h1
 h1 h1) h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 2440 (* h1 h1 h1) h3 h4 h6 (* j2 j2 j2 
j2)) (* 2632 (* h1 h1 h1) h3 h4 h6 (* j2 j2 j2)) (* 1576 (* h1 h1 h1) h3 h4 h6 
(* j2 j2)) (* 496 (* h1 h1 h1) h3 h4 h6 j2) (* 64 (* h1 h1 h1) h3 h4 h6) (* 160 
(* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 968 (* h1 h1 h1) h3 (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 2272 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 2650
 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2)) (* 1636 (* h1 h1 h1) h3 (* h5 h5) (* j2
 j2)) (* 512 (* h1 h1 h1) h3 (* h5 h5) j2) (* 64 (* h1 h1 h1) h3 (* h5 h5)) (* 
320 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1766 (* h1 h1 h1) h3 h5 h6 
(* j2 j2 j2 j2 j2)) (* 3953 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2 j2)) (* 4591 (* h1
 h1 h1) h3 h5 h6 (* j2 j2 j2)) (* 2916 (* h1 h1 h1) h3 h5 h6 (* j2 j2)) (* 960 
(* h1 h1 h1) h3 h5 h6 j2) (* 128 (* h1 h1 h1) h3 h5 h6) (* 160 (* h1 h1 h1) h3 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 848 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 1856 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 2144 (* h1 h1 h1) h3
 (* h6 h6) (* j2 j2 j2)) (* 1376 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2)) (* 464 (* 
h1 h1 h1) h3 (* h6 h6) j2) (* 64 (* h1 h1 h1) h3 (* h6 h6)) (* 30 (* h1 h1 h1) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 179 (* h1 h1 h1) (* h4 h4) h5 (* j2 j2 j2
 j2 j2)) (* 424 (* h1 h1 h1) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 515 (* h1 h1 h1) 
(* h4 h4) h5 (* j2 j2 j2)) (* 340 (* h1 h1 h1) (* h4 h4) h5 (* j2 j2)) (* 116 
(* h1 h1 h1) (* h4 h4) h5 j2) (* 16 (* h1 h1 h1) (* h4 h4) h5) (* 40 (* h1 h1 h1
) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 262 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 679 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 891 (* h1 h1 h1)
 h4 (* h5 h5) (* j2 j2 j2)) (* 626 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2)) (* 224 
(* h1 h1 h1) h4 (* h5 h5) j2) (* 32 (* h1 h1 h1) h4 (* h5 h5)) (* 100 (* h1 h1 
h1) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 595 (* h1 h1 h1) h4 h5 h6 (* j2 j2 j2 j2 
j2)) (* 1432 (* h1 h1 h1) h4 h5 h6 (* j2 j2 j2 j2)) (* 1791 (* h1 h1 h1) h4 h5 
h6 (* j2 j2 j2)) (* 1230 (* h1 h1 h1) h4 h5 h6 (* j2 j2)) (* 440 (* h1 h1 h1) h4
 h5 h6 j2) (* 64 (* h1 h1 h1) h4 h5 h6) (* 80 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 504 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1277 (* 
h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1665 (* h1 h1 h1) (* h5 h5) h6 (* j2 
j2 j2)) (* 1180 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 432 (* h1 h1 h1) (* h5 
h5) h6 j2) (* 64 (* h1 h1 h1) (* h5 h5) h6) (* 80 (* h1 h1 h1) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1196
 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1548 (* h1 h1 h1) h5 (* h6 h6) 
(* j2 j2 j2)) (* 1108 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) (* 416 (* h1 h1 h1) 
h5 (* h6 h6) j2) (* 64 (* h1 h1 h1) h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2) h5 (* j2 j2 j2 j2 j2)) 
(* 264 (* h1 h1) (* h2 h2 h2) h5 (* j2 j2 j2 j2)) (* 252 (* h1 h1) (* h2 h2 h2) 
h5 (* j2 j2 j2)) (* 132 (* h1 h1) (* h2 h2 h2) h5 (* j2 j2)) (* 36 (* h1 h1) (* 
h2 h2 h2) h5 j2) (* 4 (* h1 h1) (* h2 h2 h2) h5) (* 16 (* h1 h1) (* h2 h2 h2) h6
 (* j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2 h2) h6 (* j2 j2 j2 j2 j2)) (* 
188 (* h1 h1) (* h2 h2 h2) h6 (* j2 j2 j2 j2)) (* 202 (* h1 h1) (* h2 h2 h2) h6 
(* j2 j2 j2)) (* 116 (* h1 h1) (* h2 h2 h2) h6 (* j2 j2)) (* 34 (* h1 h1) (* h2 
h2 h2) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2) h6) (* 48 (* h1 h1) (* h2 h2) h3 h4 
(* j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1) (* h2 h2) h3 h4 (* j2 j2 j2 j2 j2)) (* 
340 (* h1 h1) (* h2 h2) h3 h4 (* j2 j2 j2 j2)) (* 302 (* h1 h1) (* h2 h2) h3 h4 
(* j2 j2 j2)) (* 148 (* h1 h1) (* h2 h2) h3 h4 (* j2 j2)) (* 38 (* h1 h1) (* h2 
h2) h3 h4 j2) (* 4 (* h1 h1) (* h2 h2) h3 h4) (* 176 (* h1 h1) (* h2 h2) h3 h5 
(* j2 j2 j2 j2 j2 j2)) (* 808 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2 j2 j2 j2)) (* 
1476 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2 j2 j2)) (* 1382 (* h1 h1) (* h2 h2) h3 
h5 (* j2 j2 j2)) (* 704 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2)) (* 186 (* h1 h1) 
(* h2 h2) h3 h5 j2) (* 20 (* h1 h1) (* h2 h2) h3 h5) (* 120 (* h1 h1) (* h2 h2) 
h3 h6 (* j2 j2 j2 j2 j2 j2)) (* 588 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2 j2 j2 j2)
) (* 1150 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2 j2 j2)) (* 1153 (* h1 h1) (* h2 h2)
 h3 h6 (* j2 j2 j2)) (* 627 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2)) (* 176 (* h1 h1
) (* h2 h2) h3 h6 j2) (* 20 (* h1 h1) (* h2 h2) h3 h6) (* 136 (* h1 h1) (* h2 h2
) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 664 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2 j2 j2 
j2)) (* 1322 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2 j2 j2)) (* 1372 (* h1 h1) (* h2 
h2) h4 h5 (* j2 j2 j2)) (* 782 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2)) (* 232 (* h1
 h1) (* h2 h2) h4 h5 j2) (* 28 (* h1 h1) (* h2 h2) h4 h5) (* 40 (* h1 h1) (* h2 
h2) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2 j2 j2
 j2)) (* 530 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2 j2 j2)) (* 616 (* h1 h1) (* h2 
h2) h4 h6 (* j2 j2 j2)) (* 386 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2)) (* 124 (* h1
 h1) (* h2 h2) h4 h6 j2) (* 16 (* h1 h1) (* h2 h2) h4 h6) (* 72 (* h1 h1) (* h2 
h2) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 360 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 730 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 j2 j2 j2)) (* 768 (* h1
 h1) (* h2 h2) (* h5 h5) (* j2 j2 j2)) (* 442 (* h1 h1) (* h2 h2) (* h5 h5) (* 
j2 j2)) (* 132 (* h1 h1) (* h2 h2) (* h5 h5) j2) (* 16 (* h1 h1) (* h2 h2) (* h5
 h5)) (* 108 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 576 (* h1 h1) 
(* h2 h2) h5 h6 (* j2 j2 j2 j2 j2)) (* 1239 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2 
j2 j2)) (* 1373 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2 j2)) (* 826 (* h1 h1) (* h2 
h2) h5 h6 (* j2 j2)) (* 256 (* h1 h1) (* h2 h2) h5 h6 j2) (* 32 (* h1 h1) (* h2 
h2) h5 h6) (* 40 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 232 (* 
h1 h1) (* h2 h2) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 530 (* h1 h1) (* h2 h2) (* h6 
h6) (* j2 j2 j2 j2)) (* 616 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2 j2)) (* 386 
(* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2)) (* 124 (* h1 h1) (* h2 h2) (* h6 h6) j2
) (* 16 (* h1 h1) (* h2 h2) (* h6 h6)) (* 168 (* h1 h1) h2 (* h3 h3) h4 (* j2 j2
 j2 j2 j2 j2)) (* 676 (* h1 h1) h2 (* h3 h3) h4 (* j2 j2 j2 j2 j2)) (* 1114 (* 
h1 h1) h2 (* h3 h3) h4 (* j2 j2 j2 j2)) (* 963 (* h1 h1) h2 (* h3 h3) h4 (* j2 
j2 j2)) (* 461 (* h1 h1) h2 (* h3 h3) h4 (* j2 j2)) (* 116 (* h1 h1) h2 (* h3 h3
) h4 j2) (* 12 (* h1 h1) h2 (* h3 h3) h4) (* 304 (* h1 h1) h2 (* h3 h3) h5 (* j2
 j2 j2 j2 j2 j2)) (* 1432 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 2604 
(* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2)) (* 2394 (* h1 h1) h2 (* h3 h3) h5 (* 
j2 j2 j2)) (* 1190 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 306 (* h1 h1) h2 (* 
h3 h3) h5 j2) (* 32 (* h1 h1) h2 (* h3 h3) h5) (* 264 (* h1 h1) h2 (* h3 h3) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1188 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 
2170 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2)) (* 2059 (* h1 h1) h2 (* h3 h3) 
h6 (* j2 j2 j2)) (* 1071 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2)) (* 290 (* h1 h1) 
h2 (* h3 h3) h6 j2) (* 32 (* h1 h1) h2 (* h3 h3) h6) (* 120 (* h1 h1) h2 h3 (* 
h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1) h2 h3 (* h4 h4) (* j2 j2 j2 j2 j2
)) (* 982 (* h1 h1) h2 h3 (* h4 h4) (* j2 j2 j2 j2)) (* 944 (* h1 h1) h2 h3 (* 
h4 h4) (* j2 j2 j2)) (* 502 (* h1 h1) h2 h3 (* h4 h4) (* j2 j2)) (* 140 (* h1 h1
) h2 h3 (* h4 h4) j2) (* 16 (* h1 h1) h2 h3 (* h4 h4)) (* 464 (* h1 h1) h2 h3 h4
 h5 (* j2 j2 j2 j2 j2 j2)) (* 2224 (* h1 h1) h2 h3 h4 h5 (* j2 j2 j2 j2 j2)) (* 
4332 (* h1 h1) h2 h3 h4 h5 (* j2 j2 j2 j2)) (* 4392 (* h1 h1) h2 h3 h4 h5 (* j2 
j2 j2)) (* 2446 (* h1 h1) h2 h3 h4 h5 (* j2 j2)) (* 710 (* h1 h1) h2 h3 h4 h5 j2
) (* 84 (* h1 h1) h2 h3 h4 h5) (* 320 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2 j2 j2 j2
)) (* 1536 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 3024 (* h1 h1) h2 h3 h4 
h6 (* j2 j2 j2 j2)) (* 3120 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2)) (* 1776 (* h1 h1
) h2 h3 h4 h6 (* j2 j2)) (* 528 (* h1 h1) h2 h3 h4 h6 j2) (* 64 (* h1 h1) h2 h3 
h4 h6) (* 224 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1)
 h2 h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2408 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 
j2 j2)) (* 2516 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2)) (* 1416 (* h1 h1) h2 h3 
(* h5 h5) (* j2 j2)) (* 410 (* h1 h1) h2 h3 (* h5 h5) j2) (* 48 (* h1 h1) h2 h3 
(* h5 h5)) (* 436 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2172 (* h1 h1)
 h2 h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 4385 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2)) 
(* 4598 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2)) (* 2643 (* h1 h1) h2 h3 h5 h6 (* j2 
j2)) (* 790 (* h1 h1) h2 h3 h5 h6 j2) (* 96 (* h1 h1) h2 h3 h5 h6) (* 200 (* h1 
h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1000 (* h1 h1) h2 h3 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2042 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2)) (* 2176 (* 
h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2)) (* 1274 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2)
) (* 388 (* h1 h1) h2 h3 (* h6 h6) j2) (* 48 (* h1 h1) h2 h3 (* h6 h6)) (* 82 
(* h1 h1) h2 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 443 (* h1 h1) h2 (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 967 (* h1 h1) h2 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 1093
 (* h1 h1) h2 (* h4 h4) h5 (* j2 j2 j2)) (* 675 (* h1 h1) h2 (* h4 h4) h5 (* j2 
j2)) (* 216 (* h1 h1) h2 (* h4 h4) h5 j2) (* 28 (* h1 h1) h2 (* h4 h4) h5) (* 6 
(* h1 h1) h2 (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 37 (* h1 h1) h2 (* h4 h4) h6
 (* j2 j2 j2 j2 j2)) (* 91 (* h1 h1) h2 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 115 (* 
h1 h1) h2 (* h4 h4) h6 (* j2 j2 j2)) (* 79 (* h1 h1) h2 (* h4 h4) h6 (* j2 j2)) 
(* 28 (* h1 h1) h2 (* h4 h4) h6 j2) (* 4 (* h1 h1) h2 (* h4 h4) h6) (* 116 (* h1
 h1) h2 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 650 (* h1 h1) h2 h4 (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 1470 (* h1 h1) h2 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 1717 (* 
h1 h1) h2 h4 (* h5 h5) (* j2 j2 j2)) (* 1093 (* h1 h1) h2 h4 (* h5 h5) (* j2 j2)
) (* 360 (* h1 h1) h2 h4 (* h5 h5) j2) (* 48 (* h1 h1) h2 h4 (* h5 h5)) (* 198 
(* h1 h1) h2 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1101 (* h1 h1) h2 h4 h5 h6 (* j2
 j2 j2 j2 j2)) (* 2479 (* h1 h1) h2 h4 h5 h6 (* j2 j2 j2 j2)) (* 2899 (* h1 h1) 
h2 h4 h5 h6 (* j2 j2 j2)) (* 1859 (* h1 h1) h2 h4 h5 h6 (* j2 j2)) (* 620 (* h1 
h1) h2 h4 h5 h6 j2) (* 84 (* h1 h1) h2 h4 h5 h6) (* 14 (* h1 h1) h2 h4 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 89 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
227 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 299 (* h1 h1) h2 h4 (* h6 h6) 
(* j2 j2 j2)) (* 215 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2)) (* 80 (* h1 h1) h2 h4 
(* h6 h6) j2) (* 12 (* h1 h1) h2 h4 (* h6 h6)) (* 16 (* h1 h1) h2 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 92 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
214 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 258 (* h1 h1) h2 (* h5 h5 h5) 
(* j2 j2 j2)) (* 170 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2)) (* 58 (* h1 h1) h2 (* 
h5 h5 h5) j2) (* 8 (* h1 h1) h2 (* h5 h5 h5)) (* 116 (* h1 h1) h2 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
1565 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1877 (* h1 h1) h2 (* h5 h5) 
h6 (* j2 j2 j2)) (* 1224 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2)) (* 412 (* h1 h1) 
h2 (* h5 h5) h6 j2) (* 56 (* h1 h1) h2 (* h5 h5) h6) (* 114 (* h1 h1) h2 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 647 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 1489 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1783 (* h1 h1) h2 h5 
(* h6 h6) (* j2 j2 j2)) (* 1173 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2)) (* 402 (* 
h1 h1) h2 h5 (* h6 h6) j2) (* 56 (* h1 h1) h2 h5 (* h6 h6)) (* 8 (* h1 h1) h2 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 136 (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 184 (* h1 h1) h2 
(* h6 h6 h6) (* j2 j2 j2)) (* 136 (* h1 h1) h2 (* h6 h6 h6) (* j2 j2)) (* 52 (* 
h1 h1) h2 (* h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h6 h6 h6)) (* 120 (* h1 h1) (* 
h3 h3 h3) h4 (* j2 j2 j2 j2 j2 j2)) (* 476 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2 j2
 j2 j2)) (* 774 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 661 (* h1 h1) (* 
h3 h3 h3) h4 (* j2 j2 j2)) (* 313 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2)) (* 78 (* 
h1 h1) (* h3 h3 h3) h4 j2) (* 8 (* h1 h1) (* h3 h3 h3) h4) (* 160 (* h1 h1) (* 
h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2
 j2 j2)) (* 1392 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 1264 (* h1 h1) 
(* h3 h3 h3) h5 (* j2 j2 j2)) (* 618 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2)) (* 156
 (* h1 h1) (* h3 h3 h3) h5 j2) (* 16 (* h1 h1) (* h3 h3 h3) h5) (* 160 (* h1 h1)
 (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 688 (* h1 h1) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2)) (* 1208 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 1108 (* h1 
h1) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 560 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2)) 
(* 148 (* h1 h1) (* h3 h3 h3) h6 j2) (* 16 (* h1 h1) (* h3 h3 h3) h6) (* 120 (* 
h1 h1) (* h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1) (* h3 h3) (* 
h4 h4) (* j2 j2 j2 j2 j2)) (* 982 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 j2 j2 j2))
 (* 944 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 j2 j2)) (* 502 (* h1 h1) (* h3 h3) 
(* h4 h4) (* j2 j2)) (* 140 (* h1 h1) (* h3 h3) (* h4 h4) j2) (* 16 (* h1 h1) 
(* h3 h3) (* h4 h4)) (* 340 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 
1580 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 3009 (* h1 h1) (* h3 h3) 
h4 h5 (* j2 j2 j2 j2)) (* 3002 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 1653 
(* h1 h1) (* h3 h3) h4 h5 (* j2 j2)) (* 476 (* h1 h1) (* h3 h3) h4 h5 j2) (* 56 
(* h1 h1) (* h3 h3) h4 h5) (* 280 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2
)) (* 1304 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 2494 (* h1 h1) (* h3
 h3) h4 h6 (* j2 j2 j2 j2)) (* 2504 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 
1390 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2)) (* 404 (* h1 h1) (* h3 h3) h4 h6 j2) 
(* 48 (* h1 h1) (* h3 h3) h4 h6) (* 160 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 832 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1680 
(* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 1728 (* h1 h1) (* h3 h3) (* h5
 h5) (* j2 j2 j2)) (* 962 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2)) (* 276 (* h1 
h1) (* h3 h3) (* h5 h5) j2) (* 32 (* h1 h1) (* h3 h3) (* h5 h5)) (* 340 (* h1 h1
) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1616 (* h1 h1) (* h3 h3) h5 h6 (* j2
 j2 j2 j2 j2)) (* 3145 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 3207 (* h1 
h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 1806 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2)) 
(* 532 (* h1 h1) (* h3 h3) h5 h6 j2) (* 64 (* h1 h1) (* h3 h3) h5 h6) (* 160 (* 
h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1512 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)
) (* 1560 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 888 (* h1 h1) (* h3 h3)
 (* h6 h6) (* j2 j2)) (* 264 (* h1 h1) (* h3 h3) (* h6 h6) j2) (* 32 (* h1 h1) 
(* h3 h3) (* h6 h6)) (* 18 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 
87 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2 j2 j2 j2)) (* 173 (* h1 h1) h3 (* h4 h4 h4
) (* j2 j2 j2 j2)) (* 181 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2 j2)) (* 105 (* h1 
h1) h3 (* h4 h4 h4) (* j2 j2)) (* 32 (* h1 h1) h3 (* h4 h4 h4) j2) (* 4 (* h1 h1
) h3 (* h4 h4 h4)) (* 114 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
563 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1151 (* h1 h1) h3 (* h4 h4)
 h5 (* j2 j2 j2 j2)) (* 1247 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2)) (* 755 (* 
h1 h1) h3 (* h4 h4) h5 (* j2 j2)) (* 242 (* h1 h1) h3 (* h4 h4) h5 j2) (* 32 (* 
h1 h1) h3 (* h4 h4) h5) (* 66 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 335 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 701 (* h1 h1) h3 (* h4 
h4) h6 (* j2 j2 j2 j2)) (* 773 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2 j2)) (* 473 
(* h1 h1) h3 (* h4 h4) h6 (* j2 j2)) (* 152 (* h1 h1) h3 (* h4 h4) h6 j2) (* 20 
(* h1 h1) h3 (* h4 h4) h6) (* 144 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 792 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1758 (* h1 h1) h3 h4 
(* h5 h5) (* j2 j2 j2 j2)) (* 2025 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 
1279 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2)) (* 420 (* h1 h1) h3 h4 (* h5 h5) j2) 
(* 56 (* h1 h1) h3 h4 (* h5 h5)) (* 260 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 1346 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 2892 (* h1 h1) h3 h4 
h5 h6 (* j2 j2 j2 j2)) (* 3294 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2)) (* 2092 (* h1
 h1) h3 h4 h5 h6 (* j2 j2)) (* 700 (* h1 h1) h3 h4 h5 h6 j2) (* 96 (* h1 h1) h3 
h4 h5 h6) (* 80 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 424 (* h1 h1
) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 928 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 
j2 j2)) (* 1072 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 688 (* h1 h1) h3 h4 
(* h6 h6) (* j2 j2)) (* 232 (* h1 h1) h3 h4 (* h6 h6) j2) (* 32 (* h1 h1) h3 h4 
(* h6 h6)) (* 32 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 200 (* h1 
h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 488 (* h1 h1) h3 (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 594 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 382 (* h1 h1) h3 
(* h5 h5 h5) (* j2 j2)) (* 124 (* h1 h1) h3 (* h5 h5 h5) j2) (* 16 (* h1 h1) h3 
(* h5 h5 h5)) (* 144 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 802 (* 
h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1815 (* h1 h1) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2141 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 1388 (* h1 h1) 
h3 (* h5 h5) h6 (* j2 j2)) (* 468 (* h1 h1) h3 (* h5 h5) h6 j2) (* 64 (* h1 h1) 
h3 (* h5 h5) h6) (* 144 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 772 
(* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1718 (* h1 h1) h3 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 2024 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 1326 (* h1 
h1) h3 h5 (* h6 h6) (* j2 j2)) (* 456 (* h1 h1) h3 h5 (* h6 h6) j2) (* 64 (* h1 
h1) h3 h5 (* h6 h6)) (* 32 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
176 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1) h3 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 480 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 320 (* h1
 h1) h3 (* h6 h6 h6) (* j2 j2)) (* 112 (* h1 h1) h3 (* h6 h6 h6) j2) (* 16 (* h1
 h1) h3 (* h6 h6 h6)) (* 6 (* h1 h1) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
37 (* h1 h1) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 91 (* h1 h1) (* h4 h4 h4) h5
 (* j2 j2 j2 j2)) (* 115 (* h1 h1) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 79 (* h1 h1)
 (* h4 h4 h4) h5 (* j2 j2)) (* 28 (* h1 h1) (* h4 h4 h4) h5 j2) (* 4 (* h1 h1) 
(* h4 h4 h4) h5) (* 20 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
126 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 318 (* h1 h1) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2)) (* 414 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 294 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2)) (* 108 (* h1 h1) (* h4 h4) (* h5
 h5) j2) (* 16 (* h1 h1) (* h4 h4) (* h5 h5)) (* 26 (* h1 h1) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
398 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 514 (* h1 h1) (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 364 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2)) (* 134 (* h1 h1) (* h4
 h4) h5 h6 j2) (* 20 (* h1 h1) (* h4 h4) h5 h6) (* 8 (* h1 h1) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
145 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 198 (* h1 h1) h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 145 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2)) (* 54 (* h1 h1) h4 (* 
h5 h5 h5) j2) (* 8 (* h1 h1) h4 (* h5 h5 h5)) (* 58 (* h1 h1) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 357 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
893 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1165 (* h1 h1) h4 (* h5 h5) h6
 (* j2 j2 j2)) (* 837 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2)) (* 314 (* h1 h1) h4 
(* h5 h5) h6 j2) (* 48 (* h1 h1) h4 (* h5 h5) h6) (* 36 (* h1 h1) h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 223 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 563 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 743 (* h1 h1) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 541 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2)) (* 206 (* h1 h1) 
h4 h5 (* h6 h6) j2) (* 32 (* h1 h1) h4 h5 (* h6 h6)) (* 16 (* h1 h1) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 273 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 370 (* h1 h1) (* h5 h5 h5)
 h6 (* j2 j2 j2)) (* 273 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) (* 104 (* h1 h1) 
(* h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h5 h5 h5) h6) (* 36 (* h1 h1) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 221 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 555 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 731 (* h1 h1
) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 533 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 
j2)) (* 204 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h5 h5) (* h6 h6
)) (* 16 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 344 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1) h5 (* h6 h6 
h6) (* j2 j2)) (* 100 (* h1 h1) h5 (* h6 h6 h6) j2) (* 16 (* h1 h1) h5 (* h6 h6 
h6)) (* 32 h1 (* h2 h2 h2) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2 h2) 
h4 h5 (* j2 j2 j2 j2 j2)) (* 264 h1 (* h2 h2 h2) h4 h5 (* j2 j2 j2 j2)) (* 252 
h1 (* h2 h2 h2) h4 h5 (* j2 j2 j2)) (* 132 h1 (* h2 h2 h2) h4 h5 (* j2 j2)) (* 
36 h1 (* h2 h2 h2) h4 h5 j2) (* 4 h1 (* h2 h2 h2) h4 h5) (* 8 h1 (* h2 h2 h2) h4
 h6 (* j2 j2 j2 j2 j2 j2)) (* 44 h1 (* h2 h2 h2) h4 h6 (* j2 j2 j2 j2 j2)) (* 94
 h1 (* h2 h2 h2) h4 h6 (* j2 j2 j2 j2)) (* 101 h1 (* h2 h2 h2) h4 h6 (* j2 j2 j2
)) (* 58 h1 (* h2 h2 h2) h4 h6 (* j2 j2)) (* 17 h1 (* h2 h2 h2) h4 h6 j2) (* 2 
h1 (* h2 h2 h2) h4 h6) (* 16 h1 (* h2 h2 h2) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 72 h1 (* h2 h2 h2) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 132 h1 (* h2 h2 h2) (* h5
 h5) (* j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2) (* h5 h5) (* j2 j2 j2)) (* 66 h1 
(* h2 h2 h2) (* h5 h5) (* j2 j2)) (* 18 h1 (* h2 h2 h2) (* h5 h5) j2) (* 2 h1 
(* h2 h2 h2) (* h5 h5)) (* 24 h1 (* h2 h2 h2) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
116 h1 (* h2 h2 h2) h5 h6 (* j2 j2 j2 j2 j2)) (* 226 h1 (* h2 h2 h2) h5 h6 (* j2
 j2 j2 j2)) (* 227 h1 (* h2 h2 h2) h5 h6 (* j2 j2 j2)) (* 124 h1 (* h2 h2 h2) h5
 h6 (* j2 j2)) (* 35 h1 (* h2 h2 h2) h5 h6 j2) (* 4 h1 (* h2 h2 h2) h5 h6) (* 8 
h1 (* h2 h2 h2) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 44 h1 (* h2 h2 h2) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 94 h1 (* h2 h2 h2) (* h6 h6) (* j2 j2 j2 j2)) (* 101 h1 
(* h2 h2 h2) (* h6 h6) (* j2 j2 j2)) (* 58 h1 (* h2 h2 h2) (* h6 h6) (* j2 j2)) 
(* 17 h1 (* h2 h2 h2) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h6 h6)) (* 24 h1 (* 
h2 h2) h3 (* h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2) h3 (* h4 h4) (* 
j2 j2 j2 j2 j2)) (* 170 h1 (* h2 h2) h3 (* h4 h4) (* j2 j2 j2 j2)) (* 151 h1 (* 
h2 h2) h3 (* h4 h4) (* j2 j2 j2)) (* 74 h1 (* h2 h2) h3 (* h4 h4) (* j2 j2)) (* 
19 h1 (* h2 h2) h3 (* h4 h4) j2) (* 2 h1 (* h2 h2) h3 (* h4 h4)) (* 144 h1 (* h2
 h2) h3 h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 632 h1 (* h2 h2) h3 h4 h5 (* j2 j2 j2 j2
 j2)) (* 1132 h1 (* h2 h2) h3 h4 h5 (* j2 j2 j2 j2)) (* 1058 h1 (* h2 h2) h3 h4 
h5 (* j2 j2 j2)) (* 544 h1 (* h2 h2) h3 h4 h5 (* j2 j2)) (* 146 h1 (* h2 h2) h3 
h4 h5 j2) (* 16 h1 (* h2 h2) h3 h4 h5) (* 72 h1 (* h2 h2) h3 h4 h6 (* j2 j2 j2 
j2 j2 j2)) (* 332 h1 (* h2 h2) h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 622 h1 (* h2 h2) 
h3 h4 h6 (* j2 j2 j2 j2)) (* 605 h1 (* h2 h2) h3 h4 h6 (* j2 j2 j2)) (* 322 h1 
(* h2 h2) h3 h4 h6 (* j2 j2)) (* 89 h1 (* h2 h2) h3 h4 h6 j2) (* 10 h1 (* h2 h2)
 h3 h4 h6) (* 64 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 304 h1 (* 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 568 h1 (* h2 h2) h3 (* h5 h5) (* j2 
j2 j2 j2)) (* 540 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 278 h1 (* h2 h2) h3
 (* h5 h5) (* j2 j2)) (* 74 h1 (* h2 h2) h3 (* h5 h5) j2) (* 8 h1 (* h2 h2) h3 
(* h5 h5)) (* 120 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 548 h1 (* h2 
h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 1018 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) 
(* 983 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 520 h1 (* h2 h2) h3 h5 h6 (* j2 j2
)) (* 143 h1 (* h2 h2) h3 h5 h6 j2) (* 16 h1 (* h2 h2) h3 h5 h6) (* 48 h1 (* h2 
h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 232 h1 (* h2 h2) h3 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 452 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 454 h1 (* h2 
h2) h3 (* h6 h6) (* j2 j2 j2)) (* 248 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2)) (* 70
 h1 (* h2 h2) h3 (* h6 h6) j2) (* 8 h1 (* h2 h2) h3 (* h6 h6)) (* 56 h1 (* h2 h2
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 276 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 554 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 579 h1 (* h2 h2)
 (* h4 h4) h5 (* j2 j2 j2)) (* 332 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2)) (* 99 h1
 (* h2 h2) (* h4 h4) h5 j2) (* 12 h1 (* h2 h2) (* h4 h4) h5) (* 4 h1 (* h2 h2) 
(* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h4 h4) h6 (* j2 j2 j2 
j2 j2)) (* 57 h1 (* h2 h2) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 69 h1 (* h2 h2) (* 
h4 h4) h6 (* j2 j2 j2)) (* 45 h1 (* h2 h2) (* h4 h4) h6 (* j2 j2)) (* 15 h1 (* 
h2 h2) (* h4 h4) h6 j2) (* 2 h1 (* h2 h2) (* h4 h4) h6) (* 60 h1 (* h2 h2) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 623 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 661 h1 (* h2 h2) h4 
(* h5 h5) (* j2 j2 j2)) (* 383 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2)) (* 115 h1 
(* h2 h2) h4 (* h5 h5) j2) (* 14 h1 (* h2 h2) h4 (* h5 h5)) (* 112 h1 (* h2 h2) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 560 h1 (* h2 h2) h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 1140 h1 (* h2 h2) h4 h5 h6 (* j2 j2 j2 j2)) (* 1208 h1 (* h2 h2) h4 h5 h6 
(* j2 j2 j2)) (* 702 h1 (* h2 h2) h4 h5 h6 (* j2 j2)) (* 212 h1 (* h2 h2) h4 h5 
h6 j2) (* 26 h1 (* h2 h2) h4 h5 h6) (* 8 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 48 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 114 h1 (* h2 
h2) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 138 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2))
 (* 90 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2)) (* 30 h1 (* h2 h2) h4 (* h6 h6) j2) 
(* 4 h1 (* h2 h2) h4 (* h6 h6)) (* 8 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 40 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 82 h1 (* h2 h2) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 88 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2 j2)) (* 52 
h1 (* h2 h2) (* h5 h5 h5) (* j2 j2)) (* 16 h1 (* h2 h2) (* h5 h5 h5) j2) (* 2 h1
 (* h2 h2) (* h5 h5 h5)) (* 56 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 288 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 598 h1 (* h2 h2) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 642 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 376 h1
 (* h2 h2) (* h5 h5) h6 (* j2 j2)) (* 114 h1 (* h2 h2) (* h5 h5) h6 j2) (* 14 h1
 (* h2 h2) (* h5 h5) h6) (* 56 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 284 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 586 h1 (* h2 h2) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 629 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 370 h1
 (* h2 h2) h5 (* h6 h6) (* j2 j2)) (* 113 h1 (* h2 h2) h5 (* h6 h6) j2) (* 14 h1
 (* h2 h2) h5 (* h6 h6)) (* 4 h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 24 h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 57 h1 (* h2 h2) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 69 h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 j2)) (* 45 h1 (* 
h2 h2) (* h6 h6 h6) (* j2 j2)) (* 15 h1 (* h2 h2) (* h6 h6 h6) j2) (* 2 h1 (* h2
 h2) (* h6 h6 h6)) (* 48 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 200
 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2)) (* 340 h1 h2 (* h3 h3) (* h4 h4) 
(* j2 j2 j2 j2)) (* 302 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2 j2)) (* 148 h1 h2 (* 
h3 h3) (* h4 h4) (* j2 j2)) (* 38 h1 h2 (* h3 h3) (* h4 h4) j2) (* 4 h1 h2 (* h3
 h3) (* h4 h4)) (* 192 h1 h2 (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 832 h1 h2
 (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 1472 h1 h2 (* h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 1360 h1 h2 (* h3 h3) h4 h5 (* j2 j2 j2)) (* 692 h1 h2 (* h3 h3) h4 h5 
(* j2 j2)) (* 184 h1 h2 (* h3 h3) h4 h5 j2) (* 20 h1 h2 (* h3 h3) h4 h5) (* 120 
h1 h2 (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 532 h1 h2 (* h3 h3) h4 h6 (* j2 
j2 j2 j2 j2)) (* 962 h1 h2 (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 907 h1 h2 (* h3 
h3) h4 h6 (* j2 j2 j2)) (* 470 h1 h2 (* h3 h3) h4 h6 (* j2 j2)) (* 127 h1 h2 (* 
h3 h3) h4 h6 j2) (* 14 h1 h2 (* h3 h3) h4 h6) (* 80 h1 h2 (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 392 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
740 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 702 h1 h2 (* h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 358 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 94 h1 h2 (* h3 h3) 
(* h5 h5) j2) (* 10 h1 h2 (* h3 h3) (* h5 h5)) (* 168 h1 h2 (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 748 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 1358 h1 
h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1285 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2)) 
(* 668 h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 181 h1 h2 (* h3 h3) h5 h6 j2) (* 20 
h1 h2 (* h3 h3) h5 h6) (* 72 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 332 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 622 h1 h2 (* h3 h3) (* 
h6 h6) (* j2 j2 j2 j2)) (* 605 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 322 h1
 h2 (* h3 h3) (* h6 h6) (* j2 j2)) (* 89 h1 h2 (* h3 h3) (* h6 h6) j2) (* 10 h1 
h2 (* h3 h3) (* h6 h6)) (* 12 h1 h2 h3 (* h4 h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 56
 h1 h2 h3 (* h4 h4 h4) (* j2 j2 j2 j2 j2)) (* 107 h1 h2 h3 (* h4 h4 h4) (* j2 j2
 j2 j2)) (* 107 h1 h2 h3 (* h4 h4 h4) (* j2 j2 j2)) (* 59 h1 h2 h3 (* h4 h4 h4) 
(* j2 j2)) (* 17 h1 h2 h3 (* h4 h4 h4) j2) (* 2 h1 h2 h3 (* h4 h4 h4)) (* 128 h1
 h2 h3 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 616 h1 h2 h3 (* h4 h4) h5 (* j2 j2
 j2 j2 j2)) (* 1216 h1 h2 h3 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 1258 h1 h2 h3 (* 
h4 h4) h5 (* j2 j2 j2)) (* 718 h1 h2 h3 (* h4 h4) h5 (* j2 j2)) (* 214 h1 h2 h3 
(* h4 h4) h5 j2) (* 26 h1 h2 h3 (* h4 h4) h5) (* 44 h1 h2 h3 (* h4 h4) h6 (* j2 
j2 j2 j2 j2 j2)) (* 216 h1 h2 h3 (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 435 h1 h2 
h3 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 459 h1 h2 h3 (* h4 h4) h6 (* j2 j2 j2)) (* 
267 h1 h2 h3 (* h4 h4) h6 (* j2 j2)) (* 81 h1 h2 h3 (* h4 h4) h6 j2) (* 10 h1 h2
 h3 (* h4 h4) h6) (* 136 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 672 h1 
h2 h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1354 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2
 j2)) (* 1422 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2)) (* 820 h1 h2 h3 h4 (* h5 h5) 
(* j2 j2)) (* 246 h1 h2 h3 h4 (* h5 h5) j2) (* 30 h1 h2 h3 h4 (* h5 h5)) (* 256 
h1 h2 h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1248 h1 h2 h3 h4 h5 h6 (* j2 j2 j2 
j2 j2)) (* 2496 h1 h2 h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 2616 h1 h2 h3 h4 h5 h6 (* 
j2 j2 j2)) (* 1512 h1 h2 h3 h4 h5 h6 (* j2 j2)) (* 456 h1 h2 h3 h4 h5 h6 j2) (* 
56 h1 h2 h3 h4 h5 h6) (* 52 h1 h2 h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 264 
h1 h2 h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 549 h1 h2 h3 h4 (* h6 h6) (* j2 j2 
j2 j2)) (* 597 h1 h2 h3 h4 (* h6 h6) (* j2 j2 j2)) (* 357 h1 h2 h3 h4 (* h6 h6) 
(* j2 j2)) (* 111 h1 h2 h3 h4 (* h6 h6) j2) (* 14 h1 h2 h3 h4 (* h6 h6)) (* 24 
h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 h3 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 270 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 290 h1 h2 h3 (* 
h5 h5 h5) (* j2 j2 j2)) (* 168 h1 h2 h3 (* h5 h5 h5) (* j2 j2)) (* 50 h1 h2 h3 
(* h5 h5 h5) j2) (* 6 h1 h2 h3 (* h5 h5 h5)) (* 128 h1 h2 h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 640 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1304 h1 h2 
h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1384 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 
806 h1 h2 h3 (* h5 h5) h6 (* j2 j2)) (* 244 h1 h2 h3 (* h5 h5) h6 j2) (* 30 h1 
h2 h3 (* h5 h5) h6) (* 128 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 632 
h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1280 h1 h2 h3 h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 1358 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2)) (* 794 h1 h2 h3 h5 (* h6 h6
) (* j2 j2)) (* 242 h1 h2 h3 h5 (* h6 h6) j2) (* 30 h1 h2 h3 h5 (* h6 h6)) (* 20
 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 104 h1 h2 h3 (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 221 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 245 h1 h2 h3 (* 
h6 h6 h6) (* j2 j2 j2)) (* 149 h1 h2 h3 (* h6 h6 h6) (* j2 j2)) (* 47 h1 h2 h3 
(* h6 h6 h6) j2) (* 6 h1 h2 h3 (* h6 h6 h6)) (* 10 h1 h2 (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 55 h1 h2 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 123 h1 h2 
(* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 143 h1 h2 (* h4 h4 h4) h5 (* j2 j2 j2)) (* 
91 h1 h2 (* h4 h4 h4) h5 (* j2 j2)) (* 30 h1 h2 (* h4 h4 h4) h5 j2) (* 4 h1 h2 
(* h4 h4 h4) h5) (* 32 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 176 
h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 396 h1 h2 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 466 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 302 h1 h2 (* 
h4 h4) (* h5 h5) (* j2 j2)) (* 102 h1 h2 (* h4 h4) (* h5 h5) j2) (* 14 h1 h2 (* 
h4 h4) (* h5 h5)) (* 34 h1 h2 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 191 h1 
h2 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 437 h1 h2 (* h4 h4) h5 h6 (* j2 j2 j2 
j2)) (* 521 h1 h2 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 341 h1 h2 (* h4 h4) h5 h6 (* 
j2 j2)) (* 116 h1 h2 (* h4 h4) h5 h6 j2) (* 16 h1 h2 (* h4 h4) h5 h6) (* 16 h1 
h2 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 92 h1 h2 h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 214 h1 h2 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 258 h1 h2 h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 170 h1 h2 h4 (* h5 h5 h5) (* j2 j2)) (* 58 h1 h2 h4 (* 
h5 h5 h5) j2) (* 8 h1 h2 h4 (* h5 h5 h5)) (* 64 h1 h2 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 356 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 810 h1 h2 h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 964 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 632 
h1 h2 h4 (* h5 h5) h6 (* j2 j2)) (* 216 h1 h2 h4 (* h5 h5) h6 j2) (* 30 h1 h2 h4
 (* h5 h5) h6) (* 38 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 217 h1 h2 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 505 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 613 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 409 h1 h2 h4 h5 (* h6 h6) (* j2 
j2)) (* 142 h1 h2 h4 h5 (* h6 h6) j2) (* 20 h1 h2 h4 h5 (* h6 h6)) (* 16 h1 h2 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 92 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 214 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 258 h1 h2 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 170 h1 h2 (* h5 h5 h5) h6 (* j2 j2)) (* 58 h1 h2 (* h5 h5 h5
) h6 j2) (* 8 h1 h2 (* h5 h5 h5) h6) (* 32 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 180 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 414 h1 h2 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 498 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 330 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2)) (* 114 h1 h2 (* h5 h5) (* h6 h6
) j2) (* 16 h1 h2 (* h5 h5) (* h6 h6)) (* 14 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 81 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 191 h1 h2 h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 235 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 159 h1 h2
 h5 (* h6 h6 h6) (* j2 j2)) (* 56 h1 h2 h5 (* h6 h6 h6) j2) (* 8 h1 h2 h5 (* h6 
h6 h6)) (* 24 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h3 
h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2)) (* 170 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2 
j2 j2)) (* 151 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)) (* 74 h1 (* h3 h3 h3) (* 
h4 h4) (* j2 j2)) (* 19 h1 (* h3 h3 h3) (* h4 h4) j2) (* 2 h1 (* h3 h3 h3) (* h4
 h4)) (* 80 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 344 h1 (* h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2)) (* 604 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 554 
h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 280 h1 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 
74 h1 (* h3 h3 h3) h4 h5 j2) (* 8 h1 (* h3 h3 h3) h4 h5) (* 56 h1 (* h3 h3 h3) 
h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 244 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) 
(* 434 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 403 h1 (* h3 h3 h3) h4 h6 (* j2
 j2 j2)) (* 206 h1 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 55 h1 (* h3 h3 h3) h4 h6 j2)
 (* 6 h1 (* h3 h3 h3) h4 h6) (* 32 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 160 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3 h3)
 (* h5 h5) (* j2 j2 j2 j2)) (* 288 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
146 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 38 h1 (* h3 h3 h3) (* h5 h5) j2) (* 
4 h1 (* h3 h3 h3) (* h5 h5)) (* 72 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 316 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 566 h1 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2)) (* 529 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 272 h1 (* h3 h3 
h3) h5 h6 (* j2 j2)) (* 73 h1 (* h3 h3 h3) h5 h6 j2) (* 8 h1 (* h3 h3 h3) h5 h6)
 (* 32 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 264 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) 
(* 252 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 132 h1 (* h3 h3 h3) (* h6 h6) 
(* j2 j2)) (* 36 h1 (* h3 h3 h3) (* h6 h6) j2) (* 4 h1 (* h3 h3 h3) (* h6 h6)) 
(* 12 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h3 h3) (* h4 
h4 h4) (* j2 j2 j2 j2 j2)) (* 107 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2 j2)) (* 
107 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2)) (* 59 h1 (* h3 h3) (* h4 h4 h4) (* 
j2 j2)) (* 17 h1 (* h3 h3) (* h4 h4 h4) j2) (* 2 h1 (* h3 h3) (* h4 h4 h4)) (* 
72 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 340 h1 (* h3 h3) (* h4 h4
) h5 (* j2 j2 j2 j2 j2)) (* 662 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 
679 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 386 h1 (* h3 h3) (* h4 h4) h5 (* 
j2 j2)) (* 115 h1 (* h3 h3) (* h4 h4) h5 j2) (* 14 h1 (* h3 h3) (* h4 h4) h5) 
(* 40 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h3 h3) (* h4
 h4) h6 (* j2 j2 j2 j2 j2)) (* 378 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) 
(* 390 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 222 h1 (* h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 66 h1 (* h3 h3) (* h4 h4) h6 j2) (* 8 h1 (* h3 h3) (* h4 h4) h6) 
(* 76 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 368 h1 (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 731 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 761 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 437 h1 (* h3 h3) h4 (* h5 h5) 
(* j2 j2)) (* 131 h1 (* h3 h3) h4 (* h5 h5) j2) (* 16 h1 (* h3 h3) h4 (* h5 h5))
 (* 144 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 688 h1 (* h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2)) (* 1356 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 1408 h1
 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 810 h1 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 244
 h1 (* h3 h3) h4 h5 h6 j2) (* 30 h1 (* h3 h3) h4 h5 h6) (* 44 h1 (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 216 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 435 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 459 h1 (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2)) (* 267 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 81 h1 (* 
h3 h3) h4 (* h6 h6) j2) (* 10 h1 (* h3 h3) h4 (* h6 h6)) (* 16 h1 (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 188 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 202 h1 (* h3 h3) (* h5
 h5 h5) (* j2 j2 j2)) (* 116 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 34 h1 (* h3
 h3) (* h5 h5 h5) j2) (* 4 h1 (* h3 h3) (* h5 h5 h5)) (* 72 h1 (* h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 352 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 706 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 742 h1 (* h3 h3) (* h5 
h5) h6 (* j2 j2 j2)) (* 430 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 130 h1 (* h3
 h3) (* h5 h5) h6 j2) (* 16 h1 (* h3 h3) (* h5 h5) h6) (* 72 h1 (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 348 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 694 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 729 h1 (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2)) (* 424 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 129 h1 (* h3
 h3) h5 (* h6 h6) j2) (* 16 h1 (* h3 h3) h5 (* h6 h6)) (* 16 h1 (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 164 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 176 h1 (* h3 h3) (* h6 h6
 h6) (* j2 j2 j2)) (* 104 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 32 h1 (* h3 h3
) (* h6 h6 h6) j2) (* 4 h1 (* h3 h3) (* h6 h6 h6)) (* 12 h1 h3 (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 60 h1 h3 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 125 h1
 h3 (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 139 h1 h3 (* h4 h4 h4) h5 (* j2 j2 j2)) 
(* 87 h1 h3 (* h4 h4 h4) h5 (* j2 j2)) (* 29 h1 h3 (* h4 h4 h4) h5 j2) (* 4 h1 
h3 (* h4 h4 h4) h5) (* 34 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
181 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 398 h1 h3 (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 462 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 298 h1 h3
 (* h4 h4) (* h5 h5) (* j2 j2)) (* 101 h1 h3 (* h4 h4) (* h5 h5) j2) (* 14 h1 h3
 (* h4 h4) (* h5 h5)) (* 40 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 206 
h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 443 h1 h3 (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 509 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 329 h1 h3 (* h4 h4) h5 h6 
(* j2 j2)) (* 113 h1 h3 (* h4 h4) h5 h6 j2) (* 16 h1 h3 (* h4 h4) h5 h6) (* 16 
h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 92 h1 h3 h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 214 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 258 h1 h3 h4 (* 
h5 h5 h5) (* j2 j2 j2)) (* 170 h1 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 58 h1 h3 h4 
(* h5 h5 h5) j2) (* 8 h1 h3 h4 (* h5 h5 h5)) (* 68 h1 h3 h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 366 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 814 h1 h3 
h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 956 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 
624 h1 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 214 h1 h3 h4 (* h5 h5) h6 j2) (* 30 h1 
h3 h4 (* h5 h5) h6) (* 44 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 232 h1
 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 511 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2
 j2)) (* 601 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 397 h1 h3 h4 h5 (* h6 h6) 
(* j2 j2)) (* 139 h1 h3 h4 h5 (* h6 h6) j2) (* 20 h1 h3 h4 h5 (* h6 h6)) (* 16 
h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 92 h1 h3 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 214 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 258 h1 h3 (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 170 h1 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 58 h1 h3 (* 
h5 h5 h5) h6 j2) (* 8 h1 h3 (* h5 h5 h5) h6) (* 34 h1 h3 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 185 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 416 
h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 494 h1 h3 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 326 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 113 h1 h3 (* h5 h5) 
(* h6 h6) j2) (* 16 h1 h3 (* h5 h5) (* h6 h6)) (* 16 h1 h3 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 86 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 193 h1 h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 231 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
155 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 55 h1 h3 h5 (* h6 h6 h6) j2) (* 8 h1 h3 
h5 (* h6 h6 h6)) (* 2 h1 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13 h1 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 34 h1 (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2)) (* 46 h1 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 34 h1 (* h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 13 h1 (* h4 h4 h4) (* h5 h5) j2) (* 2 h1 (* h4 h4 h4) 
(* h5 h5)) (* 2 h1 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13 h1 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 34 h1 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2)) (* 46 h1 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 34 h1 (* h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 13 h1 (* h4 h4) (* h5 h5 h5) j2) (* 2 h1 (* h4 h4) (* h5 h5 h5
)) (* 8 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 51 h1 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 132 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 178 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 132 h1 (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 51 h1 (* h4 h4) (* h5 h5) h6 j2) (* 8 h1 (* h4 h4) (* h5 h5) h6) 
(* 6 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 38 h1 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 98 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 132 h1 h4 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 98 h1 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 38 h1 h4
 (* h5 h5 h5) h6 j2) (* 6 h1 h4 (* h5 h5 h5) h6) (* 10 h1 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 63 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
162 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 218 h1 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 162 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 63 h1 h4 (* h5 h5) 
(* h6 h6) j2) (* 10 h1 h4 (* h5 h5) (* h6 h6)) (* 4 h1 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 25 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 64
 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 86 h1 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 64 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 25 h1 (* h5 h5 h5) (* 
h6 h6) j2) (* 4 h1 (* h5 h5 h5) (* h6 h6)) (* 4 h1 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 25 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 64 h1 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 86 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 64 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 25 h1 (* h5 h5) (* h6 h6 h6)
 j2) (* 4 h1 (* h5 h5) (* h6 h6 h6)) (* 8 (* h2 h2 h2) (* h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 36 (* h2 h2 h2) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 66 (* h2 h2 h2
) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 63 (* h2 h2 h2) (* h4 h4) h5 (* j2 j2 j2)) 
(* 33 (* h2 h2 h2) (* h4 h4) h5 (* j2 j2)) (* 9 (* h2 h2 h2) (* h4 h4) h5 j2) 
(* (* h2 h2 h2) (* h4 h4) h5) (* 8 (* h2 h2 h2) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 36 (* h2 h2 h2) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 66 (* h2 h2 h2) h4 
(* h5 h5) (* j2 j2 j2 j2)) (* 63 (* h2 h2 h2) h4 (* h5 h5) (* j2 j2 j2)) (* 33 
(* h2 h2 h2) h4 (* h5 h5) (* j2 j2)) (* 9 (* h2 h2 h2) h4 (* h5 h5) j2) (* (* h2
 h2 h2) h4 (* h5 h5)) (* 16 (* h2 h2 h2) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 72 
(* h2 h2 h2) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 132 (* h2 h2 h2) h4 h5 h6 (* j2 j2 
j2 j2)) (* 126 (* h2 h2 h2) h4 h5 h6 (* j2 j2 j2)) (* 66 (* h2 h2 h2) h4 h5 h6 
(* j2 j2)) (* 18 (* h2 h2 h2) h4 h5 h6 j2) (* 2 (* h2 h2 h2) h4 h5 h6) (* 8 (* 
h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 66 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 63 (* h2
 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 33 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) 
(* 9 (* h2 h2 h2) (* h5 h5) h6 j2) (* (* h2 h2 h2) (* h5 h5) h6) (* 8 (* h2 h2 
h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 66 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 63 (* h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2)) (* 33 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 9 (* h2
 h2 h2) h5 (* h6 h6) j2) (* (* h2 h2 h2) h5 (* h6 h6)) (* 24 (* h2 h2) h3 (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 108 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2 j2 j2 j2
)) (* 198 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 189 (* h2 h2) h3 (* h4 
h4) h5 (* j2 j2 j2)) (* 99 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2)) (* 27 (* h2 h2) 
h3 (* h4 h4) h5 j2) (* 3 (* h2 h2) h3 (* h4 h4) h5) (* 24 (* h2 h2) h3 h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 108 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 198 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 189 (* h2 h2) h3 h4 (* h5 
h5) (* j2 j2 j2)) (* 99 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 27 (* h2 h2) h3 
h4 (* h5 h5) j2) (* 3 (* h2 h2) h3 h4 (* h5 h5)) (* 48 (* h2 h2) h3 h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 216 (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 396 (* 
h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 378 (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) 
(* 198 (* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 54 (* h2 h2) h3 h4 h5 h6 j2) (* 6 (* 
h2 h2) h3 h4 h5 h6) (* 24 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
108 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 198 (* h2 h2) h3 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 189 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 99 (* h2 
h2) h3 (* h5 h5) h6 (* j2 j2)) (* 27 (* h2 h2) h3 (* h5 h5) h6 j2) (* 3 (* h2 h2
) h3 (* h5 h5) h6) (* 24 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 108
 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 198 (* h2 h2) h3 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 189 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 99 (* h2 h2) 
h3 h5 (* h6 h6) (* j2 j2)) (* 27 (* h2 h2) h3 h5 (* h6 h6) j2) (* 3 (* h2 h2) h3
 h5 (* h6 h6)) (* 4 (* h2 h2) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 20 (* h2
 h2) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 41 (* h2 h2) (* h4 h4 h4) h5 (* j2 
j2 j2 j2)) (* 44 (* h2 h2) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 26 (* h2 h2) (* h4 
h4 h4) h5 (* j2 j2)) (* 8 (* h2 h2) (* h4 h4 h4) h5 j2) (* (* h2 h2) (* h4 h4 h4
) h5) (* 8 (* h2 h2) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 82 (* h2 h2) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2)) (* 88 (* h2 h2) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 52 (* h2 h2) 
(* h4 h4) (* h5 h5) (* j2 j2)) (* 16 (* h2 h2) (* h4 h4) (* h5 h5) j2) (* 2 (* 
h2 h2) (* h4 h4) (* h5 h5)) (* 12 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2
)) (* 60 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 123 (* h2 h2) (* h4 h4
) h5 h6 (* j2 j2 j2 j2)) (* 132 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 78 
(* h2 h2) (* h4 h4) h5 h6 (* j2 j2)) (* 24 (* h2 h2) (* h4 h4) h5 h6 j2) (* 3 
(* h2 h2) (* h4 h4) h5 h6) (* 4 (* h2 h2) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 20 (* h2 h2) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 41 (* h2 h2) h4 (* h5 h5
 h5) (* j2 j2 j2 j2)) (* 44 (* h2 h2) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 26 (* h2 
h2) h4 (* h5 h5 h5) (* j2 j2)) (* 8 (* h2 h2) h4 (* h5 h5 h5) j2) (* (* h2 h2) 
h4 (* h5 h5 h5)) (* 16 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 
(* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 164 (* h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 176 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 104 (* h2 h2)
 h4 (* h5 h5) h6 (* j2 j2)) (* 32 (* h2 h2) h4 (* h5 h5) h6 j2) (* 4 (* h2 h2) 
h4 (* h5 h5) h6) (* 12 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60 
(* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 123 (* h2 h2) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 132 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 78 (* h2 h2) 
h4 h5 (* h6 h6) (* j2 j2)) (* 24 (* h2 h2) h4 h5 (* h6 h6) j2) (* 3 (* h2 h2) h4
 h5 (* h6 h6)) (* 4 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 20 (* h2
 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 41 (* h2 h2) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 44 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 26 (* h2 h2) (* h5 
h5 h5) h6 (* j2 j2)) (* 8 (* h2 h2) (* h5 h5 h5) h6 j2) (* (* h2 h2) (* h5 h5 h5
) h6) (* 8 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 82 (* h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 88 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 52 (* h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 16 (* h2 h2) (* h5 h5) (* h6 h6) j2) (* 2 (* 
h2 h2) (* h5 h5) (* h6 h6)) (* 4 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 20 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 41 (* h2 h2) h5 (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 44 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 26 (* 
h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 8 (* h2 h2) h5 (* h6 h6 h6) j2) (* (* h2 h2
) h5 (* h6 h6 h6)) (* 24 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 108
 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 198 h2 (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 189 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 99 h2 (* h3 
h3) (* h4 h4) h5 (* j2 j2)) (* 27 h2 (* h3 h3) (* h4 h4) h5 j2) (* 3 h2 (* h3 h3
) (* h4 h4) h5) (* 24 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 108 h2
 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 198 h2 (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2)) (* 189 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 99 h2 (* h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 27 h2 (* h3 h3) h4 (* h5 h5) j2) (* 3 h2 (* h3 h3) h4
 (* h5 h5)) (* 48 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 216 h2 (* h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 396 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 378 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 198 h2 (* h3 h3) h4 h5 h6 (* j2 j2
)) (* 54 h2 (* h3 h3) h4 h5 h6 j2) (* 6 h2 (* h3 h3) h4 h5 h6) (* 24 h2 (* h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 108 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 198 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 189 h2 (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2)) (* 99 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 27 h2 
(* h3 h3) (* h5 h5) h6 j2) (* 3 h2 (* h3 h3) (* h5 h5) h6) (* 24 h2 (* h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 108 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 198 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 189 h2 (* h3 h3) h5
 (* h6 h6) (* j2 j2 j2)) (* 99 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 27 h2 (* 
h3 h3) h5 (* h6 h6) j2) (* 3 h2 (* h3 h3) h5 (* h6 h6)) (* 8 h2 h3 (* h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 40 h2 h3 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 82 
h2 h3 (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 88 h2 h3 (* h4 h4 h4) h5 (* j2 j2 j2))
 (* 52 h2 h3 (* h4 h4 h4) h5 (* j2 j2)) (* 16 h2 h3 (* h4 h4 h4) h5 j2) (* 2 h2 
h3 (* h4 h4 h4) h5) (* 16 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 80
 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 164 h2 h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 176 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 104 h2 h3 (* 
h4 h4) (* h5 h5) (* j2 j2)) (* 32 h2 h3 (* h4 h4) (* h5 h5) j2) (* 4 h2 h3 (* h4
 h4) (* h5 h5)) (* 24 h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 120 h2 h3 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 246 h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 264 h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 156 h2 h3 (* h4 h4) h5 h6 (* j2 
j2)) (* 48 h2 h3 (* h4 h4) h5 h6 j2) (* 6 h2 h3 (* h4 h4) h5 h6) (* 8 h2 h3 h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 40 h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 82 h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 88 h2 h3 h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 52 h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 16 h2 h3 h4 (* h5 h5 h5)
 j2) (* 2 h2 h3 h4 (* h5 h5 h5)) (* 32 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 160 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 328 h2 h3 h4 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 352 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 208 h2 h3 h4 
(* h5 h5) h6 (* j2 j2)) (* 64 h2 h3 h4 (* h5 h5) h6 j2) (* 8 h2 h3 h4 (* h5 h5) 
h6) (* 24 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 h2 h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 246 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 264 h2 
h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 156 h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 48 
h2 h3 h4 h5 (* h6 h6) j2) (* 6 h2 h3 h4 h5 (* h6 h6)) (* 8 h2 h3 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 40 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 82 h2
 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 88 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 52 h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 16 h2 h3 (* h5 h5 h5) h6 j2) (* 2 h2 
h3 (* h5 h5 h5) h6) (* 16 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 80
 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 164 h2 h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 176 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 104 h2 h3 (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 32 h2 h3 (* h5 h5) (* h6 h6) j2) (* 4 h2 h3 (* h5
 h5) (* h6 h6)) (* 8 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 h2 h3 h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 82 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 88 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 52 h2 h3 h5 (* h6 h6 h6) (* j2 j2))
 (* 16 h2 h3 h5 (* h6 h6 h6) j2) (* 2 h2 h3 h5 (* h6 h6 h6)) (* 2 h2 (* h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 h2 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 25 h2 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 30 h2 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 20 h2 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 7 h2 (* h4
 h4 h4) (* h5 h5) j2) (* h2 (* h4 h4 h4) (* h5 h5)) (* 2 h2 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 11 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 25 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 30 h2 (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2)) (* 20 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 7 h2 (* h4 h4) (* 
h5 h5 h5) j2) (* h2 (* h4 h4) (* h5 h5 h5)) (* 6 h2 (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 33 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 75 h2 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 90 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 60 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 21 h2 (* h4 h4) (* h5 h5) h6
 j2) (* 3 h2 (* h4 h4) (* h5 h5) h6) (* 4 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 22 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h2 h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 60 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 40 h2 h4 (* h5
 h5 h5) h6 (* j2 j2)) (* 14 h2 h4 (* h5 h5 h5) h6 j2) (* 2 h2 h4 (* h5 h5 h5) h6
) (* 6 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 h2 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 75 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 90 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 60 h2 h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 21 h2 h4 (* h5 h5) (* h6 h6) j2) (* 3 h2 h4 (* h5 h5) (* h6 h6)) 
(* 2 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 h2 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 25 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
30 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20 h2 (* h5 h5 h5) (* h6 h6) (* j2
 j2)) (* 7 h2 (* h5 h5 h5) (* h6 h6) j2) (* h2 (* h5 h5 h5) (* h6 h6)) (* 2 h2 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 25 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 30 h2 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 20 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 7 h2 (* h5 h5) (* h6 h6 h6) j2) (* h2 (* h5 h5) (* h6 h6 h6)) (* 8 (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 36 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2 j2)) (* 66 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 63 (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2)) (* 33 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 9 (* h3
 h3 h3) (* h4 h4) h5 j2) (* (* h3 h3 h3) (* h4 h4) h5) (* 8 (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 36 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 66 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 63 (* h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2)) (* 33 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 9 (* h3 h3 h3) 
h4 (* h5 h5) j2) (* (* h3 h3 h3) h4 (* h5 h5)) (* 16 (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 72 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 132 (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 126 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 
66 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 18 (* h3 h3 h3) h4 h5 h6 j2) (* 2 (* h3 
h3 h3) h4 h5 h6) (* 8 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 36 (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 66 (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 63 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 33 (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2)) (* 9 (* h3 h3 h3) (* h5 h5) h6 j2) (* (* h3 h3 h3) (* h5 h5
) h6) (* 8 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 66 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 63 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 33 (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2)) (* 9 (* h3 h3 h3) h5 (* h6 h6) j2) (* (* h3 h3 h3) h5 (* h6 h6)) (* 4
 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 20 (* h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 41 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 44 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 26 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2
)) (* 8 (* h3 h3) (* h4 h4 h4) h5 j2) (* (* h3 h3) (* h4 h4 h4) h5) (* 8 (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 40 (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 82 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
88 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 52 (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2)) (* 16 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 2 (* h3 h3) (* h4 h4) 
(* h5 h5)) (* 12 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 60 (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 123 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 132 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 78 (* h3 h3) (* h4 h4)
 h5 h6 (* j2 j2)) (* 24 (* h3 h3) (* h4 h4) h5 h6 j2) (* 3 (* h3 h3) (* h4 h4) 
h5 h6) (* 4 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 41 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)
) (* 44 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 26 (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2)) (* 8 (* h3 h3) h4 (* h5 h5 h5) j2) (* (* h3 h3) h4 (* h5 h5 h5)) (* 
16 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 (* h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 164 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 176
 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 104 (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2)) (* 32 (* h3 h3) h4 (* h5 h5) h6 j2) (* 4 (* h3 h3) h4 (* h5 h5) h6) (* 12 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60 (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 123 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 132 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 78 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2
)) (* 24 (* h3 h3) h4 h5 (* h6 h6) j2) (* 3 (* h3 h3) h4 h5 (* h6 h6)) (* 4 (* 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 20 (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 41 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 44 (* h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 26 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) 
(* 8 (* h3 h3) (* h5 h5 h5) h6 j2) (* (* h3 h3) (* h5 h5 h5) h6) (* 8 (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 82 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 88 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 52 (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 16 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 2 (* h3 h3) (* h5 h5) (* 
h6 h6)) (* 4 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 41 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 44 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 26 (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2)) (* 8 (* h3 h3) h5 (* h6 h6 h6) j2) (* (* h3 h3) h5 (* h6 h6 h6)) (* 
2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 h3 (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 25 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 30 
h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 20 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2
)) (* 7 h3 (* h4 h4 h4) (* h5 h5) j2) (* h3 (* h4 h4 h4) (* h5 h5)) (* 2 h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 h3 (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 25 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 30 h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2)) (* 20 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 7 
h3 (* h4 h4) (* h5 h5 h5) j2) (* h3 (* h4 h4) (* h5 h5 h5)) (* 6 h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 33 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 75 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 90 h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 60 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 21 h3 (* 
h4 h4) (* h5 h5) h6 j2) (* 3 h3 (* h4 h4) (* h5 h5) h6) (* 4 h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 22 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 
h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 60 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 40 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 14 h3 h4 (* h5 h5 h5) h6 j2) (* 2 h3 
h4 (* h5 h5 h5) h6) (* 6 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 75 h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 90 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 60 h3 h4 (* h5
 h5) (* h6 h6) (* j2 j2)) (* 21 h3 h4 (* h5 h5) (* h6 h6) j2) (* 3 h3 h4 (* h5 
h5) (* h6 h6)) (* 2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 25 h3 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 30 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20 h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 7 h3 (* h5 h5 h5) (* h6 h6) j2) (* h3 (* h5 h5 h5) (* h6
 h6)) (* 2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 25 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 30 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 20 h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 7 h3 (* h5 h5) (* h6 h6 h6) j2) (* h3 (* h5 h5) (* h6 h6 h6))) 0))
)
(check-sat)
(exit)
