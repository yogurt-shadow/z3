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
(set-info :instance |E19E27|)
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
(+ (* 512 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 128 (* h1 h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) (* 512 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h6 (* j2 j2)) (* 128 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 j2) (* 128 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 256 (* h1 h1 h1 h1) (* h2 h2 h2
) h3 h5 h6 j2) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6) (* 128 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) 
h6) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6)) (* 4096 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 j2) (* 4096 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h6 j2) (* 1536 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 384 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 h6 (* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) 
(* 2048 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 512 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) j2) (* 4096 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h5 h6 (* j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 j2) 
(* 64 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 2048 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6) j2) (* 384 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) j2) (* 512 (* h1 
h1 h1 h1) (* h2 h2) h3 h4 h5 h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6)
 (* 128 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) j2) (* 256 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5) j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 j2)
 (* 128 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6) (* 1024 (* h1 h1 h1 h1) (* h2
 h2) h3 h5 (* h6 h6) j2) (* 192 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)) (* 
256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1 h1) (* h2 h2
) h4 (* h5 h5) h6) (* 32 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6)) (* 64 (* h1 
h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6) (* 128 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6)) (* 64 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6)) (* 8192 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h4 h5 (* j2 j2)) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 j2) (* 4096 (* h1 
h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) h4 h6 (* j2 j2)) (* 256 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 j2) (* 8192
 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 2048 (* h1 h1 h1 h1)
 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 16384 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h5 h6 (* j2 j2 j2)) (* 6144 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 
512 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6)
 (* j2 j2)) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 1536 (* h1 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 384 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h5 j2) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2))
 (* 128 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 4096 (* h1 h1 h1 h1) h2
 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 1024 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5) j2) (* 7168 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 2304 (* h1 
h1 h1 h1) h2 (* h3 h3) h4 h5 h6 j2) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6)
 (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1
 h1) h2 (* h3 h3) h4 (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5
 h5) (* j2 j2)) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 
1536 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 3072 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6) j2) (* 128 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6)) (* 2048 (* h1 h1 h1 h1
) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6
 h6 h6) j2) (* 384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) j2) (* 256 (* h1 h1
 h1 h1) h2 h3 (* h4 h4) h5 h6 j2) (* 32 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6) 
(* 512 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) j2) (* 1792 (* h1 h1 h1 h1) h2 h3 
h4 (* h5 h5) h6 j2) (* 128 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6) (* 1024 (* h1 
h1 h1 h1) h2 h3 h4 h5 (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)
) (* 1024 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 j2) (* 2048 (* h1 h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6)) (* 
1024 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 h3 h5 
(* h6 h6 h6)) (* 32 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6) (* 64 (* h1 h1 h1
 h1) h2 h4 (* h5 h5 h5) h6) (* 128 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6)) 
(* 128 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)) (* 128 (* h1 h1 h1 h1) h2 (* 
h5 h5) (* h6 h6 h6)) (* 4096 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2)) (* 2048 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 256 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2)) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 8192 (* h1 
h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 1024 (* h1 h1 h1 h1) (* h3 h3 h3) 
h4 h5 h6 j2) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) 
(* 4096 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 16384 (* h1 h1 
h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 8192 (* h1 h1 h1 h1) (* h3 h3 
h3) h5 (* h6 h6) (* j2 j2)) (* 1024 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) j2
) (* 512 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 128 (* h1 h1 h1
 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 2048 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 512 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 3072 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 768 (* h1 h1 h1 
h1) (* h3 h3) (* h4 h4) h5 h6 j2) (* 2048 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 8192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 
2048 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) (* 6144 (* h1 h1 h1 h1) (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6
) j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 8192 (* h1
 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2048 (* h1 h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6) j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2)) (* 1024 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* h1 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) j2) (* 256 (* h1 h1 h1 h1) h3 (* h4 h4) (* 
h5 h5 h5) j2) (* 768 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 j2) (* 1024 (* h1
 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 j2) (* 1536 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* 
h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 1024 (* h1 
h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h5 (* j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2) (* 128 
(* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2
 h2 h2) (* h3 h3) h6 j2) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) j2) (* 
64 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 j2) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) 
h3 h5 h6) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) j2) (* 8 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h5 h5) h6) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6)) 
(* 2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 1024 (* h1 h1
 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h5 j2) (* 2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 
j2)) (* 1024 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 128 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 j2) (* 1280 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2)) (* 320 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 j2) (* 896
 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 224 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h4 h6 j2) (* 1024 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)
 (* j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) j2) (* 2048 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 768 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h5 h6 j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6) (* 1024
 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* 
h5 h5) j2) (* 448 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 j2) (* 56 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 h5 h6) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) j2) 
(* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) (* 512 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) h6 j2) (* 64 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6) (* 
512 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) j2) (* 96 (* h1 h1 h1) (* h2 h2 h2
) h3 h5 (* h6 h6)) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) j2) (* 56 
(* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 32 (* h1 h1 h1) (* h2 h2 h2) h4 h5
 (* h6 h6)) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6) (* 64 (* h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6)) (* 32 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6
)) (* 4096 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 3072 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 768 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3
) h5 j2) (* 4096 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 
3072 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 768 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h6 j2) (* 10240 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) 
(* 5120 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 640 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h5 j2) (* 6144 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4
 h6 (* j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) 
(* 384 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 j2) (* 7168 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 2560 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) (* h5 h5) (* j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
j2) (* 14336 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 6912 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 896 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h5 h6 j2) (* 16 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6) (* 7168 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4096 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) (* h3
 h3 h3) (* h6 h6) j2) (* 2304 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* 
j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 896 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 224 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h6 j2) (* 5120 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5)
 (* j2 j2)) (* 1280 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 8576 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 2912 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h5 h6 j2) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 
2688 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 800 (* h1 h1 h1
) (* h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5) (* j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) j2)
 (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 1728 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) h6) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2
)) (* 2816 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 144 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) h5 (* h6 h6)) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6 h6) (* j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) j2) 
(* 576 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 448 (* h1 h1 h1) (* 
h2 h2) h3 (* h4 h4) h5 h6 j2) (* 56 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6) 
(* 32 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 640 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) j2) (* 2144 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 
j2) (* 192 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 1344 (* h1 h1 h1) (* h2
 h2) h3 h4 h5 (* h6 h6) j2) (* 200 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6)) 
(* 96 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2)
 h3 (* h5 h5 h5 h5) j2) (* 896 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 
48 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6) (* 1664 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6)) 
(* 896 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) j2) (* 144 (* h1 h1 h1) (* h2 
h2) h3 h5 (* h6 h6 h6)) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 
56 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6) (* 8 (* h1 h1 h1) (* h2 h2) 
(* h4 h4) h5 (* h6 h6)) (* 96 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6) (* 168 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6)) (* 24 (* h1 h1 h1) (* h2 h2) h4 
h5 (* h6 h6 h6)) (* 16 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6) (* 112 (* h1 
h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5)
 (* h6 h6 h6)) (* 16 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6)) (* 8192 (* h1 h1
 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 6144 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h4 h5 (* j2 j2 j2)) (* 1536 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 
j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 j2) (* 4096 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
h4 h6 (* j2 j2 j2)) (* 768 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 
64 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 j2) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3
 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5
) (* j2 j2 j2)) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 
16384 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 10240 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 2048 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h5 h6 (* j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) (* 8192 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 6144 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1536 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) (* h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) j2) 
(* 10240 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 5120 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 640 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h5 j2) (* 2048 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2)) (* 1024 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 128 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 j2) (* 18432 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2)) (* 6144 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2
 j2)) (* 384 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) j2) (* 32768 (* h1 h1 h1)
 h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 16128 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 h5 h6 (* j2 j2)) (* 2048 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 j2) (* 16 (* h1 
h1 h1) h2 (* h3 h3 h3) h4 h5 h6) (* 6144 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 
h6) (* j2 j2 j2)) (* 3072 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) 
(* 384 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) j2) (* 4096 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 1024 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5) (* j2 j2)) (* 24576 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2
)) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 512 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 24576 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 13312 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2
 j2)) (* 1920 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) (* 32 (* h1 h1 h1) 
h2 (* h3 h3 h3) h5 (* h6 h6)) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2)) (* 2048 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 
256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) j2) (* 1280 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2)) (* 320 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 
j2) (* 128 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 32 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 5120 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2)) (* 1280 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 6912 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1984 (* h1 h1 h1
) h2 (* h3 h3) (* h4 h4) h5 h6 j2) (* 32 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 
h6) (* 640 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 160 (* h1
 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 4608 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2)) (* 384 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) j2) 
(* 15872 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 4032 (* h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5) h6 j2) (* 48 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5
) h6) (* 11776 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 3712 (* 
h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 (* h3 h3) h4 h5
 (* h6 h6)) (* 1024 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 256 
(* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) j2) (* 512 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2)) (* 6144 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2)) (* 640 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 j2) (* 11264 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 3328 (* h1 h1 h1) h2 (* h3 h3
) (* h5 h5) (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6)) 
(* 6144 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2048 (* h1 h1 h1
) h2 (* h3 h3) h5 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 
h6)) (* 512 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1
 h1) h2 (* h3 h3) (* h6 h6 h6 h6) j2) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* 
h5 h5) j2) (* 64 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 j2) (* 8 (* h1 h1 h1) h2 
h3 (* h4 h4 h4) h5 h6) (* 640 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) j2) (* 
1728 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 j2) (* 64 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) h6) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) j2) (* 40 
(* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6)) (* 128 (* h1 h1 h1) h2 h3 h4 (* h5 h5
 h5 h5) j2) (* 2048 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 j2) (* 48 (* h1 h1 h1)
 h2 h3 h4 (* h5 h5 h5) h6) (* 2944 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) j2)
 (* 192 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 512 (* h1 h1 h1) h2 h3 h4 
h5 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)) (* 256 (* h1 h1
 h1) h2 h3 (* h5 h5 h5 h5) h6 j2) (* 1536 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6) j2) (* 96 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)) (* 1536 (* h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6))
 (* 256 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) (* 32 (* h1 h1 h1) h2 h3 h5 
(* h6 h6 h6 h6)) (* 8 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6) (* 32 (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5 h5) h6) (* 40 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* 
h6 h6)) (* 16 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6) (* 96 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* 32 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5) 
(* h6 h6 h6)) (* 32 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 4096 (* h1 h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 768 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 8192 (* h1 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 4096 (* h1 h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 512 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2)) (* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)
) (* 12288 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 3072 (* h1 h1 
h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 h3 h3) h4 
h5 h6 j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 8192 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 1024 (* h1 h1
 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 16384 (* h1 h1 h1) (* h3 h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12288 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) 
(* 256 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 2048 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2)) (* 128 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 7168 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2560 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 192 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) j2) (* 10240 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2)) (* 5120 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 640 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 4096 (* h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2)) (* 22528 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 8704
 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 768 (* h1 h1 h1) (* h3 
h3 h3) h4 (* h5 h5) h6 j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 8192 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
1024 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 8192 (* h1 h1 h1) (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2048 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2)) (* 16384 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 7168 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 768 (* 
h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 8192 (* h1 h1 h1) (* h3 h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4096 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2)) (* 512 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* h1 h1
 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 32 (* h1 h1 h1) (* h3 h3) (* h4 
h4 h4 h4) h5 j2) (* 1024 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)
) (* 256 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 896 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 224 (* h1 h1 h1) (* h3 h3) (* h4 h4 
h4) h5 h6 j2) (* 1792 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 192 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 5120 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1280 (* h1 h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5) h6 j2) (* 2304 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 576 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 512 (* h1 h1
 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 5632 (* h1 h1 h1) (* h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 768 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 j2) 
(* 8192 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2048 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 2560 (* h1 h1 h1) (* h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2)) (* 640 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) 
(* 1024 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 4096 (* h1 h1 h1
) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1) (* h3 h3) (* 
h5 h5 h5) (* h6 h6) j2) (* 4096 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 1024 (* 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3) 
h5 (* h6 h6 h6 h6) j2) (* 32 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 
128 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 224 (* h1 h1 h1) h3 (* h4 
h4 h4) (* h5 h5) h6 j2) (* 64 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 
640 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 576 (* h1 h1 h1) h3 (* h4 
h4) (* h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 
1024 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 640 (* h1 h1 h1) h3 h4 (* 
h5 h5) (* h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 
512 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6 h6) j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 
j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 16 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3 h3) h6 (* j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 j2) (* 192 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 32 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5) (* j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) 
j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 96 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5 h6 j2) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 
h6) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 48 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 48 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 (* h5 h5) j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 j2) (* 8 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 h5 h6) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) j2)
 (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) j2) (* 64 (* h1 h1) (* h2 h2 h2
 h2) h3 (* h5 h5) h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6) (* 64 
(* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) j2) (* 12 (* h1 h1) (* h2 h2 h2 h2) h3
 h5 (* h6 h6)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) j2) (* 8 (* h1 h1
) (* h2 h2 h2 h2) h4 (* h5 h5) h6) (* 4 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6
)) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6) (* 8 (* h1 h1) (* h2 h2 h2 h2
) (* h5 h5) (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6)) (* 1024 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 768 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h5 (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 j2) (* 
1024 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 768 (* h1 h1)
 (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3 h3) h6 (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 j2) 
(* 3072 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 1536 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* h3
 h3 h3) h4 h5 j2) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)
) (* 896 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 112 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 3584 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 1728 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h5 h6 (* j2 j2)) (* 224 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 
j2) (* 4 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) (* 1792 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1024 (* h1 h1) (* h2 h2 h2) (* h3 h3
 h3) (* h6 h6) (* j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) 
j2) (* 960 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 240 (* h1
 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 384 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h4 h4) h6 (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6
 j2) (* 1536 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 384 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 2624 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2)) (* 880 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 
j2) (* 28 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6) (* 832 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4
 (* h6 h6) j2) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 1664 (* h1 h1) (* h2 
h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5) h6 j2) (* 12 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 1664 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 704 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 36 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* 
h6 h6)) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 144 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 240 (* h1 h1) (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5) j2) (* 192 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 j2) 
(* 24 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6) (* 16 (* h1 h1) (* h2 h2 h2) h3
 (* h4 h4) (* h6 h6) j2) (* 192 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) j2) 
(* 656 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 56 (* h1 h1) (* h2 h2 h2
) h3 h4 (* h5 h5) h6) (* 416 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 60
 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) j2) (* 224 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 12 (* h1 h1) (* h2 h2 h2) h3 (* h5
 h5 h5) h6) (* 416 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 64 (* h1
 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 224 (* h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6 h6) j2) (* 36 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 16 (* h1 h1
) (* h2 h2 h2) h3 (* h6 h6 h6 h6) j2) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* 
h5 h5) h6) (* 4 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 28 (* h1 h1) 
(* h2 h2 h2) h4 (* h5 h5 h5) h6) (* 52 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6
 h6)) (* 8 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2
) (* h5 h5 h5 h5) h6) (* 28 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 28
 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6 h6)) (* 7168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 5376 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 1344 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 112 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h4 h5 j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 
j2 j2 j2)) (* 3072 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 
768 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 64 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h4 h6 j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2)) (* 2048 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2
 j2 j2)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 8192
 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 5376 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 1152 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h5 h6 (* j2 j2)) (* 80 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 j2) 
(* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 3328 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 896 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 80 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) (* h6 h6) j2) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2
 j2 j2)) (* 3328 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 416
 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 1792 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 896 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2)) (* 112 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2)
 (* 9472 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 3712 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 336 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) h4 (* h5 h5) j2) (* 16896 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2)) (* 8960 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) 
(* 1248 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 16 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5 h6) (* 3840 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2)) (* 2048 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
272 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 2048 (* h1 h1) (* h2 h2
) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3
) (* h5 h5 h5) (* j2 j2)) (* 10240 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2)) (* 3712 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 288 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 10240 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 5888 (* h1 h1) (* h2 h2) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 912 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6
 h6) j2) (* 20 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 2048 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 1152 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6 h6) j2) (* 960 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) 
(* 240 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 128 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 j2) (* 3328 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2)) (* 832 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 4352 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1312 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 j2) (* 28 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 
h6) (* 512 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 144 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 2368 (* h1 h1) (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 336 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) j2) (* 7936 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)
) (* 2240 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 48 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 5952 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 2032 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) 
(* 68 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 640 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* 
h6 h6 h6) j2) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) 
(* 2560 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 336 (* h1 h1
) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 4608 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 1472 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) j2) (* 56 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 2560 
(* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 960 (* h1 h1) (* h2 
h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 40 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 
h6 h6)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 80 
(* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 240 (* h1 h1) (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5) j2) (* 64 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 j2) 
(* 8 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6) (* 416 (* h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) j2) (* 1088 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6
 j2) (* 56 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 256 (* h1 h1) (* h2
 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 36 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* 
h6 h6)) (* 112 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 1056 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 48 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5)
 h6) (* 1488 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 128 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 320 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 
h6 h6) j2) (* 48 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 128 (* h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 640 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6) j2) (* 52 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 640 (* h1 h1)
 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 72 (* h1 h1) (* h2 h2) h3 (* h5 h5) 
(* h6 h6 h6)) (* 128 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 20 (* h1 
h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5
 h5) h6) (* 28 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 32 (* h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 16 (* h1 h1) (* h2 h2) h4 (* h5 h5 
h5 h5) h6) (* 60 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 40 (* h1 h1) 
(* h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6)) (* 32 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 7168 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2)) (* 5376 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 1344 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 112 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 1024 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 16 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 12288 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 6144 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) 
(* 21504 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 15360 (* h1 
h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 3648 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 h5 h6 (* j2 j2)) (* 288 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 3072
 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 2304 (* h1 h1) h2
 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 576 (* h1 h1) h2 (* h3 h3 h3 h3) 
h4 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 
2048 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 512 (* h1 h1)
 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 14336 (* h1 h1) h2 (* h3 h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6656 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5
) h6 (* j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 14336 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 10240 (* 
h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 2432 (* h1 h1) h2 (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 
h6) j2) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1536 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 384 (* h1 h1) h2
 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h6 h6 h6) j2) (* 3072 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) 
(* 1536 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 192 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 256 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2)) (* 128 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 
16 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 9472 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3712 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2)) (* 336 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 12800 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 6336 (* h1 
h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 800 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 h6 j2) (* 4 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 1024 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 64 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) (* h6 h6) j2) (* 6144 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 1536 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 22784 (* h1 h1
) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 9344 (* h1 h1) h2 (* h3 h3 h3
) h4 (* h5 h5) h6 (* j2 j2)) (* 912 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 j2
) (* 16896 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 8640 (* h1
 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 1152 (* h1 h1) h2 (* h3 h3 h3
) h4 h5 (* h6 h6) j2) (* 12 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)) (* 1280 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 640 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 80 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6
 h6) j2) (* 512 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 7168 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1664 (* h1 h1) h2 (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 13312 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 5760 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 608 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 7168 (* 
h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3840 (* h1 h1) h2 (* h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 544 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 
h6) j2) (* 8 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)) (* 512 (* h1 h1) h2 (* 
h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1) h2 (* h3 h3 h3) (* h6 
h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 192 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3
) (* h4 h4 h4 h4) h5 j2) (* 1536 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 1216 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 336 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5 h6 j2) (* 4 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 2368 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 336 (* h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 6272 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2)) (* 1584 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 
12 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 2752 (* h1 h1) h2 (* h3 h3)
 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 816 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 
(* h6 h6) j2) (* 16 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 768 (* h1 
h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 5696 (* h1 h1) h2 (* h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 j2)
 (* 8064 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2160 (* h1 
h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 36 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6)) (* 2624 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 816 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 20 (* h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6 h6)) (* 896 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)
) (* 3328 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 640 (* h1 
h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 3328 (* h1 h1) h2 (* h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6
) j2) (* 24 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 896 (* h1 h1) h2 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 288 (* h1 h1) h2 (* h3 h3) h5 (* h6 
h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 48 (* h1 h1) h2
 h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 192 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 
h5) j2) (* 304 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h5 h5) h6) (* 112 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) 
j2) (* 800 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 12 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) h6) (* 688 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) 
j2) (* 32 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 336 (* h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) h6 j2) (* 1056 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) j2) 
(* 36 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) (* 656 (* h1 h1) h2 h3 h4 (* h5
 h5) (* h6 h6 h6) j2) (* 40 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6)) (* 224 
(* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 448 (* h1 h1) h2 h3 (* h5 h5 h5
) (* h6 h6 h6) j2) (* 24 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* 224 (* h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) h2 h3 (* h5 h5) (* h6 
h6 h6 h6)) (* 4 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6) (* 4 (* h1 h1) h2 (* 
h4 h4) (* h5 h5 h5 h5) h6) (* 16 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6)) 
(* 12 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 20 (* h1 h1) h2 h4 (* h5 h5 
h5) (* h6 h6 h6)) (* 8 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1)
 h2 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 1024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4)
 h5 (* j2 j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2)) (* 192 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 16 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2)) (* 2048 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) 
(* 5120 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3840 (* h1
 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 960 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 
j2) (* 2048 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 512 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 12288 (* h1 h1) (* h3
 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6144 (* h1 h1) (* h3 h3 h3 h3) h4
 (* h5 h5) h6 (* j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2)) (* 8192 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
6144 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1536 (* h1 h1) 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 128 (* h1 h1) (* h3 h3 h3 h3) h4 
h5 (* h6 h6) j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 1024 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8192 (* 
h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4096 (* h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 4096 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 3072 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2
 j2)) (* 768 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2)) (* 128 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2))
 (* 16 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 1792 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 640 (* h1 h1) (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2)) (* 48 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2)
 (* 1536 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 768 (* h1 h1
) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 h6 j2) (* 2048 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 512 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 7424 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2816 (* h1 h1) (* h3
 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 240 (* h1 h1) (* h3 h3 h3) (* h4 h4
) (* h5 h5) h6 j2) (* 3328 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2)) (* 1664 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 208 
(* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 512 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 6144 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 1536 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 9728 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3968 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 384 (* h1 h1) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) j2) (* 3072 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)
 (* j2 j2 j2)) (* 1536 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 
192 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 1024 (* h1 h1) (* h3 h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 1024 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 1792 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1
) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 1024 (* h1 h1) (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 128 (* h1 h1) (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) j2) (* 448 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2)) (* 48 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 768 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 192 (* h1 h1) (* h3 h3) (* h4 
h4 h4) (* h5 h5) h6 j2) (* 256 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2)) (* 1856 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 240 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 1664 (* h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 416 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) j2) (* 768 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2)) (* 2432 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 384 (* 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 1536 (* h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 384 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
1024 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2)
 (* 16 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 16 (* h1 h1) h3 (* h4 h4
 h4) (* h5 h5 h5 h5) j2) (* 96 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 
80 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 208 (* h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) 
(* 192 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5
 h5 h5) (* h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 
256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 128 h1 (* h2 h2 h2 h2
) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) 
(* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 64 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 j2)
 (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 32 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h5 h6 (* j2 j2 j2)) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) 
(* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 96 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 24 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4) h5 j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 8 h1
 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 
224 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 72 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 h5 h6 j2) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) (* 64 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3
) h4 (* h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 128 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 24 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h5 h5) h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)
 (* j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 2 h1 (* h2 h2
 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) 
(* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 24 h1 (* h2 h2 
h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 16 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 j2
) (* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* 16 h1 (* h2 h2 h2 h2) h3 h4 (* 
h5 h5 h5) j2) (* 56 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 4 h1 (* h2 h2 
h2 h2) h3 h4 (* h5 h5) h6) (* 32 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 4 
h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
h6 j2) (* 32 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 2
 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 
h5) h6) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6) (* 4 h1 (* h2 h2 h2 h2) h4 
(* h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* 
h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h5 (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) 
(* 192 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 16 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 
j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 96 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 h6 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2)) (* 640 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)
) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h5 h6 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 96
 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3
 h3 h3 h3) (* h6 h6) j2) (* 1280 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2
 j2 j2)) (* 640 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 80 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* 
j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 1536 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 576 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 48 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 
2816 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 1472 h1 (* h2 h2 h2)
 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 200 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 
j2) (* 2 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 512 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 256 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3 h3
) (* h5 h5 h5) (* j2 j2)) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 32 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 832 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 120 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 2 h1 (* h2 h2 h2
) (* h3 h3 h3) h5 (* h6 h6)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 16 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 256 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) 
(* 32 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 j2) (* 640 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2)) (* 160 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 896 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 256 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 j2) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 96
 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) j2) (* 384 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 48 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 1344 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 368 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 j2) (* 6 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 1024 
h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 320 h1 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) j2) (* 8 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 96
 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2
 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 40 h1 (* h2
 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 704 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 208 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 6 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 384 h1 (* h2 h2 h2) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)
 j2) (* 4 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 32 h1 (* h2 h2 h2) (* h3
 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
j2) (* 64 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 16 h1 (* h2 h2 h2) h3
 (* h4 h4 h4) h5 h6 j2) (* 2 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6) (* 80 h1 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 224 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 j2) (* 8 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 48 h1 (* h2 h2 
h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 6 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)
) (* 16 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 176 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5) h6 j2) (* 6 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 256 h1 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 16 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6
 h6)) (* 48 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 6 h1 (* h2 h2 h2) h3 h4
 h5 (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 96 h1 (* h2
 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6
 h6)) (* 96 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 8 h1 (* h2 h2 h2) 
h3 (* h5 h5) (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 2 
h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 
h5) h6) (* 4 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 6 h1 (* h2 h2 h2) (* 
h4 h4) (* h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 8 h1 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 6 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 
h6 h6)) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 4 h1 (* h2 h2 h2) (* 
h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 3072 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 2304 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 576 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 
512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 384 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3 h3 h3
) (* h4 h4) h6 (* j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 
3584 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 1792 h1 (* h2
 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 224 h1 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h5 h5) (* j2 j2)) (* 6656 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2)) (* 4864 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 1184 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3 h3 
h3) h4 h5 h6 j2) (* 1024 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 192 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2) (* h3 h3 h3
 h3) h4 (* h6 h6) j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 128 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 3584 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1664 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 192 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2)) (* 3584 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 2560 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
608 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6) j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) 
(* 96 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h6 h6 h6) j2) (* 1280 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2)) (* 640 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 80 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2)) (* 64 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 3072 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1344 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) j2) (* 4352 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) 
(* 2240 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 296 h1 (* h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 2 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6
) (* 384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 192 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h6 h6) j2) (* 1792 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2)) (* 448 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
6400 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 2784 h1 (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 296 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 j2) (* 4864 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2))
 (* 2560 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 352 h1 (* h2 h2
) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 4 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6
)) (* 384 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 192 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3) 
h4 (* h6 h6 h6) j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2
)) (* 1792 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 416 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 3328 h1 (* h2 h2) (* h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 152 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 1792 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 960 h1 (* h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 136 h1 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 128 h1 (* h2
 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) j2) 
(* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 24 h1 (* h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 640 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2)) (* 160 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 
512 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 144 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) h5 h6 j2) (* 2 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) 
(* 768 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 144 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2112 h1 (* h2 h2) (* h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2)) (* 560 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 
j2) (* 6 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 960 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3) (* h4 h4)
 h5 (* h6 h6) j2) (* 6 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 224 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1600 h1 (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 304 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 
j2) (* 2304 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 640 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 12 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6)) (* 768 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2))
 (* 240 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 6 h1 (* h2 h2) (* h3 h3
) h4 h5 (* h6 h6 h6)) (* 224 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)
) (* 832 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 160 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 832 h1 (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 240 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)
 j2) (* 6 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 224 h1 (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 72 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6
 h6) j2) (* 2 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 24 h1 (* h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5) j2) (* 80 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2
) (* 128 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 4 h1 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) h6) (* 48 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 
272 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 6 h1 (* h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) h6) (* 240 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 12
 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 104 h1 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) h6 j2) (* 304 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 12 h1 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 192 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) j2) (* 12 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 56 h1 (* h2 h2
) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 112 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) j2) (* 6 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 56 h1 (* h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) j2) (* 4 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) 
(* 2 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* 2 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) h6) (* 6 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 4 h1 (* 
h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 
h6)) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2) (* h5 h5 
h5) (* h6 h6 h6 h6)) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2)) (* 768 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 192 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4)
 h5 j2) (* 3584 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
1792 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 224 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 4096 h1 h2 (* h3 h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2)) (* 2944 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2)) (* 704 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 56 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) h5 h6 j2) (* 2048 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 7680
 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3712 h1 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 448 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 5120 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
3584 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 832 h1 h2 (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 64 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2
) (* 2048 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 512 h1 h2 
(* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4096 h1 h2 (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1920 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 224 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 2048 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1408 h1 h2 (* 
h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 320 h1 h2 (* h3 h3 h3 h3) h5 (* h6
 h6 h6) (* j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 h1 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4
 h4 h4) h5 (* j2 j2)) (* 16 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 1536 h1
 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 576 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 48 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5
) j2) (* 1280 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 608 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 72 h1 h2 (* h3 h3 h3) (* h4 h4 h4)
 h5 h6 j2) (* 1792 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 
448 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 5120 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1984 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 176 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 
2304 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1056 h1 h2 (* h3
 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 120 h1 h2 (* h3 h3 h3) (* h4 h4) h5
 (* h6 h6) j2) (* 512 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
3840 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 928 h1 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 5632 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 2240 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 208 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1792 h1 h2 (* h3 h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 800 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 88 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2048 h1 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 480 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 2048 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 832 h1 
h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 80 h1 h2 (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 224 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 h1 h2 (* h3 h3 h3
) h5 (* h6 h6 h6 h6) j2) (* 128 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2)) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 384 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 48 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5) j2) (* 640 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 152 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 224 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2)) (* 1280 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 184 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 1152 h1 h2 (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 264 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) j2) (* 480 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
1408 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 224 h1 h2 (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) j2) (* 896 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 200 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 256 h1 h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 512 h1 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 88 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 
256 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 56 h1 h2 (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) j2) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) 
(* 16 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 80 h1 h2 h3 (* h4 h4 h4) (* 
h5 h5 h5) h6 j2) (* 64 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 144 h1 h2 h3
 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 80 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6
) j2) (* 112 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 h1 h2 h3 (* h5 h5 
h5 h5) (* h6 h6 h6) j2) (* 32 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 512 
h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 256 h1 (* h3 h3 h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 32 h1 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 128 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2048 
h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1024 h1 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 128 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 1536 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 384 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2560 h1 
(* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1280 h1 (* h3 h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 160 h1 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 1024 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 256 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1024 
h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 512 h1 (* h3 h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 h1 (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 32 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 256 h1 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 64 h1 (* h3 h3 h3) (* h4 h4 h4
) (* h5 h5 h5) (* j2 j2)) (* 640 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2)) (* 160 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 128 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1024 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 256 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2)) (* 1152 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 288 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 384 h1 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1280 h1 (* h3 h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 320 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 896 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 224 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 256 h1 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 512 h1 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 128 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 256 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h1 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4
 h4) (* h5 h5 h5) (* j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2)) (* 160 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 128 h1 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 288 h1 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 160 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 224 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64
 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 h1 (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 4
 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3
) h4 (* h5 h5) (* j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2)) (* 128 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 64 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
h5 h6 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 16 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 16 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) 
(* 8 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 48 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 12 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 
h6 j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 64 (* h2 h2
 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h5 h5) h6 j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
12 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) h6 (* j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 16 (* h2 h2
 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 4 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 12 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5
 h5) h6 j2) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 12 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5) (* h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2
) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 256 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2
)) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 256 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2
)) (* 512 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 384 (* h2 h2
 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 256 (* h2 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5
) h6 (* j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 192 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 48 (* h2 h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h5
 (* h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) 
(* 64 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 8 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 j2) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)
) (* 12 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 384 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 h6 (* j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 
128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 32 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2)) (* 224 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2)) (* 24 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 384 (* h2 h2 h2) (* 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 128 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 32 (* h2 h2 h2) (* h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 12 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 128 (* h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) 
(* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 4 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) h5 j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5
) (* j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 64 (* h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 12 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 192 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) h6 j2) (* 96 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 16 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 192 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 48 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 16 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16 (* h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) (* h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 4 
(* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5) j2) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 4 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5
 h5) h6 j2) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 8 (* h2 
h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 24 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 
h6) j2) (* 16 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3
 (* h5 h5 h5 h5) (* h6 h6) j2) (* 8 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2
) (* 4 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2
)) (* 4 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 512 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 576 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 144 (* h2 h2)
 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 h6 j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2
)) (* 64 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 1024 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 512 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 576 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 144 (* h2 h2
) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3 h3) h4 
h5 (* h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 64 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 512 (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 48 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2
 j2)) (* 32 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 4 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 112 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 256 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 128 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) 
(* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 64 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 336 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 36 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) 
(* 384 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 192 (* h2 
h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2
 j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 128 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 768 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 336 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2)) (* 36 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2)
 (* 256 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 128 (* h2 h2)
 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 256 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 64 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 112 (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) 
(* 64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) h5 (* h6 
h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
8 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 64 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 12 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) j2) (* 128 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 32 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2)) (* 36 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) 
(* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 48 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 64 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 192 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 36 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 128 (* h2 
h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 32 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 64 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 12 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6
 h6) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 4 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6
 j2) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 24 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 12 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6
) j2) (* 16 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2)
 (* 256 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 128 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 16 h2 (* h3 h3 h3 h3) (* h4
 h4 h4) (* h5 h5) (* j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 64 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) 
(* 768 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 384 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 48 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2)) (* 512 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 128 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 768 h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3 h3
) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 48 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 64 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 256 h2 (* 
h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 128 h2 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 16 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 16 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 128 h2 (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 32 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 256 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 64 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 96 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 96 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 128 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 384 h2 (* h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 96 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 256 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 h2 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 h2 (* h3 h3 h3) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 32 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 
h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
 h5) (* j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 64
 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 48 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 96 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 48 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
64 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16 h2 (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2))) 0)))
(check-sat)
(exit)
