(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x6 () Real)
(declare-fun x23 () Real)
(declare-fun x40 () Real)
(declare-fun x57 () Real)
(declare-fun x13 () Real)
(declare-fun x30 () Real)
(declare-fun x47 () Real)
(declare-fun x64 () Real)
(declare-fun x3 () Real)
(declare-fun x20 () Real)
(declare-fun x37 () Real)
(declare-fun x54 () Real)
(declare-fun x10 () Real)
(declare-fun x27 () Real)
(declare-fun x44 () Real)
(declare-fun x61 () Real)
(declare-fun x0 () Real)
(declare-fun x17 () Real)
(declare-fun x34 () Real)
(declare-fun x51 () Real)
(declare-fun x7 () Real)
(declare-fun x24 () Real)
(declare-fun x41 () Real)
(declare-fun x58 () Real)
(declare-fun x14 () Real)
(declare-fun x31 () Real)
(declare-fun x48 () Real)
(declare-fun x65 () Real)
(declare-fun x4 () Real)
(declare-fun x21 () Real)
(declare-fun x38 () Real)
(declare-fun x55 () Real)
(declare-fun x11 () Real)
(declare-fun x28 () Real)
(declare-fun x45 () Real)
(declare-fun x62 () Real)
(declare-fun x1 () Real)
(declare-fun x18 () Real)
(declare-fun x35 () Real)
(declare-fun x52 () Real)
(declare-fun x8 () Real)
(declare-fun x25 () Real)
(declare-fun x42 () Real)
(declare-fun x59 () Real)
(declare-fun x15 () Real)
(declare-fun x32 () Real)
(declare-fun x49 () Real)
(declare-fun x5 () Real)
(declare-fun x22 () Real)
(declare-fun x39 () Real)
(declare-fun x56 () Real)
(declare-fun x12 () Real)
(declare-fun x29 () Real)
(declare-fun x46 () Real)
(declare-fun x63 () Real)
(declare-fun x2 () Real)
(declare-fun x19 () Real)
(declare-fun x36 () Real)
(declare-fun x53 () Real)
(declare-fun x9 () Real)
(declare-fun x26 () Real)
(declare-fun x43 () Real)
(declare-fun x60 () Real)
(declare-fun x16 () Real)
(declare-fun x33 () Real)
(declare-fun x50 () Real)
(assert (>= x6 0))
(assert (>= x23 0))
(assert (>= x40 0))
(assert (>= x57 0))
(assert (>= x13 0))
(assert (>= x30 0))
(assert (>= x47 0))
(assert (>= x64 0))
(assert (>= x3 0))
(assert (>= x20 0))
(assert (>= x37 0))
(assert (>= x54 0))
(assert (>= x10 0))
(assert (>= x27 0))
(assert (>= x44 0))
(assert (>= x61 0))
(assert (>= x0 0))
(assert (>= x17 0))
(assert (>= x34 0))
(assert (>= x51 0))
(assert (>= x7 0))
(assert (>= x24 0))
(assert (>= x41 0))
(assert (>= x58 0))
(assert (>= x14 0))
(assert (>= x31 0))
(assert (>= x48 0))
(assert (>= x65 0))
(assert (>= x4 0))
(assert (>= x21 0))
(assert (>= x38 0))
(assert (>= x55 0))
(assert (>= x11 0))
(assert (>= x28 0))
(assert (>= x45 0))
(assert (>= x62 0))
(assert (>= x1 0))
(assert (>= x18 0))
(assert (>= x35 0))
(assert (>= x52 0))
(assert (>= x8 0))
(assert (>= x25 0))
(assert (>= x42 0))
(assert (>= x59 0))
(assert (>= x15 0))
(assert (>= x32 0))
(assert (>= x49 0))
(assert (>= x5 0))
(assert (>= x22 0))
(assert (>= x39 0))
(assert (>= x56 0))
(assert (>= x12 0))
(assert (>= x29 0))
(assert (>= x46 0))
(assert (>= x63 0))
(assert (>= x2 0))
(assert (>= x19 0))
(assert (>= x36 0))
(assert (>= x53 0))
(assert (>= x9 0))
(assert (>= x26 0))
(assert (>= x43 0))
(assert (>= x60 0))
(assert (>= x16 0))
(assert (>= x33 0))
(assert (>= x50 0))
(assert (let ((?v_0 (+ x36 (+ (+ (+ (+ (* x41 x36) (* x42 x37)) (* x43 x38)) (* x44 x39)) (* x45 x40)))) (?v_1 (+ x37 (+ (+ (+ (+ (* x46 x36) (* x47 x37)) (* x48 x38)) (* x49 x39)) (* x50 x40)))) (?v_2 (+ x38 (+ (+ (+ (+ (* x51 x36) (* x52 x37)) (* x53 x38)) (* x54 x39)) (* x55 x40)))) (?v_3 (+ x39 (+ (+ (+ (+ (* x56 x36) (* x57 x37)) (* x58 x38)) (* x59 x39)) (* x60 x40)))) (?v_4 (+ x40 (+ (+ (+ (+ (* x61 x36) (* x62 x37)) (* x63 x38)) (* x64 x39)) (* x65 x40))))) (let ((?v_38 (+ x6 (+ (+ (+ (+ (* x11 ?v_0) (* x12 ?v_1)) (* x13 ?v_2)) (* x14 ?v_3)) (* x15 ?v_4)))) (?v_39 (+ x7 (+ (+ (+ (+ (* x16 ?v_0) (* x17 ?v_1)) (* x18 ?v_2)) (* x19 ?v_3)) (* x20 ?v_4)))) (?v_40 (+ x8 (+ (+ (+ (+ (* x21 ?v_0) (* x22 ?v_1)) (* x23 ?v_2)) (* x24 ?v_3)) (* x25 ?v_4)))) (?v_41 (+ x9 (+ (+ (+ (+ (* x26 ?v_0) (* x27 ?v_1)) (* x28 ?v_2)) (* x29 ?v_3)) (* x30 ?v_4)))) (?v_42 (+ x10 (+ (+ (+ (+ (* x31 ?v_0) (* x32 ?v_1)) (* x33 ?v_2)) (* x34 ?v_3)) (* x35 ?v_4))))) (let ((?v_5 (+ x0 (+ (+ (+ (+ (* x1 ?v_38) (* x2 ?v_39)) (* x3 ?v_40)) (* x4 ?v_41)) (* x5 ?v_42)))) (?v_6 (+ (+ (+ (+ (* x41 x41) (* x42 x46)) (* x43 x51)) (* x44 x56)) (* x45 x61))) (?v_7 (+ (+ (+ (+ (* x46 x41) (* x47 x46)) (* x48 x51)) (* x49 x56)) (* x50 x61))) (?v_8 (+ (+ (+ (+ (* x51 x41) (* x52 x46)) (* x53 x51)) (* x54 x56)) (* x55 x61))) (?v_9 (+ (+ (+ (+ (* x56 x41) (* x57 x46)) (* x58 x51)) (* x59 x56)) (* x60 x61))) (?v_10 (+ (+ (+ (+ (* x61 x41) (* x62 x46)) (* x63 x51)) (* x64 x56)) (* x65 x61)))) (let ((?v_65 (+ (+ (+ (+ (* x11 ?v_6) (* x12 ?v_7)) (* x13 ?v_8)) (* x14 ?v_9)) (* x15 ?v_10))) (?v_66 (+ (+ (+ (+ (* x16 ?v_6) (* x17 ?v_7)) (* x18 ?v_8)) (* x19 ?v_9)) (* x20 ?v_10))) (?v_67 (+ (+ (+ (+ (* x21 ?v_6) (* x22 ?v_7)) (* x23 ?v_8)) (* x24 ?v_9)) (* x25 ?v_10))) (?v_68 (+ (+ (+ (+ (* x26 ?v_6) (* x27 ?v_7)) (* x28 ?v_8)) (* x29 ?v_9)) (* x30 ?v_10))) (?v_69 (+ (+ (+ (+ (* x31 ?v_6) (* x32 ?v_7)) (* x33 ?v_8)) (* x34 ?v_9)) (* x35 ?v_10)))) (let ((?v_32 (+ (+ (+ (+ (* x1 ?v_65) (* x2 ?v_66)) (* x3 ?v_67)) (* x4 ?v_68)) (* x5 ?v_69))) (?v_11 (+ (+ (+ (+ (* x41 x42) (* x42 x47)) (* x43 x52)) (* x44 x57)) (* x45 x62))) (?v_12 (+ (+ (+ (+ (* x46 x42) (* x47 x47)) (* x48 x52)) (* x49 x57)) (* x50 x62))) (?v_13 (+ (+ (+ (+ (* x51 x42) (* x52 x47)) (* x53 x52)) (* x54 x57)) (* x55 x62))) (?v_14 (+ (+ (+ (+ (* x56 x42) (* x57 x47)) (* x58 x52)) (* x59 x57)) (* x60 x62))) (?v_15 (+ (+ (+ (+ (* x61 x42) (* x62 x47)) (* x63 x52)) (* x64 x57)) (* x65 x62)))) (let ((?v_85 (+ (+ (+ (+ (* x11 ?v_11) (* x12 ?v_12)) (* x13 ?v_13)) (* x14 ?v_14)) (* x15 ?v_15))) (?v_86 (+ (+ (+ (+ (* x16 ?v_11) (* x17 ?v_12)) (* x18 ?v_13)) (* x19 ?v_14)) (* x20 ?v_15))) (?v_87 (+ (+ (+ (+ (* x21 ?v_11) (* x22 ?v_12)) (* x23 ?v_13)) (* x24 ?v_14)) (* x25 ?v_15))) (?v_88 (+ (+ (+ (+ (* x26 ?v_11) (* x27 ?v_12)) (* x28 ?v_13)) (* x29 ?v_14)) (* x30 ?v_15))) (?v_89 (+ (+ (+ (+ (* x31 ?v_11) (* x32 ?v_12)) (* x33 ?v_13)) (* x34 ?v_14)) (* x35 ?v_15)))) (let ((?v_33 (+ (+ (+ (+ (* x1 ?v_85) (* x2 ?v_86)) (* x3 ?v_87)) (* x4 ?v_88)) (* x5 ?v_89))) (?v_16 (+ (+ (+ (+ (* x41 x43) (* x42 x48)) (* x43 x53)) (* x44 x58)) (* x45 x63))) (?v_17 (+ (+ (+ (+ (* x46 x43) (* x47 x48)) (* x48 x53)) (* x49 x58)) (* x50 x63))) (?v_18 (+ (+ (+ (+ (* x51 x43) (* x52 x48)) (* x53 x53)) (* x54 x58)) (* x55 x63))) (?v_19 (+ (+ (+ (+ (* x56 x43) (* x57 x48)) (* x58 x53)) (* x59 x58)) (* x60 x63))) (?v_20 (+ (+ (+ (+ (* x61 x43) (* x62 x48)) (* x63 x53)) (* x64 x58)) (* x65 x63)))) (let ((?v_105 (+ (+ (+ (+ (* x11 ?v_16) (* x12 ?v_17)) (* x13 ?v_18)) (* x14 ?v_19)) (* x15 ?v_20))) (?v_106 (+ (+ (+ (+ (* x16 ?v_16) (* x17 ?v_17)) (* x18 ?v_18)) (* x19 ?v_19)) (* x20 ?v_20))) (?v_107 (+ (+ (+ (+ (* x21 ?v_16) (* x22 ?v_17)) (* x23 ?v_18)) (* x24 ?v_19)) (* x25 ?v_20))) (?v_108 (+ (+ (+ (+ (* x26 ?v_16) (* x27 ?v_17)) (* x28 ?v_18)) (* x29 ?v_19)) (* x30 ?v_20))) (?v_109 (+ (+ (+ (+ (* x31 ?v_16) (* x32 ?v_17)) (* x33 ?v_18)) (* x34 ?v_19)) (* x35 ?v_20)))) (let ((?v_34 (+ (+ (+ (+ (* x1 ?v_105) (* x2 ?v_106)) (* x3 ?v_107)) (* x4 ?v_108)) (* x5 ?v_109))) (?v_21 (+ (+ (+ (+ (* x41 x44) (* x42 x49)) (* x43 x54)) (* x44 x59)) (* x45 x64))) (?v_22 (+ (+ (+ (+ (* x46 x44) (* x47 x49)) (* x48 x54)) (* x49 x59)) (* x50 x64))) (?v_23 (+ (+ (+ (+ (* x51 x44) (* x52 x49)) (* x53 x54)) (* x54 x59)) (* x55 x64))) (?v_24 (+ (+ (+ (+ (* x56 x44) (* x57 x49)) (* x58 x54)) (* x59 x59)) (* x60 x64))) (?v_25 (+ (+ (+ (+ (* x61 x44) (* x62 x49)) (* x63 x54)) (* x64 x59)) (* x65 x64)))) (let ((?v_125 (+ (+ (+ (+ (* x11 ?v_21) (* x12 ?v_22)) (* x13 ?v_23)) (* x14 ?v_24)) (* x15 ?v_25))) (?v_126 (+ (+ (+ (+ (* x16 ?v_21) (* x17 ?v_22)) (* x18 ?v_23)) (* x19 ?v_24)) (* x20 ?v_25))) (?v_127 (+ (+ (+ (+ (* x21 ?v_21) (* x22 ?v_22)) (* x23 ?v_23)) (* x24 ?v_24)) (* x25 ?v_25))) (?v_128 (+ (+ (+ (+ (* x26 ?v_21) (* x27 ?v_22)) (* x28 ?v_23)) (* x29 ?v_24)) (* x30 ?v_25))) (?v_129 (+ (+ (+ (+ (* x31 ?v_21) (* x32 ?v_22)) (* x33 ?v_23)) (* x34 ?v_24)) (* x35 ?v_25)))) (let ((?v_35 (+ (+ (+ (+ (* x1 ?v_125) (* x2 ?v_126)) (* x3 ?v_127)) (* x4 ?v_128)) (* x5 ?v_129))) (?v_26 (+ (+ (+ (+ (* x41 x45) (* x42 x50)) (* x43 x55)) (* x44 x60)) (* x45 x65))) (?v_27 (+ (+ (+ (+ (* x46 x45) (* x47 x50)) (* x48 x55)) (* x49 x60)) (* x50 x65))) (?v_28 (+ (+ (+ (+ (* x51 x45) (* x52 x50)) (* x53 x55)) (* x54 x60)) (* x55 x65))) (?v_29 (+ (+ (+ (+ (* x56 x45) (* x57 x50)) (* x58 x55)) (* x59 x60)) (* x60 x65))) (?v_30 (+ (+ (+ (+ (* x61 x45) (* x62 x50)) (* x63 x55)) (* x64 x60)) (* x65 x65)))) (let ((?v_145 (+ (+ (+ (+ (* x11 ?v_26) (* x12 ?v_27)) (* x13 ?v_28)) (* x14 ?v_29)) (* x15 ?v_30))) (?v_146 (+ (+ (+ (+ (* x16 ?v_26) (* x17 ?v_27)) (* x18 ?v_28)) (* x19 ?v_29)) (* x20 ?v_30))) (?v_147 (+ (+ (+ (+ (* x21 ?v_26) (* x22 ?v_27)) (* x23 ?v_28)) (* x24 ?v_29)) (* x25 ?v_30))) (?v_148 (+ (+ (+ (+ (* x26 ?v_26) (* x27 ?v_27)) (* x28 ?v_28)) (* x29 ?v_29)) (* x30 ?v_30))) (?v_149 (+ (+ (+ (+ (* x31 ?v_26) (* x32 ?v_27)) (* x33 ?v_28)) (* x34 ?v_29)) (* x35 ?v_30)))) (let ((?v_36 (+ (+ (+ (+ (* x1 ?v_145) (* x2 ?v_146)) (* x3 ?v_147)) (* x4 ?v_148)) (* x5 ?v_149))) (?v_31 (+ x0 (+ (+ (+ (+ (* x1 x6) (* x2 x7)) (* x3 x8)) (* x4 x9)) (* x5 x10)))) (?v_43 (+ x6 (+ (+ (+ (+ (* x11 x6) (* x12 x7)) (* x13 x8)) (* x14 x9)) (* x15 x10)))) (?v_44 (+ x7 (+ (+ (+ (+ (* x16 x6) (* x17 x7)) (* x18 x8)) (* x19 x9)) (* x20 x10)))) (?v_45 (+ x8 (+ (+ (+ (+ (* x21 x6) (* x22 x7)) (* x23 x8)) (* x24 x9)) (* x25 x10)))) (?v_46 (+ x9 (+ (+ (+ (+ (* x26 x6) (* x27 x7)) (* x28 x8)) (* x29 x9)) (* x30 x10)))) (?v_47 (+ x10 (+ (+ (+ (+ (* x31 x6) (* x32 x7)) (* x33 x8)) (* x34 x9)) (* x35 x10))))) (let ((?v_37 (+ x0 (+ (+ (+ (+ (* x1 ?v_43) (* x2 ?v_44)) (* x3 ?v_45)) (* x4 ?v_46)) (* x5 ?v_47)))) (?v_70 (+ (+ (+ (+ (* x11 x11) (* x12 x16)) (* x13 x21)) (* x14 x26)) (* x15 x31))) (?v_71 (+ (+ (+ (+ (* x16 x11) (* x17 x16)) (* x18 x21)) (* x19 x26)) (* x20 x31))) (?v_72 (+ (+ (+ (+ (* x21 x11) (* x22 x16)) (* x23 x21)) (* x24 x26)) (* x25 x31))) (?v_73 (+ (+ (+ (+ (* x26 x11) (* x27 x16)) (* x28 x21)) (* x29 x26)) (* x30 x31))) (?v_74 (+ (+ (+ (+ (* x31 x11) (* x32 x16)) (* x33 x21)) (* x34 x26)) (* x35 x31))) (?v_90 (+ (+ (+ (+ (* x11 x12) (* x12 x17)) (* x13 x22)) (* x14 x27)) (* x15 x32))) (?v_91 (+ (+ (+ (+ (* x16 x12) (* x17 x17)) (* x18 x22)) (* x19 x27)) (* x20 x32))) (?v_92 (+ (+ (+ (+ (* x21 x12) (* x22 x17)) (* x23 x22)) (* x24 x27)) (* x25 x32))) (?v_93 (+ (+ (+ (+ (* x26 x12) (* x27 x17)) (* x28 x22)) (* x29 x27)) (* x30 x32))) (?v_94 (+ (+ (+ (+ (* x31 x12) (* x32 x17)) (* x33 x22)) (* x34 x27)) (* x35 x32))) (?v_110 (+ (+ (+ (+ (* x11 x13) (* x12 x18)) (* x13 x23)) (* x14 x28)) (* x15 x33))) (?v_111 (+ (+ (+ (+ (* x16 x13) (* x17 x18)) (* x18 x23)) (* x19 x28)) (* x20 x33))) (?v_112 (+ (+ (+ (+ (* x21 x13) (* x22 x18)) (* x23 x23)) (* x24 x28)) (* x25 x33))) (?v_113 (+ (+ (+ (+ (* x26 x13) (* x27 x18)) (* x28 x23)) (* x29 x28)) (* x30 x33))) (?v_114 (+ (+ (+ (+ (* x31 x13) (* x32 x18)) (* x33 x23)) (* x34 x28)) (* x35 x33))) (?v_130 (+ (+ (+ (+ (* x11 x14) (* x12 x19)) (* x13 x24)) (* x14 x29)) (* x15 x34))) (?v_131 (+ (+ (+ (+ (* x16 x14) (* x17 x19)) (* x18 x24)) (* x19 x29)) (* x20 x34))) (?v_132 (+ (+ (+ (+ (* x21 x14) (* x22 x19)) (* x23 x24)) (* x24 x29)) (* x25 x34))) (?v_133 (+ (+ (+ (+ (* x26 x14) (* x27 x19)) (* x28 x24)) (* x29 x29)) (* x30 x34))) (?v_134 (+ (+ (+ (+ (* x31 x14) (* x32 x19)) (* x33 x24)) (* x34 x29)) (* x35 x34))) (?v_150 (+ (+ (+ (+ (* x11 x15) (* x12 x20)) (* x13 x25)) (* x14 x30)) (* x15 x35))) (?v_151 (+ (+ (+ (+ (* x16 x15) (* x17 x20)) (* x18 x25)) (* x19 x30)) (* x20 x35))) (?v_152 (+ (+ (+ (+ (* x21 x15) (* x22 x20)) (* x23 x25)) (* x24 x30)) (* x25 x35))) (?v_153 (+ (+ (+ (+ (* x26 x15) (* x27 x20)) (* x28 x25)) (* x29 x30)) (* x30 x35))) (?v_154 (+ (+ (+ (+ (* x31 x15) (* x32 x20)) (* x33 x25)) (* x34 x30)) (* x35 x35)))) (let ((?v_190 (and (and (and (and (> ?v_5 x0) (>= ?v_5 x0)) (and (and (and (and (>= ?v_32 x1) (>= ?v_33 x2)) (>= ?v_34 x3)) (>= ?v_35 x4)) (>= ?v_36 x5))) (and (and (> ?v_5 ?v_31) (>= ?v_5 ?v_31)) (and (and (and (and (>= ?v_32 (+ (+ (+ (+ (* x1 x11) (* x2 x16)) (* x3 x21)) (* x4 x26)) (* x5 x31))) (>= ?v_33 (+ (+ (+ (+ (* x1 x12) (* x2 x17)) (* x3 x22)) (* x4 x27)) (* x5 x32)))) (>= ?v_34 (+ (+ (+ (+ (* x1 x13) (* x2 x18)) (* x3 x23)) (* x4 x28)) (* x5 x33)))) (>= ?v_35 (+ (+ (+ (+ (* x1 x14) (* x2 x19)) (* x3 x24)) (* x4 x29)) (* x5 x34)))) (>= ?v_36 (+ (+ (+ (+ (* x1 x15) (* x2 x20)) (* x3 x25)) (* x4 x30)) (* x5 x35)))))) (and (and (> ?v_5 ?v_37) (>= ?v_5 ?v_37)) (and (and (and (and (>= ?v_32 (+ (+ (+ (+ (* x1 ?v_70) (* x2 ?v_71)) (* x3 ?v_72)) (* x4 ?v_73)) (* x5 ?v_74))) (>= ?v_33 (+ (+ (+ (+ (* x1 ?v_90) (* x2 ?v_91)) (* x3 ?v_92)) (* x4 ?v_93)) (* x5 ?v_94)))) (>= ?v_34 (+ (+ (+ (+ (* x1 ?v_110) (* x2 ?v_111)) (* x3 ?v_112)) (* x4 ?v_113)) (* x5 ?v_114)))) (>= ?v_35 (+ (+ (+ (+ (* x1 ?v_130) (* x2 ?v_131)) (* x3 ?v_132)) (* x4 ?v_133)) (* x5 ?v_134)))) (>= ?v_36 (+ (+ (+ (+ (* x1 ?v_150) (* x2 ?v_151)) (* x3 ?v_152)) (* x4 ?v_153)) (* x5 ?v_154))))))) (?v_48 (+ x6 (+ (+ (+ (+ (* x11 ?v_43) (* x12 ?v_44)) (* x13 ?v_45)) (* x14 ?v_46)) (* x15 ?v_47)))) (?v_49 (+ x7 (+ (+ (+ (+ (* x16 ?v_43) (* x17 ?v_44)) (* x18 ?v_45)) (* x19 ?v_46)) (* x20 ?v_47)))) (?v_50 (+ x8 (+ (+ (+ (+ (* x21 ?v_43) (* x22 ?v_44)) (* x23 ?v_45)) (* x24 ?v_46)) (* x25 ?v_47)))) (?v_51 (+ x9 (+ (+ (+ (+ (* x26 ?v_43) (* x27 ?v_44)) (* x28 ?v_45)) (* x29 ?v_46)) (* x30 ?v_47)))) (?v_52 (+ x10 (+ (+ (+ (+ (* x31 ?v_43) (* x32 ?v_44)) (* x33 ?v_45)) (* x34 ?v_46)) (* x35 ?v_47))))) (let ((?v_53 (+ x36 (+ (+ (+ (+ (* x41 ?v_48) (* x42 ?v_49)) (* x43 ?v_50)) (* x44 ?v_51)) (* x45 ?v_52)))) (?v_54 (+ x37 (+ (+ (+ (+ (* x46 ?v_48) (* x47 ?v_49)) (* x48 ?v_50)) (* x49 ?v_51)) (* x50 ?v_52)))) (?v_55 (+ x38 (+ (+ (+ (+ (* x51 ?v_48) (* x52 ?v_49)) (* x53 ?v_50)) (* x54 ?v_51)) (* x55 ?v_52)))) (?v_56 (+ x39 (+ (+ (+ (+ (* x56 ?v_48) (* x57 ?v_49)) (* x58 ?v_50)) (* x59 ?v_51)) (* x60 ?v_52)))) (?v_57 (+ x40 (+ (+ (+ (+ (* x61 ?v_48) (* x62 ?v_49)) (* x63 ?v_50)) (* x64 ?v_51)) (* x65 ?v_52))))) (let ((?v_60 (+ x36 (+ (+ (+ (+ (* x41 ?v_53) (* x42 ?v_54)) (* x43 ?v_55)) (* x44 ?v_56)) (* x45 ?v_57)))) (?v_61 (+ x37 (+ (+ (+ (+ (* x46 ?v_53) (* x47 ?v_54)) (* x48 ?v_55)) (* x49 ?v_56)) (* x50 ?v_57)))) (?v_62 (+ x38 (+ (+ (+ (+ (* x51 ?v_53) (* x52 ?v_54)) (* x53 ?v_55)) (* x54 ?v_56)) (* x55 ?v_57)))) (?v_63 (+ x39 (+ (+ (+ (+ (* x56 ?v_53) (* x57 ?v_54)) (* x58 ?v_55)) (* x59 ?v_56)) (* x60 ?v_57)))) (?v_64 (+ x40 (+ (+ (+ (+ (* x61 ?v_53) (* x62 ?v_54)) (* x63 ?v_55)) (* x64 ?v_56)) (* x65 ?v_57))))) (let ((?v_59 (+ x36 (+ (+ (+ (+ (* x41 ?v_60) (* x42 ?v_61)) (* x43 ?v_62)) (* x44 ?v_63)) (* x45 ?v_64)))) (?v_58 (+ x6 (+ (+ (+ (+ (* x11 ?v_38) (* x12 ?v_39)) (* x13 ?v_40)) (* x14 ?v_41)) (* x15 ?v_42)))) (?v_75 (+ (+ (+ (+ (* x11 ?v_70) (* x12 ?v_71)) (* x13 ?v_72)) (* x14 ?v_73)) (* x15 ?v_74))) (?v_76 (+ (+ (+ (+ (* x16 ?v_70) (* x17 ?v_71)) (* x18 ?v_72)) (* x19 ?v_73)) (* x20 ?v_74))) (?v_77 (+ (+ (+ (+ (* x21 ?v_70) (* x22 ?v_71)) (* x23 ?v_72)) (* x24 ?v_73)) (* x25 ?v_74))) (?v_78 (+ (+ (+ (+ (* x26 ?v_70) (* x27 ?v_71)) (* x28 ?v_72)) (* x29 ?v_73)) (* x30 ?v_74))) (?v_79 (+ (+ (+ (+ (* x31 ?v_70) (* x32 ?v_71)) (* x33 ?v_72)) (* x34 ?v_73)) (* x35 ?v_74)))) (let ((?v_80 (+ (+ (+ (+ (* x41 ?v_75) (* x42 ?v_76)) (* x43 ?v_77)) (* x44 ?v_78)) (* x45 ?v_79))) (?v_81 (+ (+ (+ (+ (* x46 ?v_75) (* x47 ?v_76)) (* x48 ?v_77)) (* x49 ?v_78)) (* x50 ?v_79))) (?v_82 (+ (+ (+ (+ (* x51 ?v_75) (* x52 ?v_76)) (* x53 ?v_77)) (* x54 ?v_78)) (* x55 ?v_79))) (?v_83 (+ (+ (+ (+ (* x56 ?v_75) (* x57 ?v_76)) (* x58 ?v_77)) (* x59 ?v_78)) (* x60 ?v_79))) (?v_84 (+ (+ (+ (+ (* x61 ?v_75) (* x62 ?v_76)) (* x63 ?v_77)) (* x64 ?v_78)) (* x65 ?v_79)))) (let ((?v_165 (+ (+ (+ (+ (* x41 ?v_80) (* x42 ?v_81)) (* x43 ?v_82)) (* x44 ?v_83)) (* x45 ?v_84))) (?v_166 (+ (+ (+ (+ (* x46 ?v_80) (* x47 ?v_81)) (* x48 ?v_82)) (* x49 ?v_83)) (* x50 ?v_84))) (?v_167 (+ (+ (+ (+ (* x51 ?v_80) (* x52 ?v_81)) (* x53 ?v_82)) (* x54 ?v_83)) (* x55 ?v_84))) (?v_168 (+ (+ (+ (+ (* x56 ?v_80) (* x57 ?v_81)) (* x58 ?v_82)) (* x59 ?v_83)) (* x60 ?v_84))) (?v_169 (+ (+ (+ (+ (* x61 ?v_80) (* x62 ?v_81)) (* x63 ?v_82)) (* x64 ?v_83)) (* x65 ?v_84))) (?v_95 (+ (+ (+ (+ (* x11 ?v_90) (* x12 ?v_91)) (* x13 ?v_92)) (* x14 ?v_93)) (* x15 ?v_94))) (?v_96 (+ (+ (+ (+ (* x16 ?v_90) (* x17 ?v_91)) (* x18 ?v_92)) (* x19 ?v_93)) (* x20 ?v_94))) (?v_97 (+ (+ (+ (+ (* x21 ?v_90) (* x22 ?v_91)) (* x23 ?v_92)) (* x24 ?v_93)) (* x25 ?v_94))) (?v_98 (+ (+ (+ (+ (* x26 ?v_90) (* x27 ?v_91)) (* x28 ?v_92)) (* x29 ?v_93)) (* x30 ?v_94))) (?v_99 (+ (+ (+ (+ (* x31 ?v_90) (* x32 ?v_91)) (* x33 ?v_92)) (* x34 ?v_93)) (* x35 ?v_94)))) (let ((?v_100 (+ (+ (+ (+ (* x41 ?v_95) (* x42 ?v_96)) (* x43 ?v_97)) (* x44 ?v_98)) (* x45 ?v_99))) (?v_101 (+ (+ (+ (+ (* x46 ?v_95) (* x47 ?v_96)) (* x48 ?v_97)) (* x49 ?v_98)) (* x50 ?v_99))) (?v_102 (+ (+ (+ (+ (* x51 ?v_95) (* x52 ?v_96)) (* x53 ?v_97)) (* x54 ?v_98)) (* x55 ?v_99))) (?v_103 (+ (+ (+ (+ (* x56 ?v_95) (* x57 ?v_96)) (* x58 ?v_97)) (* x59 ?v_98)) (* x60 ?v_99))) (?v_104 (+ (+ (+ (+ (* x61 ?v_95) (* x62 ?v_96)) (* x63 ?v_97)) (* x64 ?v_98)) (* x65 ?v_99)))) (let ((?v_170 (+ (+ (+ (+ (* x41 ?v_100) (* x42 ?v_101)) (* x43 ?v_102)) (* x44 ?v_103)) (* x45 ?v_104))) (?v_171 (+ (+ (+ (+ (* x46 ?v_100) (* x47 ?v_101)) (* x48 ?v_102)) (* x49 ?v_103)) (* x50 ?v_104))) (?v_172 (+ (+ (+ (+ (* x51 ?v_100) (* x52 ?v_101)) (* x53 ?v_102)) (* x54 ?v_103)) (* x55 ?v_104))) (?v_173 (+ (+ (+ (+ (* x56 ?v_100) (* x57 ?v_101)) (* x58 ?v_102)) (* x59 ?v_103)) (* x60 ?v_104))) (?v_174 (+ (+ (+ (+ (* x61 ?v_100) (* x62 ?v_101)) (* x63 ?v_102)) (* x64 ?v_103)) (* x65 ?v_104))) (?v_115 (+ (+ (+ (+ (* x11 ?v_110) (* x12 ?v_111)) (* x13 ?v_112)) (* x14 ?v_113)) (* x15 ?v_114))) (?v_116 (+ (+ (+ (+ (* x16 ?v_110) (* x17 ?v_111)) (* x18 ?v_112)) (* x19 ?v_113)) (* x20 ?v_114))) (?v_117 (+ (+ (+ (+ (* x21 ?v_110) (* x22 ?v_111)) (* x23 ?v_112)) (* x24 ?v_113)) (* x25 ?v_114))) (?v_118 (+ (+ (+ (+ (* x26 ?v_110) (* x27 ?v_111)) (* x28 ?v_112)) (* x29 ?v_113)) (* x30 ?v_114))) (?v_119 (+ (+ (+ (+ (* x31 ?v_110) (* x32 ?v_111)) (* x33 ?v_112)) (* x34 ?v_113)) (* x35 ?v_114)))) (let ((?v_120 (+ (+ (+ (+ (* x41 ?v_115) (* x42 ?v_116)) (* x43 ?v_117)) (* x44 ?v_118)) (* x45 ?v_119))) (?v_121 (+ (+ (+ (+ (* x46 ?v_115) (* x47 ?v_116)) (* x48 ?v_117)) (* x49 ?v_118)) (* x50 ?v_119))) (?v_122 (+ (+ (+ (+ (* x51 ?v_115) (* x52 ?v_116)) (* x53 ?v_117)) (* x54 ?v_118)) (* x55 ?v_119))) (?v_123 (+ (+ (+ (+ (* x56 ?v_115) (* x57 ?v_116)) (* x58 ?v_117)) (* x59 ?v_118)) (* x60 ?v_119))) (?v_124 (+ (+ (+ (+ (* x61 ?v_115) (* x62 ?v_116)) (* x63 ?v_117)) (* x64 ?v_118)) (* x65 ?v_119)))) (let ((?v_175 (+ (+ (+ (+ (* x41 ?v_120) (* x42 ?v_121)) (* x43 ?v_122)) (* x44 ?v_123)) (* x45 ?v_124))) (?v_176 (+ (+ (+ (+ (* x46 ?v_120) (* x47 ?v_121)) (* x48 ?v_122)) (* x49 ?v_123)) (* x50 ?v_124))) (?v_177 (+ (+ (+ (+ (* x51 ?v_120) (* x52 ?v_121)) (* x53 ?v_122)) (* x54 ?v_123)) (* x55 ?v_124))) (?v_178 (+ (+ (+ (+ (* x56 ?v_120) (* x57 ?v_121)) (* x58 ?v_122)) (* x59 ?v_123)) (* x60 ?v_124))) (?v_179 (+ (+ (+ (+ (* x61 ?v_120) (* x62 ?v_121)) (* x63 ?v_122)) (* x64 ?v_123)) (* x65 ?v_124))) (?v_135 (+ (+ (+ (+ (* x11 ?v_130) (* x12 ?v_131)) (* x13 ?v_132)) (* x14 ?v_133)) (* x15 ?v_134))) (?v_136 (+ (+ (+ (+ (* x16 ?v_130) (* x17 ?v_131)) (* x18 ?v_132)) (* x19 ?v_133)) (* x20 ?v_134))) (?v_137 (+ (+ (+ (+ (* x21 ?v_130) (* x22 ?v_131)) (* x23 ?v_132)) (* x24 ?v_133)) (* x25 ?v_134))) (?v_138 (+ (+ (+ (+ (* x26 ?v_130) (* x27 ?v_131)) (* x28 ?v_132)) (* x29 ?v_133)) (* x30 ?v_134))) (?v_139 (+ (+ (+ (+ (* x31 ?v_130) (* x32 ?v_131)) (* x33 ?v_132)) (* x34 ?v_133)) (* x35 ?v_134)))) (let ((?v_140 (+ (+ (+ (+ (* x41 ?v_135) (* x42 ?v_136)) (* x43 ?v_137)) (* x44 ?v_138)) (* x45 ?v_139))) (?v_141 (+ (+ (+ (+ (* x46 ?v_135) (* x47 ?v_136)) (* x48 ?v_137)) (* x49 ?v_138)) (* x50 ?v_139))) (?v_142 (+ (+ (+ (+ (* x51 ?v_135) (* x52 ?v_136)) (* x53 ?v_137)) (* x54 ?v_138)) (* x55 ?v_139))) (?v_143 (+ (+ (+ (+ (* x56 ?v_135) (* x57 ?v_136)) (* x58 ?v_137)) (* x59 ?v_138)) (* x60 ?v_139))) (?v_144 (+ (+ (+ (+ (* x61 ?v_135) (* x62 ?v_136)) (* x63 ?v_137)) (* x64 ?v_138)) (* x65 ?v_139)))) (let ((?v_180 (+ (+ (+ (+ (* x41 ?v_140) (* x42 ?v_141)) (* x43 ?v_142)) (* x44 ?v_143)) (* x45 ?v_144))) (?v_181 (+ (+ (+ (+ (* x46 ?v_140) (* x47 ?v_141)) (* x48 ?v_142)) (* x49 ?v_143)) (* x50 ?v_144))) (?v_182 (+ (+ (+ (+ (* x51 ?v_140) (* x52 ?v_141)) (* x53 ?v_142)) (* x54 ?v_143)) (* x55 ?v_144))) (?v_183 (+ (+ (+ (+ (* x56 ?v_140) (* x57 ?v_141)) (* x58 ?v_142)) (* x59 ?v_143)) (* x60 ?v_144))) (?v_184 (+ (+ (+ (+ (* x61 ?v_140) (* x62 ?v_141)) (* x63 ?v_142)) (* x64 ?v_143)) (* x65 ?v_144))) (?v_155 (+ (+ (+ (+ (* x11 ?v_150) (* x12 ?v_151)) (* x13 ?v_152)) (* x14 ?v_153)) (* x15 ?v_154))) (?v_156 (+ (+ (+ (+ (* x16 ?v_150) (* x17 ?v_151)) (* x18 ?v_152)) (* x19 ?v_153)) (* x20 ?v_154))) (?v_157 (+ (+ (+ (+ (* x21 ?v_150) (* x22 ?v_151)) (* x23 ?v_152)) (* x24 ?v_153)) (* x25 ?v_154))) (?v_158 (+ (+ (+ (+ (* x26 ?v_150) (* x27 ?v_151)) (* x28 ?v_152)) (* x29 ?v_153)) (* x30 ?v_154))) (?v_159 (+ (+ (+ (+ (* x31 ?v_150) (* x32 ?v_151)) (* x33 ?v_152)) (* x34 ?v_153)) (* x35 ?v_154)))) (let ((?v_160 (+ (+ (+ (+ (* x41 ?v_155) (* x42 ?v_156)) (* x43 ?v_157)) (* x44 ?v_158)) (* x45 ?v_159))) (?v_161 (+ (+ (+ (+ (* x46 ?v_155) (* x47 ?v_156)) (* x48 ?v_157)) (* x49 ?v_158)) (* x50 ?v_159))) (?v_162 (+ (+ (+ (+ (* x51 ?v_155) (* x52 ?v_156)) (* x53 ?v_157)) (* x54 ?v_158)) (* x55 ?v_159))) (?v_163 (+ (+ (+ (+ (* x56 ?v_155) (* x57 ?v_156)) (* x58 ?v_157)) (* x59 ?v_158)) (* x60 ?v_159))) (?v_164 (+ (+ (+ (+ (* x61 ?v_155) (* x62 ?v_156)) (* x63 ?v_157)) (* x64 ?v_158)) (* x65 ?v_159)))) (let ((?v_185 (+ (+ (+ (+ (* x41 ?v_160) (* x42 ?v_161)) (* x43 ?v_162)) (* x44 ?v_163)) (* x45 ?v_164))) (?v_186 (+ (+ (+ (+ (* x46 ?v_160) (* x47 ?v_161)) (* x48 ?v_162)) (* x49 ?v_163)) (* x50 ?v_164))) (?v_187 (+ (+ (+ (+ (* x51 ?v_160) (* x52 ?v_161)) (* x53 ?v_162)) (* x54 ?v_163)) (* x55 ?v_164))) (?v_188 (+ (+ (+ (+ (* x56 ?v_160) (* x57 ?v_161)) (* x58 ?v_162)) (* x59 ?v_163)) (* x60 ?v_164))) (?v_189 (+ (+ (+ (+ (* x61 ?v_160) (* x62 ?v_161)) (* x63 ?v_162)) (* x64 ?v_163)) (* x65 ?v_164)))) (and (and ?v_190 (and (and (> ?v_58 ?v_59) (and (and (and (and (>= ?v_58 ?v_59) (>= (+ x7 (+ (+ (+ (+ (* x16 ?v_38) (* x17 ?v_39)) (* x18 ?v_40)) (* x19 ?v_41)) (* x20 ?v_42))) (+ x37 (+ (+ (+ (+ (* x46 ?v_60) (* x47 ?v_61)) (* x48 ?v_62)) (* x49 ?v_63)) (* x50 ?v_64))))) (>= (+ x8 (+ (+ (+ (+ (* x21 ?v_38) (* x22 ?v_39)) (* x23 ?v_40)) (* x24 ?v_41)) (* x25 ?v_42))) (+ x38 (+ (+ (+ (+ (* x51 ?v_60) (* x52 ?v_61)) (* x53 ?v_62)) (* x54 ?v_63)) (* x55 ?v_64))))) (>= (+ x9 (+ (+ (+ (+ (* x26 ?v_38) (* x27 ?v_39)) (* x28 ?v_40)) (* x29 ?v_41)) (* x30 ?v_42))) (+ x39 (+ (+ (+ (+ (* x56 ?v_60) (* x57 ?v_61)) (* x58 ?v_62)) (* x59 ?v_63)) (* x60 ?v_64))))) (>= (+ x10 (+ (+ (+ (+ (* x31 ?v_38) (* x32 ?v_39)) (* x33 ?v_40)) (* x34 ?v_41)) (* x35 ?v_42))) (+ x40 (+ (+ (+ (+ (* x61 ?v_60) (* x62 ?v_61)) (* x63 ?v_62)) (* x64 ?v_63)) (* x65 ?v_64)))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (+ (* x11 ?v_65) (* x12 ?v_66)) (* x13 ?v_67)) (* x14 ?v_68)) (* x15 ?v_69)) (+ (+ (+ (+ (* x41 ?v_165) (* x42 ?v_166)) (* x43 ?v_167)) (* x44 ?v_168)) (* x45 ?v_169))) (>= (+ (+ (+ (+ (* x11 ?v_85) (* x12 ?v_86)) (* x13 ?v_87)) (* x14 ?v_88)) (* x15 ?v_89)) (+ (+ (+ (+ (* x41 ?v_170) (* x42 ?v_171)) (* x43 ?v_172)) (* x44 ?v_173)) (* x45 ?v_174)))) (>= (+ (+ (+ (+ (* x11 ?v_105) (* x12 ?v_106)) (* x13 ?v_107)) (* x14 ?v_108)) (* x15 ?v_109)) (+ (+ (+ (+ (* x41 ?v_175) (* x42 ?v_176)) (* x43 ?v_177)) (* x44 ?v_178)) (* x45 ?v_179)))) (>= (+ (+ (+ (+ (* x11 ?v_125) (* x12 ?v_126)) (* x13 ?v_127)) (* x14 ?v_128)) (* x15 ?v_129)) (+ (+ (+ (+ (* x41 ?v_180) (* x42 ?v_181)) (* x43 ?v_182)) (* x44 ?v_183)) (* x45 ?v_184)))) (>= (+ (+ (+ (+ (* x11 ?v_145) (* x12 ?v_146)) (* x13 ?v_147)) (* x14 ?v_148)) (* x15 ?v_149)) (+ (+ (+ (+ (* x41 ?v_185) (* x42 ?v_186)) (* x43 ?v_187)) (* x44 ?v_188)) (* x45 ?v_189)))) (>= (+ (+ (+ (+ (* x16 ?v_65) (* x17 ?v_66)) (* x18 ?v_67)) (* x19 ?v_68)) (* x20 ?v_69)) (+ (+ (+ (+ (* x46 ?v_165) (* x47 ?v_166)) (* x48 ?v_167)) (* x49 ?v_168)) (* x50 ?v_169)))) (>= (+ (+ (+ (+ (* x16 ?v_85) (* x17 ?v_86)) (* x18 ?v_87)) (* x19 ?v_88)) (* x20 ?v_89)) (+ (+ (+ (+ (* x46 ?v_170) (* x47 ?v_171)) (* x48 ?v_172)) (* x49 ?v_173)) (* x50 ?v_174)))) (>= (+ (+ (+ (+ (* x16 ?v_105) (* x17 ?v_106)) (* x18 ?v_107)) (* x19 ?v_108)) (* x20 ?v_109)) (+ (+ (+ (+ (* x46 ?v_175) (* x47 ?v_176)) (* x48 ?v_177)) (* x49 ?v_178)) (* x50 ?v_179)))) (>= (+ (+ (+ (+ (* x16 ?v_125) (* x17 ?v_126)) (* x18 ?v_127)) (* x19 ?v_128)) (* x20 ?v_129)) (+ (+ (+ (+ (* x46 ?v_180) (* x47 ?v_181)) (* x48 ?v_182)) (* x49 ?v_183)) (* x50 ?v_184)))) (>= (+ (+ (+ (+ (* x16 ?v_145) (* x17 ?v_146)) (* x18 ?v_147)) (* x19 ?v_148)) (* x20 ?v_149)) (+ (+ (+ (+ (* x46 ?v_185) (* x47 ?v_186)) (* x48 ?v_187)) (* x49 ?v_188)) (* x50 ?v_189)))) (>= (+ (+ (+ (+ (* x21 ?v_65) (* x22 ?v_66)) (* x23 ?v_67)) (* x24 ?v_68)) (* x25 ?v_69)) (+ (+ (+ (+ (* x51 ?v_165) (* x52 ?v_166)) (* x53 ?v_167)) (* x54 ?v_168)) (* x55 ?v_169)))) (>= (+ (+ (+ (+ (* x21 ?v_85) (* x22 ?v_86)) (* x23 ?v_87)) (* x24 ?v_88)) (* x25 ?v_89)) (+ (+ (+ (+ (* x51 ?v_170) (* x52 ?v_171)) (* x53 ?v_172)) (* x54 ?v_173)) (* x55 ?v_174)))) (>= (+ (+ (+ (+ (* x21 ?v_105) (* x22 ?v_106)) (* x23 ?v_107)) (* x24 ?v_108)) (* x25 ?v_109)) (+ (+ (+ (+ (* x51 ?v_175) (* x52 ?v_176)) (* x53 ?v_177)) (* x54 ?v_178)) (* x55 ?v_179)))) (>= (+ (+ (+ (+ (* x21 ?v_125) (* x22 ?v_126)) (* x23 ?v_127)) (* x24 ?v_128)) (* x25 ?v_129)) (+ (+ (+ (+ (* x51 ?v_180) (* x52 ?v_181)) (* x53 ?v_182)) (* x54 ?v_183)) (* x55 ?v_184)))) (>= (+ (+ (+ (+ (* x21 ?v_145) (* x22 ?v_146)) (* x23 ?v_147)) (* x24 ?v_148)) (* x25 ?v_149)) (+ (+ (+ (+ (* x51 ?v_185) (* x52 ?v_186)) (* x53 ?v_187)) (* x54 ?v_188)) (* x55 ?v_189)))) (>= (+ (+ (+ (+ (* x26 ?v_65) (* x27 ?v_66)) (* x28 ?v_67)) (* x29 ?v_68)) (* x30 ?v_69)) (+ (+ (+ (+ (* x56 ?v_165) (* x57 ?v_166)) (* x58 ?v_167)) (* x59 ?v_168)) (* x60 ?v_169)))) (>= (+ (+ (+ (+ (* x26 ?v_85) (* x27 ?v_86)) (* x28 ?v_87)) (* x29 ?v_88)) (* x30 ?v_89)) (+ (+ (+ (+ (* x56 ?v_170) (* x57 ?v_171)) (* x58 ?v_172)) (* x59 ?v_173)) (* x60 ?v_174)))) (>= (+ (+ (+ (+ (* x26 ?v_105) (* x27 ?v_106)) (* x28 ?v_107)) (* x29 ?v_108)) (* x30 ?v_109)) (+ (+ (+ (+ (* x56 ?v_175) (* x57 ?v_176)) (* x58 ?v_177)) (* x59 ?v_178)) (* x60 ?v_179)))) (>= (+ (+ (+ (+ (* x26 ?v_125) (* x27 ?v_126)) (* x28 ?v_127)) (* x29 ?v_128)) (* x30 ?v_129)) (+ (+ (+ (+ (* x56 ?v_180) (* x57 ?v_181)) (* x58 ?v_182)) (* x59 ?v_183)) (* x60 ?v_184)))) (>= (+ (+ (+ (+ (* x26 ?v_145) (* x27 ?v_146)) (* x28 ?v_147)) (* x29 ?v_148)) (* x30 ?v_149)) (+ (+ (+ (+ (* x56 ?v_185) (* x57 ?v_186)) (* x58 ?v_187)) (* x59 ?v_188)) (* x60 ?v_189)))) (>= (+ (+ (+ (+ (* x31 ?v_65) (* x32 ?v_66)) (* x33 ?v_67)) (* x34 ?v_68)) (* x35 ?v_69)) (+ (+ (+ (+ (* x61 ?v_165) (* x62 ?v_166)) (* x63 ?v_167)) (* x64 ?v_168)) (* x65 ?v_169)))) (>= (+ (+ (+ (+ (* x31 ?v_85) (* x32 ?v_86)) (* x33 ?v_87)) (* x34 ?v_88)) (* x35 ?v_89)) (+ (+ (+ (+ (* x61 ?v_170) (* x62 ?v_171)) (* x63 ?v_172)) (* x64 ?v_173)) (* x65 ?v_174)))) (>= (+ (+ (+ (+ (* x31 ?v_105) (* x32 ?v_106)) (* x33 ?v_107)) (* x34 ?v_108)) (* x35 ?v_109)) (+ (+ (+ (+ (* x61 ?v_175) (* x62 ?v_176)) (* x63 ?v_177)) (* x64 ?v_178)) (* x65 ?v_179)))) (>= (+ (+ (+ (+ (* x31 ?v_125) (* x32 ?v_126)) (* x33 ?v_127)) (* x34 ?v_128)) (* x35 ?v_129)) (+ (+ (+ (+ (* x61 ?v_180) (* x62 ?v_181)) (* x63 ?v_182)) (* x64 ?v_183)) (* x65 ?v_184)))) (>= (+ (+ (+ (+ (* x31 ?v_145) (* x32 ?v_146)) (* x33 ?v_147)) (* x34 ?v_148)) (* x35 ?v_149)) (+ (+ (+ (+ (* x61 ?v_185) (* x62 ?v_186)) (* x63 ?v_187)) (* x64 ?v_188)) (* x65 ?v_189)))))) ?v_190))))))))))))))))))))))))))))))
(check-sat)
(exit)
