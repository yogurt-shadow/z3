(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x6 () Real)
(declare-fun x84 () Real)
(declare-fun x23 () Real)
(declare-fun x101 () Real)
(declare-fun x40 () Real)
(declare-fun x57 () Real)
(declare-fun x74 () Real)
(declare-fun x13 () Real)
(declare-fun x91 () Real)
(declare-fun x30 () Real)
(declare-fun x47 () Real)
(declare-fun x64 () Real)
(declare-fun x3 () Real)
(declare-fun x81 () Real)
(declare-fun x20 () Real)
(declare-fun x98 () Real)
(declare-fun x37 () Real)
(declare-fun x54 () Real)
(declare-fun x71 () Real)
(declare-fun x10 () Real)
(declare-fun x88 () Real)
(declare-fun x27 () Real)
(declare-fun x44 () Real)
(declare-fun x61 () Real)
(declare-fun x0 () Real)
(declare-fun x78 () Real)
(declare-fun x17 () Real)
(declare-fun x95 () Real)
(declare-fun x34 () Real)
(declare-fun x51 () Real)
(declare-fun x68 () Real)
(declare-fun x7 () Real)
(declare-fun x85 () Real)
(declare-fun x24 () Real)
(declare-fun x102 () Real)
(declare-fun x41 () Real)
(declare-fun x58 () Real)
(declare-fun x75 () Real)
(declare-fun x14 () Real)
(declare-fun x92 () Real)
(declare-fun x31 () Real)
(declare-fun x48 () Real)
(declare-fun x65 () Real)
(declare-fun x4 () Real)
(declare-fun x82 () Real)
(declare-fun x21 () Real)
(declare-fun x99 () Real)
(declare-fun x38 () Real)
(declare-fun x55 () Real)
(declare-fun x72 () Real)
(declare-fun x11 () Real)
(declare-fun x89 () Real)
(declare-fun x28 () Real)
(declare-fun x45 () Real)
(declare-fun x62 () Real)
(declare-fun x1 () Real)
(declare-fun x79 () Real)
(declare-fun x18 () Real)
(declare-fun x96 () Real)
(declare-fun x35 () Real)
(declare-fun x52 () Real)
(declare-fun x69 () Real)
(declare-fun x8 () Real)
(declare-fun x86 () Real)
(declare-fun x25 () Real)
(declare-fun x103 () Real)
(declare-fun x42 () Real)
(declare-fun x59 () Real)
(declare-fun x76 () Real)
(declare-fun x15 () Real)
(declare-fun x93 () Real)
(declare-fun x32 () Real)
(declare-fun x49 () Real)
(declare-fun x66 () Real)
(declare-fun x5 () Real)
(declare-fun x83 () Real)
(declare-fun x22 () Real)
(declare-fun x100 () Real)
(declare-fun x39 () Real)
(declare-fun x56 () Real)
(declare-fun x73 () Real)
(declare-fun x12 () Real)
(declare-fun x90 () Real)
(declare-fun x29 () Real)
(declare-fun x46 () Real)
(declare-fun x63 () Real)
(declare-fun x2 () Real)
(declare-fun x80 () Real)
(declare-fun x19 () Real)
(declare-fun x97 () Real)
(declare-fun x36 () Real)
(declare-fun x53 () Real)
(declare-fun x70 () Real)
(declare-fun x9 () Real)
(declare-fun x87 () Real)
(declare-fun x26 () Real)
(declare-fun x43 () Real)
(declare-fun x60 () Real)
(declare-fun x77 () Real)
(declare-fun x16 () Real)
(declare-fun x94 () Real)
(declare-fun x33 () Real)
(declare-fun x50 () Real)
(declare-fun x67 () Real)
(assert (>= x6 0))
(assert (>= x84 0))
(assert (>= x23 0))
(assert (>= x101 0))
(assert (>= x40 0))
(assert (>= x57 0))
(assert (>= x74 0))
(assert (>= x13 0))
(assert (>= x91 0))
(assert (>= x30 0))
(assert (>= x47 0))
(assert (>= x64 0))
(assert (>= x3 0))
(assert (>= x81 0))
(assert (>= x20 0))
(assert (>= x98 0))
(assert (>= x37 0))
(assert (>= x54 0))
(assert (>= x71 0))
(assert (>= x10 0))
(assert (>= x88 0))
(assert (>= x27 0))
(assert (>= x44 0))
(assert (>= x61 0))
(assert (>= x0 0))
(assert (>= x78 0))
(assert (>= x17 0))
(assert (>= x95 0))
(assert (>= x34 0))
(assert (>= x51 0))
(assert (>= x68 0))
(assert (>= x7 0))
(assert (>= x85 0))
(assert (>= x24 0))
(assert (>= x102 0))
(assert (>= x41 0))
(assert (>= x58 0))
(assert (>= x75 0))
(assert (>= x14 0))
(assert (>= x92 0))
(assert (>= x31 0))
(assert (>= x48 0))
(assert (>= x65 0))
(assert (>= x4 0))
(assert (>= x82 0))
(assert (>= x21 0))
(assert (>= x99 0))
(assert (>= x38 0))
(assert (>= x55 0))
(assert (>= x72 0))
(assert (>= x11 0))
(assert (>= x89 0))
(assert (>= x28 0))
(assert (>= x45 0))
(assert (>= x62 0))
(assert (>= x1 0))
(assert (>= x79 0))
(assert (>= x18 0))
(assert (>= x96 0))
(assert (>= x35 0))
(assert (>= x52 0))
(assert (>= x69 0))
(assert (>= x8 0))
(assert (>= x86 0))
(assert (>= x25 0))
(assert (>= x103 0))
(assert (>= x42 0))
(assert (>= x59 0))
(assert (>= x76 0))
(assert (>= x15 0))
(assert (>= x93 0))
(assert (>= x32 0))
(assert (>= x49 0))
(assert (>= x66 0))
(assert (>= x5 0))
(assert (>= x83 0))
(assert (>= x22 0))
(assert (>= x100 0))
(assert (>= x39 0))
(assert (>= x56 0))
(assert (>= x73 0))
(assert (>= x12 0))
(assert (>= x90 0))
(assert (>= x29 0))
(assert (>= x46 0))
(assert (>= x63 0))
(assert (>= x2 0))
(assert (>= x80 0))
(assert (>= x19 0))
(assert (>= x97 0))
(assert (>= x36 0))
(assert (>= x53 0))
(assert (>= x70 0))
(assert (>= x9 0))
(assert (>= x87 0))
(assert (>= x26 0))
(assert (>= x43 0))
(assert (>= x60 0))
(assert (>= x77 0))
(assert (>= x16 0))
(assert (>= x94 0))
(assert (>= x33 0))
(assert (>= x50 0))
(assert (>= x67 0))
(assert (let ((?v_0 (+ x5 (+ (+ (+ (* x9 x25) (* x10 x26)) (* x11 x27)) (* x12 x28)))) (?v_1 (+ x6 (+ (+ (+ (* x13 x25) (* x14 x26)) (* x15 x27)) (* x16 x28)))) (?v_2 (+ x7 (+ (+ (+ (* x17 x25) (* x18 x26)) (* x19 x27)) (* x20 x28)))) (?v_3 (+ x8 (+ (+ (+ (* x21 x25) (* x22 x26)) (* x23 x27)) (* x24 x28))))) (let ((?v_5 (+ x29 (+ (+ (+ (* x30 ?v_0) (* x31 ?v_1)) (* x32 ?v_2)) (* x33 ?v_3)))) (?v_30 (+ x5 (+ (+ (+ (* x9 ?v_0) (* x10 ?v_1)) (* x11 ?v_2)) (* x12 ?v_3)))) (?v_31 (+ x6 (+ (+ (+ (* x13 ?v_0) (* x14 ?v_1)) (* x15 ?v_2)) (* x16 ?v_3)))) (?v_32 (+ x7 (+ (+ (+ (* x17 ?v_0) (* x18 ?v_1)) (* x19 ?v_2)) (* x20 ?v_3)))) (?v_33 (+ x8 (+ (+ (+ (* x21 ?v_0) (* x22 ?v_1)) (* x23 ?v_2)) (* x24 ?v_3))))) (let ((?v_4 (+ x0 (+ (+ (+ (* x1 ?v_30) (* x2 ?v_31)) (* x3 ?v_32)) (* x4 ?v_33)))) (?v_7 (+ x39 (+ (+ (+ (* x43 ?v_0) (* x44 ?v_1)) (* x45 ?v_2)) (* x46 ?v_3)))) (?v_8 (+ x40 (+ (+ (+ (* x47 ?v_0) (* x48 ?v_1)) (* x49 ?v_2)) (* x50 ?v_3)))) (?v_9 (+ x41 (+ (+ (+ (* x51 ?v_0) (* x52 ?v_1)) (* x53 ?v_2)) (* x54 ?v_3)))) (?v_10 (+ x42 (+ (+ (+ (* x55 ?v_0) (* x56 ?v_1)) (* x57 ?v_2)) (* x58 ?v_3))))) (let ((?v_6 (+ x34 (+ (+ (+ (* x35 ?v_7) (* x36 ?v_8)) (* x37 ?v_9)) (* x38 ?v_10)))) (?v_34 (+ x5 (+ (+ (+ (* x9 ?v_7) (* x10 ?v_8)) (* x11 ?v_9)) (* x12 ?v_10)))) (?v_35 (+ x6 (+ (+ (+ (* x13 ?v_7) (* x14 ?v_8)) (* x15 ?v_9)) (* x16 ?v_10)))) (?v_36 (+ x7 (+ (+ (+ (* x17 ?v_7) (* x18 ?v_8)) (* x19 ?v_9)) (* x20 ?v_10)))) (?v_37 (+ x8 (+ (+ (+ (* x21 ?v_7) (* x22 ?v_8)) (* x23 ?v_9)) (* x24 ?v_10))))) (let ((?v_11 (+ x59 (+ (+ (+ (* x60 ?v_34) (* x61 ?v_35)) (* x62 ?v_36)) (* x63 ?v_37)))) (?v_12 (+ x59 (+ (+ (+ (* x60 x5) (* x61 x6)) (* x62 x7)) (* x63 x8)))) (?v_14 (+ (+ (+ (* x60 x9) (* x61 x13)) (* x62 x17)) (* x63 x21))) (?v_15 (+ (+ (+ (* x60 x10) (* x61 x14)) (* x62 x18)) (* x63 x22))) (?v_16 (+ (+ (+ (* x60 x11) (* x61 x15)) (* x62 x19)) (* x63 x23))) (?v_17 (+ (+ (+ (* x60 x12) (* x61 x16)) (* x62 x20)) (* x63 x24))) (?v_13 (+ x34 (+ (+ (+ (* x35 x64) (* x36 x65)) (* x37 x66)) (* x38 x67)))) (?v_23 (+ (+ (+ (* x35 x68) (* x36 x72)) (* x37 x76)) (* x38 x80))) (?v_24 (+ (+ (+ (* x35 x69) (* x36 x73)) (* x37 x77)) (* x38 x81))) (?v_25 (+ (+ (+ (* x35 x70) (* x36 x74)) (* x37 x78)) (* x38 x82))) (?v_26 (+ (+ (+ (* x35 x71) (* x36 x75)) (* x37 x79)) (* x38 x83))) (?v_40 (+ x5 (+ (+ (+ (* x9 x64) (* x10 x65)) (* x11 x66)) (* x12 x67)))) (?v_41 (+ x6 (+ (+ (+ (* x13 x64) (* x14 x65)) (* x15 x66)) (* x16 x67)))) (?v_42 (+ x7 (+ (+ (+ (* x17 x64) (* x18 x65)) (* x19 x66)) (* x20 x67)))) (?v_43 (+ x8 (+ (+ (+ (* x21 x64) (* x22 x65)) (* x23 x66)) (* x24 x67))))) (let ((?v_18 (+ x0 (+ (+ (+ (* x1 ?v_40) (* x2 ?v_41)) (* x3 ?v_42)) (* x4 ?v_43)))) (?v_46 (+ (+ (+ (* x9 x68) (* x10 x72)) (* x11 x76)) (* x12 x80))) (?v_47 (+ (+ (+ (* x13 x68) (* x14 x72)) (* x15 x76)) (* x16 x80))) (?v_48 (+ (+ (+ (* x17 x68) (* x18 x72)) (* x19 x76)) (* x20 x80))) (?v_49 (+ (+ (+ (* x21 x68) (* x22 x72)) (* x23 x76)) (* x24 x80))) (?v_50 (+ (+ (+ (* x9 x69) (* x10 x73)) (* x11 x77)) (* x12 x81))) (?v_51 (+ (+ (+ (* x13 x69) (* x14 x73)) (* x15 x77)) (* x16 x81))) (?v_52 (+ (+ (+ (* x17 x69) (* x18 x73)) (* x19 x77)) (* x20 x81))) (?v_53 (+ (+ (+ (* x21 x69) (* x22 x73)) (* x23 x77)) (* x24 x81))) (?v_54 (+ (+ (+ (* x9 x70) (* x10 x74)) (* x11 x78)) (* x12 x82))) (?v_55 (+ (+ (+ (* x13 x70) (* x14 x74)) (* x15 x78)) (* x16 x82))) (?v_56 (+ (+ (+ (* x17 x70) (* x18 x74)) (* x19 x78)) (* x20 x82))) (?v_57 (+ (+ (+ (* x21 x70) (* x22 x74)) (* x23 x78)) (* x24 x82))) (?v_58 (+ (+ (+ (* x9 x71) (* x10 x75)) (* x11 x79)) (* x12 x83))) (?v_59 (+ (+ (+ (* x13 x71) (* x14 x75)) (* x15 x79)) (* x16 x83))) (?v_60 (+ (+ (+ (* x17 x71) (* x18 x75)) (* x19 x79)) (* x20 x83))) (?v_61 (+ (+ (+ (* x21 x71) (* x22 x75)) (* x23 x79)) (* x24 x83))) (?v_20 (+ x0 (+ (+ (+ (* x1 x25) (* x2 x26)) (* x3 x27)) (* x4 x28)))) (?v_19 (+ x59 (+ (+ (+ (* x60 x25) (* x61 x26)) (* x62 x27)) (* x63 x28)))) (?v_22 (+ x0 (+ (+ (+ (* x1 x39) (* x2 x40)) (* x3 x41)) (* x4 x42)))) (?v_21 (+ x59 (+ (+ (+ (* x60 x39) (* x61 x40)) (* x62 x41)) (* x63 x42)))) (?v_27 (+ x34 (+ (+ (+ (* x35 x84) (* x36 x85)) (* x37 x86)) (* x38 x87)))) (?v_28 (+ x29 (+ (+ (+ (* x30 x64) (* x31 x65)) (* x32 x66)) (* x33 x67)))) (?v_29 (+ x29 (+ (+ (+ (* x30 x84) (* x31 x85)) (* x32 x86)) (* x33 x87))))) (let ((?v_69 (and (and (and (and (and (and (and (and (and (and (and (and (> ?v_4 ?v_5) (>= ?v_4 ?v_5)) (and (> ?v_4 ?v_6) (>= ?v_4 ?v_6))) (and (> ?v_4 ?v_11) (>= ?v_4 ?v_11))) (and (and (> ?v_12 x59) (>= ?v_12 x59)) (and (and (and (>= ?v_14 x60) (>= ?v_15 x61)) (>= ?v_16 x62)) (>= ?v_17 x63)))) (and (and (> ?v_12 ?v_13) (>= ?v_12 ?v_13)) (and (and (and (>= ?v_14 ?v_23) (>= ?v_15 ?v_24)) (>= ?v_16 ?v_25)) (>= ?v_17 ?v_26)))) (and (and (> ?v_12 ?v_18) (>= ?v_12 ?v_18)) (and (and (and (>= ?v_14 (+ (+ (+ (* x1 ?v_46) (* x2 ?v_47)) (* x3 ?v_48)) (* x4 ?v_49))) (>= ?v_15 (+ (+ (+ (* x1 ?v_50) (* x2 ?v_51)) (* x3 ?v_52)) (* x4 ?v_53)))) (>= ?v_16 (+ (+ (+ (* x1 ?v_54) (* x2 ?v_55)) (* x3 ?v_56)) (* x4 ?v_57)))) (>= ?v_17 (+ (+ (+ (* x1 ?v_58) (* x2 ?v_59)) (* x3 ?v_60)) (* x4 ?v_61)))))) (and (> ?v_19 ?v_20) (>= ?v_19 ?v_20))) (and (and (> ?v_21 ?v_22) (>= ?v_21 ?v_22)) (and (and (and (>= (+ (+ (+ (* x60 x43) (* x61 x47)) (* x62 x51)) (* x63 x55)) (+ (+ (+ (* x1 x43) (* x2 x47)) (* x3 x51)) (* x4 x55))) (>= (+ (+ (+ (* x60 x44) (* x61 x48)) (* x62 x52)) (* x63 x56)) (+ (+ (+ (* x1 x44) (* x2 x48)) (* x3 x52)) (* x4 x56)))) (>= (+ (+ (+ (* x60 x45) (* x61 x49)) (* x62 x53)) (* x63 x57)) (+ (+ (+ (* x1 x45) (* x2 x49)) (* x3 x53)) (* x4 x57)))) (>= (+ (+ (+ (* x60 x46) (* x61 x50)) (* x62 x54)) (* x63 x58)) (+ (+ (+ (* x1 x46) (* x2 x50)) (* x3 x54)) (* x4 x58)))))) (and (and (> ?v_13 x34) (>= ?v_13 x34)) (and (and (and (>= ?v_23 x35) (>= ?v_24 x36)) (>= ?v_25 x37)) (>= ?v_26 x38)))) (and (and (> ?v_27 x34) (>= ?v_27 x34)) (and (and (and (>= (+ (+ (+ (* x35 x88) (* x36 x92)) (* x37 x96)) (* x38 x100)) x35) (>= (+ (+ (+ (* x35 x89) (* x36 x93)) (* x37 x97)) (* x38 x101)) x36)) (>= (+ (+ (+ (* x35 x90) (* x36 x94)) (* x37 x98)) (* x38 x102)) x37)) (>= (+ (+ (+ (* x35 x91) (* x36 x95)) (* x37 x99)) (* x38 x103)) x38)))) (and (and (> ?v_28 x29) (>= ?v_28 x29)) (and (and (and (>= (+ (+ (+ (* x30 x68) (* x31 x72)) (* x32 x76)) (* x33 x80)) x30) (>= (+ (+ (+ (* x30 x69) (* x31 x73)) (* x32 x77)) (* x33 x81)) x31)) (>= (+ (+ (+ (* x30 x70) (* x31 x74)) (* x32 x78)) (* x33 x82)) x32)) (>= (+ (+ (+ (* x30 x71) (* x31 x75)) (* x32 x79)) (* x33 x83)) x33)))) (and (and (> ?v_29 x29) (>= ?v_29 x29)) (and (and (and (>= (+ (+ (+ (* x30 x88) (* x31 x92)) (* x32 x96)) (* x33 x100)) x30) (>= (+ (+ (+ (* x30 x89) (* x31 x93)) (* x32 x97)) (* x33 x101)) x31)) (>= (+ (+ (+ (* x30 x90) (* x31 x94)) (* x32 x98)) (* x33 x102)) x32)) (>= (+ (+ (+ (* x30 x91) (* x31 x95)) (* x32 x99)) (* x33 x103)) x33))))) (?v_39 (+ x64 (+ (+ (+ (* x68 ?v_34) (* x69 ?v_35)) (* x70 ?v_36)) (* x71 ?v_37)))) (?v_38 (+ x84 (+ (+ (+ (* x88 ?v_30) (* x89 ?v_31)) (* x90 ?v_32)) (* x91 ?v_33)))) (?v_45 (+ x84 (+ (+ (+ (* x88 ?v_40) (* x89 ?v_41)) (* x90 ?v_42)) (* x91 ?v_43)))) (?v_44 (+ x64 (+ (+ (+ (* x68 x5) (* x69 x6)) (* x70 x7)) (* x71 x8)))) (?v_63 (+ x84 (+ (+ (+ (* x88 x25) (* x89 x26)) (* x90 x27)) (* x91 x28)))) (?v_62 (+ x64 (+ (+ (+ (* x68 x25) (* x69 x26)) (* x70 x27)) (* x71 x28)))) (?v_65 (+ x84 (+ (+ (+ (* x88 x39) (* x89 x40)) (* x90 x41)) (* x91 x42)))) (?v_64 (+ x64 (+ (+ (+ (* x68 x39) (* x69 x40)) (* x70 x41)) (* x71 x42)))) (?v_66 (+ x5 (+ (+ (+ (* x9 x84) (* x10 x85)) (* x11 x86)) (* x12 x87)))) (?v_67 (+ x39 (+ (+ (+ (* x43 x64) (* x44 x65)) (* x45 x66)) (* x46 x67)))) (?v_68 (+ x39 (+ (+ (+ (* x43 x84) (* x44 x85)) (* x45 x86)) (* x46 x87))))) (and (and (and (and (and (and (and (and (and ?v_69 (and (> ?v_38 ?v_39) (and (and (and (>= ?v_38 ?v_39) (>= (+ x85 (+ (+ (+ (* x92 ?v_30) (* x93 ?v_31)) (* x94 ?v_32)) (* x95 ?v_33))) (+ x65 (+ (+ (+ (* x72 ?v_34) (* x73 ?v_35)) (* x74 ?v_36)) (* x75 ?v_37))))) (>= (+ x86 (+ (+ (+ (* x96 ?v_30) (* x97 ?v_31)) (* x98 ?v_32)) (* x99 ?v_33))) (+ x66 (+ (+ (+ (* x76 ?v_34) (* x77 ?v_35)) (* x78 ?v_36)) (* x79 ?v_37))))) (>= (+ x87 (+ (+ (+ (* x100 ?v_30) (* x101 ?v_31)) (* x102 ?v_32)) (* x103 ?v_33))) (+ x67 (+ (+ (+ (* x80 ?v_34) (* x81 ?v_35)) (* x82 ?v_36)) (* x83 ?v_37))))))) (and (and (> ?v_44 ?v_45) (and (and (and (>= ?v_44 ?v_45) (>= (+ x65 (+ (+ (+ (* x72 x5) (* x73 x6)) (* x74 x7)) (* x75 x8))) (+ x85 (+ (+ (+ (* x92 ?v_40) (* x93 ?v_41)) (* x94 ?v_42)) (* x95 ?v_43))))) (>= (+ x66 (+ (+ (+ (* x76 x5) (* x77 x6)) (* x78 x7)) (* x79 x8))) (+ x86 (+ (+ (+ (* x96 ?v_40) (* x97 ?v_41)) (* x98 ?v_42)) (* x99 ?v_43))))) (>= (+ x67 (+ (+ (+ (* x80 x5) (* x81 x6)) (* x82 x7)) (* x83 x8))) (+ x87 (+ (+ (+ (* x100 ?v_40) (* x101 ?v_41)) (* x102 ?v_42)) (* x103 ?v_43)))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (* x68 x9) (* x69 x13)) (* x70 x17)) (* x71 x21)) (+ (+ (+ (* x88 ?v_46) (* x89 ?v_47)) (* x90 ?v_48)) (* x91 ?v_49))) (>= (+ (+ (+ (* x68 x10) (* x69 x14)) (* x70 x18)) (* x71 x22)) (+ (+ (+ (* x88 ?v_50) (* x89 ?v_51)) (* x90 ?v_52)) (* x91 ?v_53)))) (>= (+ (+ (+ (* x68 x11) (* x69 x15)) (* x70 x19)) (* x71 x23)) (+ (+ (+ (* x88 ?v_54) (* x89 ?v_55)) (* x90 ?v_56)) (* x91 ?v_57)))) (>= (+ (+ (+ (* x68 x12) (* x69 x16)) (* x70 x20)) (* x71 x24)) (+ (+ (+ (* x88 ?v_58) (* x89 ?v_59)) (* x90 ?v_60)) (* x91 ?v_61)))) (>= (+ (+ (+ (* x72 x9) (* x73 x13)) (* x74 x17)) (* x75 x21)) (+ (+ (+ (* x92 ?v_46) (* x93 ?v_47)) (* x94 ?v_48)) (* x95 ?v_49)))) (>= (+ (+ (+ (* x72 x10) (* x73 x14)) (* x74 x18)) (* x75 x22)) (+ (+ (+ (* x92 ?v_50) (* x93 ?v_51)) (* x94 ?v_52)) (* x95 ?v_53)))) (>= (+ (+ (+ (* x72 x11) (* x73 x15)) (* x74 x19)) (* x75 x23)) (+ (+ (+ (* x92 ?v_54) (* x93 ?v_55)) (* x94 ?v_56)) (* x95 ?v_57)))) (>= (+ (+ (+ (* x72 x12) (* x73 x16)) (* x74 x20)) (* x75 x24)) (+ (+ (+ (* x92 ?v_58) (* x93 ?v_59)) (* x94 ?v_60)) (* x95 ?v_61)))) (>= (+ (+ (+ (* x76 x9) (* x77 x13)) (* x78 x17)) (* x79 x21)) (+ (+ (+ (* x96 ?v_46) (* x97 ?v_47)) (* x98 ?v_48)) (* x99 ?v_49)))) (>= (+ (+ (+ (* x76 x10) (* x77 x14)) (* x78 x18)) (* x79 x22)) (+ (+ (+ (* x96 ?v_50) (* x97 ?v_51)) (* x98 ?v_52)) (* x99 ?v_53)))) (>= (+ (+ (+ (* x76 x11) (* x77 x15)) (* x78 x19)) (* x79 x23)) (+ (+ (+ (* x96 ?v_54) (* x97 ?v_55)) (* x98 ?v_56)) (* x99 ?v_57)))) (>= (+ (+ (+ (* x76 x12) (* x77 x16)) (* x78 x20)) (* x79 x24)) (+ (+ (+ (* x96 ?v_58) (* x97 ?v_59)) (* x98 ?v_60)) (* x99 ?v_61)))) (>= (+ (+ (+ (* x80 x9) (* x81 x13)) (* x82 x17)) (* x83 x21)) (+ (+ (+ (* x100 ?v_46) (* x101 ?v_47)) (* x102 ?v_48)) (* x103 ?v_49)))) (>= (+ (+ (+ (* x80 x10) (* x81 x14)) (* x82 x18)) (* x83 x22)) (+ (+ (+ (* x100 ?v_50) (* x101 ?v_51)) (* x102 ?v_52)) (* x103 ?v_53)))) (>= (+ (+ (+ (* x80 x11) (* x81 x15)) (* x82 x19)) (* x83 x23)) (+ (+ (+ (* x100 ?v_54) (* x101 ?v_55)) (* x102 ?v_56)) (* x103 ?v_57)))) (>= (+ (+ (+ (* x80 x12) (* x81 x16)) (* x82 x20)) (* x83 x24)) (+ (+ (+ (* x100 ?v_58) (* x101 ?v_59)) (* x102 ?v_60)) (* x103 ?v_61)))))) (and (> ?v_62 ?v_63) (and (and (and (>= ?v_62 ?v_63) (>= (+ x65 (+ (+ (+ (* x72 x25) (* x73 x26)) (* x74 x27)) (* x75 x28))) (+ x85 (+ (+ (+ (* x92 x25) (* x93 x26)) (* x94 x27)) (* x95 x28))))) (>= (+ x66 (+ (+ (+ (* x76 x25) (* x77 x26)) (* x78 x27)) (* x79 x28))) (+ x86 (+ (+ (+ (* x96 x25) (* x97 x26)) (* x98 x27)) (* x99 x28))))) (>= (+ x67 (+ (+ (+ (* x80 x25) (* x81 x26)) (* x82 x27)) (* x83 x28))) (+ x87 (+ (+ (+ (* x100 x25) (* x101 x26)) (* x102 x27)) (* x103 x28))))))) (and (and (> ?v_64 ?v_65) (and (and (and (>= ?v_64 ?v_65) (>= (+ x65 (+ (+ (+ (* x72 x39) (* x73 x40)) (* x74 x41)) (* x75 x42))) (+ x85 (+ (+ (+ (* x92 x39) (* x93 x40)) (* x94 x41)) (* x95 x42))))) (>= (+ x66 (+ (+ (+ (* x76 x39) (* x77 x40)) (* x78 x41)) (* x79 x42))) (+ x86 (+ (+ (+ (* x96 x39) (* x97 x40)) (* x98 x41)) (* x99 x42))))) (>= (+ x67 (+ (+ (+ (* x80 x39) (* x81 x40)) (* x82 x41)) (* x83 x42))) (+ x87 (+ (+ (+ (* x100 x39) (* x101 x40)) (* x102 x41)) (* x103 x42)))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (* x68 x43) (* x69 x47)) (* x70 x51)) (* x71 x55)) (+ (+ (+ (* x88 x43) (* x89 x47)) (* x90 x51)) (* x91 x55))) (>= (+ (+ (+ (* x68 x44) (* x69 x48)) (* x70 x52)) (* x71 x56)) (+ (+ (+ (* x88 x44) (* x89 x48)) (* x90 x52)) (* x91 x56)))) (>= (+ (+ (+ (* x68 x45) (* x69 x49)) (* x70 x53)) (* x71 x57)) (+ (+ (+ (* x88 x45) (* x89 x49)) (* x90 x53)) (* x91 x57)))) (>= (+ (+ (+ (* x68 x46) (* x69 x50)) (* x70 x54)) (* x71 x58)) (+ (+ (+ (* x88 x46) (* x89 x50)) (* x90 x54)) (* x91 x58)))) (>= (+ (+ (+ (* x72 x43) (* x73 x47)) (* x74 x51)) (* x75 x55)) (+ (+ (+ (* x92 x43) (* x93 x47)) (* x94 x51)) (* x95 x55)))) (>= (+ (+ (+ (* x72 x44) (* x73 x48)) (* x74 x52)) (* x75 x56)) (+ (+ (+ (* x92 x44) (* x93 x48)) (* x94 x52)) (* x95 x56)))) (>= (+ (+ (+ (* x72 x45) (* x73 x49)) (* x74 x53)) (* x75 x57)) (+ (+ (+ (* x92 x45) (* x93 x49)) (* x94 x53)) (* x95 x57)))) (>= (+ (+ (+ (* x72 x46) (* x73 x50)) (* x74 x54)) (* x75 x58)) (+ (+ (+ (* x92 x46) (* x93 x50)) (* x94 x54)) (* x95 x58)))) (>= (+ (+ (+ (* x76 x43) (* x77 x47)) (* x78 x51)) (* x79 x55)) (+ (+ (+ (* x96 x43) (* x97 x47)) (* x98 x51)) (* x99 x55)))) (>= (+ (+ (+ (* x76 x44) (* x77 x48)) (* x78 x52)) (* x79 x56)) (+ (+ (+ (* x96 x44) (* x97 x48)) (* x98 x52)) (* x99 x56)))) (>= (+ (+ (+ (* x76 x45) (* x77 x49)) (* x78 x53)) (* x79 x57)) (+ (+ (+ (* x96 x45) (* x97 x49)) (* x98 x53)) (* x99 x57)))) (>= (+ (+ (+ (* x76 x46) (* x77 x50)) (* x78 x54)) (* x79 x58)) (+ (+ (+ (* x96 x46) (* x97 x50)) (* x98 x54)) (* x99 x58)))) (>= (+ (+ (+ (* x80 x43) (* x81 x47)) (* x82 x51)) (* x83 x55)) (+ (+ (+ (* x100 x43) (* x101 x47)) (* x102 x51)) (* x103 x55)))) (>= (+ (+ (+ (* x80 x44) (* x81 x48)) (* x82 x52)) (* x83 x56)) (+ (+ (+ (* x100 x44) (* x101 x48)) (* x102 x52)) (* x103 x56)))) (>= (+ (+ (+ (* x80 x45) (* x81 x49)) (* x82 x53)) (* x83 x57)) (+ (+ (+ (* x100 x45) (* x101 x49)) (* x102 x53)) (* x103 x57)))) (>= (+ (+ (+ (* x80 x46) (* x81 x50)) (* x82 x54)) (* x83 x58)) (+ (+ (+ (* x100 x46) (* x101 x50)) (* x102 x54)) (* x103 x58)))))) (and (and (> ?v_40 x5) (and (and (and (>= ?v_40 x5) (>= ?v_41 x6)) (>= ?v_42 x7)) (>= ?v_43 x8))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= ?v_46 x9) (>= ?v_50 x10)) (>= ?v_54 x11)) (>= ?v_58 x12)) (>= ?v_47 x13)) (>= ?v_51 x14)) (>= ?v_55 x15)) (>= ?v_59 x16)) (>= ?v_48 x17)) (>= ?v_52 x18)) (>= ?v_56 x19)) (>= ?v_60 x20)) (>= ?v_49 x21)) (>= ?v_53 x22)) (>= ?v_57 x23)) (>= ?v_61 x24)))) (and (and (> ?v_66 x5) (and (and (and (>= ?v_66 x5) (>= (+ x6 (+ (+ (+ (* x13 x84) (* x14 x85)) (* x15 x86)) (* x16 x87))) x6)) (>= (+ x7 (+ (+ (+ (* x17 x84) (* x18 x85)) (* x19 x86)) (* x20 x87))) x7)) (>= (+ x8 (+ (+ (+ (* x21 x84) (* x22 x85)) (* x23 x86)) (* x24 x87))) x8))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (* x9 x88) (* x10 x92)) (* x11 x96)) (* x12 x100)) x9) (>= (+ (+ (+ (* x9 x89) (* x10 x93)) (* x11 x97)) (* x12 x101)) x10)) (>= (+ (+ (+ (* x9 x90) (* x10 x94)) (* x11 x98)) (* x12 x102)) x11)) (>= (+ (+ (+ (* x9 x91) (* x10 x95)) (* x11 x99)) (* x12 x103)) x12)) (>= (+ (+ (+ (* x13 x88) (* x14 x92)) (* x15 x96)) (* x16 x100)) x13)) (>= (+ (+ (+ (* x13 x89) (* x14 x93)) (* x15 x97)) (* x16 x101)) x14)) (>= (+ (+ (+ (* x13 x90) (* x14 x94)) (* x15 x98)) (* x16 x102)) x15)) (>= (+ (+ (+ (* x13 x91) (* x14 x95)) (* x15 x99)) (* x16 x103)) x16)) (>= (+ (+ (+ (* x17 x88) (* x18 x92)) (* x19 x96)) (* x20 x100)) x17)) (>= (+ (+ (+ (* x17 x89) (* x18 x93)) (* x19 x97)) (* x20 x101)) x18)) (>= (+ (+ (+ (* x17 x90) (* x18 x94)) (* x19 x98)) (* x20 x102)) x19)) (>= (+ (+ (+ (* x17 x91) (* x18 x95)) (* x19 x99)) (* x20 x103)) x20)) (>= (+ (+ (+ (* x21 x88) (* x22 x92)) (* x23 x96)) (* x24 x100)) x21)) (>= (+ (+ (+ (* x21 x89) (* x22 x93)) (* x23 x97)) (* x24 x101)) x22)) (>= (+ (+ (+ (* x21 x90) (* x22 x94)) (* x23 x98)) (* x24 x102)) x23)) (>= (+ (+ (+ (* x21 x91) (* x22 x95)) (* x23 x99)) (* x24 x103)) x24)))) (and (and (> ?v_67 x39) (and (and (and (>= ?v_67 x39) (>= (+ x40 (+ (+ (+ (* x47 x64) (* x48 x65)) (* x49 x66)) (* x50 x67))) x40)) (>= (+ x41 (+ (+ (+ (* x51 x64) (* x52 x65)) (* x53 x66)) (* x54 x67))) x41)) (>= (+ x42 (+ (+ (+ (* x55 x64) (* x56 x65)) (* x57 x66)) (* x58 x67))) x42))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (* x43 x68) (* x44 x72)) (* x45 x76)) (* x46 x80)) x43) (>= (+ (+ (+ (* x43 x69) (* x44 x73)) (* x45 x77)) (* x46 x81)) x44)) (>= (+ (+ (+ (* x43 x70) (* x44 x74)) (* x45 x78)) (* x46 x82)) x45)) (>= (+ (+ (+ (* x43 x71) (* x44 x75)) (* x45 x79)) (* x46 x83)) x46)) (>= (+ (+ (+ (* x47 x68) (* x48 x72)) (* x49 x76)) (* x50 x80)) x47)) (>= (+ (+ (+ (* x47 x69) (* x48 x73)) (* x49 x77)) (* x50 x81)) x48)) (>= (+ (+ (+ (* x47 x70) (* x48 x74)) (* x49 x78)) (* x50 x82)) x49)) (>= (+ (+ (+ (* x47 x71) (* x48 x75)) (* x49 x79)) (* x50 x83)) x50)) (>= (+ (+ (+ (* x51 x68) (* x52 x72)) (* x53 x76)) (* x54 x80)) x51)) (>= (+ (+ (+ (* x51 x69) (* x52 x73)) (* x53 x77)) (* x54 x81)) x52)) (>= (+ (+ (+ (* x51 x70) (* x52 x74)) (* x53 x78)) (* x54 x82)) x53)) (>= (+ (+ (+ (* x51 x71) (* x52 x75)) (* x53 x79)) (* x54 x83)) x54)) (>= (+ (+ (+ (* x55 x68) (* x56 x72)) (* x57 x76)) (* x58 x80)) x55)) (>= (+ (+ (+ (* x55 x69) (* x56 x73)) (* x57 x77)) (* x58 x81)) x56)) (>= (+ (+ (+ (* x55 x70) (* x56 x74)) (* x57 x78)) (* x58 x82)) x57)) (>= (+ (+ (+ (* x55 x71) (* x56 x75)) (* x57 x79)) (* x58 x83)) x58)))) (and (and (> ?v_68 x39) (and (and (and (>= ?v_68 x39) (>= (+ x40 (+ (+ (+ (* x47 x84) (* x48 x85)) (* x49 x86)) (* x50 x87))) x40)) (>= (+ x41 (+ (+ (+ (* x51 x84) (* x52 x85)) (* x53 x86)) (* x54 x87))) x41)) (>= (+ x42 (+ (+ (+ (* x55 x84) (* x56 x85)) (* x57 x86)) (* x58 x87))) x42))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (* x43 x88) (* x44 x92)) (* x45 x96)) (* x46 x100)) x43) (>= (+ (+ (+ (* x43 x89) (* x44 x93)) (* x45 x97)) (* x46 x101)) x44)) (>= (+ (+ (+ (* x43 x90) (* x44 x94)) (* x45 x98)) (* x46 x102)) x45)) (>= (+ (+ (+ (* x43 x91) (* x44 x95)) (* x45 x99)) (* x46 x103)) x46)) (>= (+ (+ (+ (* x47 x88) (* x48 x92)) (* x49 x96)) (* x50 x100)) x47)) (>= (+ (+ (+ (* x47 x89) (* x48 x93)) (* x49 x97)) (* x50 x101)) x48)) (>= (+ (+ (+ (* x47 x90) (* x48 x94)) (* x49 x98)) (* x50 x102)) x49)) (>= (+ (+ (+ (* x47 x91) (* x48 x95)) (* x49 x99)) (* x50 x103)) x50)) (>= (+ (+ (+ (* x51 x88) (* x52 x92)) (* x53 x96)) (* x54 x100)) x51)) (>= (+ (+ (+ (* x51 x89) (* x52 x93)) (* x53 x97)) (* x54 x101)) x52)) (>= (+ (+ (+ (* x51 x90) (* x52 x94)) (* x53 x98)) (* x54 x102)) x53)) (>= (+ (+ (+ (* x51 x91) (* x52 x95)) (* x53 x99)) (* x54 x103)) x54)) (>= (+ (+ (+ (* x55 x88) (* x56 x92)) (* x57 x96)) (* x58 x100)) x55)) (>= (+ (+ (+ (* x55 x89) (* x56 x93)) (* x57 x97)) (* x58 x101)) x56)) (>= (+ (+ (+ (* x55 x90) (* x56 x94)) (* x57 x98)) (* x58 x102)) x57)) (>= (+ (+ (+ (* x55 x91) (* x56 x95)) (* x57 x99)) (* x58 x103)) x58)))) ?v_69)))))))))
(check-sat)
(exit)
