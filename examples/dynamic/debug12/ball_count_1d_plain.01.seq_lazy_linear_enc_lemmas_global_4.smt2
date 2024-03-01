(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |Benchmarks generated from hycomp (https://es-static.fbk.eu/tools/hycomp/). BMC instances of non-linear hybrid automata taken from: Alessandro Cimatti, Sergio Mover, Stefano Tonetta, A quantifier-free SMT encoding of non-linear hybrid automata, FMCAD 2012 and Alessandro Cimatti, Sergio Mover, Stefano Tonetta, Quantier-free encoding of invariants for Hybrid Systems, Formal Methods in System Design. This instance solves a BMC problem of depth 4 and uses the quantifier free encoding with equivalences and lemmas encoding. Contacts: Sergio Mover (mover@fbk.eu), Stefano Tonetta (tonettas@fbk.eu), Alessandro Cimatti (cimatti@fbk.eu).|)
(set-info :category "industrial")
(set-info :status sat)
;; MathSAT API call trace
;; generated on Mon Mar 19 10:41:37 2012
(declare-fun b.counter.2__AT1 () Bool)
(declare-fun b.delta__AT2 () Real)
(declare-fun b.EVENT.0__AT2 () Bool)
(declare-fun speed_loss__AT0 () Real)
(declare-fun b.y__AT2 () Real)
(declare-fun b.EVENT.1__AT2 () Bool)
(declare-fun b.speed_y__AT0 () Real)
(declare-fun b.event_is_timed__AT1 () Bool)
(declare-fun b.counter.0__AT2 () Bool)
(declare-fun b.event_is_timed__AT0 () Bool)
(declare-fun b.counter.1__AT2 () Bool)
(declare-fun b.counter.3__AT1 () Bool)
(declare-fun b.delta__AT0 () Real)
(declare-fun b.event_is_timed__AT4 () Bool)
(declare-fun b.y__AT1 () Real)
(declare-fun b.event_is_timed__AT3 () Bool)
(declare-fun b.counter.0__AT1 () Bool)
(declare-fun b.counter.3__AT0 () Bool)
(declare-fun b.speed_y__AT2 () Real)
(declare-fun b.y__AT4 () Real)
(declare-fun b.y__AT3 () Real)
(declare-fun b.counter.2__AT2 () Bool)
(declare-fun b.delta__AT1 () Real)
(declare-fun b.counter.0__AT3 () Bool)
(declare-fun b.counter.3__AT2 () Bool)
(declare-fun b.EVENT.0__AT1 () Bool)
(declare-fun b.EVENT.1__AT0 () Bool)
(declare-fun b.delta__AT4 () Real)
(declare-fun b.time__AT3 () Real)
(declare-fun b.counter.1__AT3 () Bool)
(declare-fun b.EVENT.1__AT1 () Bool)
(declare-fun b.EVENT.0__AT0 () Bool)
(declare-fun b.EVENT.0__AT4 () Bool)
(declare-fun b.delta__AT3 () Real)
(declare-fun b.counter.2__AT3 () Bool)
(declare-fun b.time__AT1 () Real)
(declare-fun b.EVENT.1__AT4 () Bool)
(declare-fun b.EVENT.0__AT3 () Bool)
(declare-fun b.counter.3__AT3 () Bool)
(declare-fun b.speed_y__AT1 () Real)
(declare-fun b.EVENT.1__AT3 () Bool)
(declare-fun b.time__AT0 () Real)
(declare-fun b.speed_y__AT4 () Real)
(declare-fun b.event_is_timed__AT2 () Bool)
(declare-fun b.speed_y__AT3 () Real)
(declare-fun b.counter.0__AT4 () Bool)
(declare-fun b.y__AT0 () Real)
(declare-fun b.counter.1__AT4 () Bool)
(declare-fun b.counter.0__AT0 () Bool)
(declare-fun b.counter.2__AT4 () Bool)
(declare-fun b.counter.2__AT0 () Bool)
(declare-fun b.counter.1__AT0 () Bool)
(declare-fun b.time__AT4 () Real)
(declare-fun b.counter.1__AT1 () Bool)
(declare-fun b.counter.3__AT4 () Bool)
(declare-fun b.time__AT2 () Real)
(assert (let ((.def_850 (<= 0.0 b.speed_y__AT4)))
(let ((.def_844 (* (- 49.0) b.delta__AT4)))
(let ((.def_845 (* 5.0 b.speed_y__AT4)))
(let ((.def_847 (+ .def_845 .def_844)))
(let ((.def_848 (<= 0.0 .def_847)))
(let ((.def_849 (not .def_848)))
(let ((.def_881 (or .def_849 .def_850)))
(let ((.def_864 (<= .def_847 0.0 )))
(let ((.def_862 (<= b.speed_y__AT4 0.0 )))
(let ((.def_863 (not .def_862)))
(let ((.def_880 (or .def_863 .def_864)))
(let ((.def_882 (and .def_880 .def_881)))
(let ((.def_877 (and .def_862 .def_864)))
(let ((.def_876 (and .def_848 .def_850)))
(let ((.def_878 (or .def_876 .def_877)))
(let ((.def_836 (* b.speed_y__AT4 b.delta__AT4)))
(let ((.def_837 (* 10.0 .def_836)))
(let ((.def_834 (* b.delta__AT4 b.delta__AT4)))
(let ((.def_835 (* (- 49.0) .def_834)))
(let ((.def_838 (+ .def_835 .def_837)))
(let ((.def_839 (* 10.0 b.y__AT4)))
(let ((.def_841 (+ .def_839 .def_838)))
(let ((.def_856 (<= .def_841 0.0 )))
(let ((.def_870 (not .def_856)))
(let ((.def_854 (<= b.y__AT4 0.0 )))
(let ((.def_871 (or .def_854 .def_870)))
(let ((.def_824 (<= 0.0 b.y__AT4)))
(let ((.def_868 (not .def_824)))
(let ((.def_842 (<= 0.0 .def_841)))
(let ((.def_869 (or .def_842 .def_868)))
(let ((.def_872 (and .def_869 .def_871)))
(let ((.def_865 (not .def_864)))
(let ((.def_866 (or .def_863 .def_865)))
(let ((.def_867 (not .def_866)))
(let ((.def_873 (or .def_867 .def_872)))
(let ((.def_858 (not .def_842)))
(let ((.def_859 (or .def_824 .def_858)))
(let ((.def_855 (not .def_854)))
(let ((.def_857 (or .def_855 .def_856)))
(let ((.def_860 (and .def_857 .def_859)))
(let ((.def_851 (not .def_850)))
(let ((.def_852 (or .def_849 .def_851)))
(let ((.def_853 (not .def_852)))
(let ((.def_861 (or .def_853 .def_860)))
(let ((.def_874 (and .def_861 .def_873)))
(let ((.def_843 (and .def_824 .def_842)))
(let ((.def_875 (and .def_843 .def_874)))
(let ((.def_879 (and .def_875 .def_878)))
(let ((.def_883 (and .def_879 .def_882)))
(let ((.def_59 (<= speed_loss__AT0 (/ 1 2))))
(let ((.def_56 (<= (/ 1 10) speed_loss__AT0)))
(let ((.def_60 (and .def_56 .def_59)))
(let ((.def_884 (and .def_60 .def_883)))
(let ((.def_528 (not b.counter.0__AT3)))
(let ((.def_516 (not b.counter.1__AT3)))
(let ((.def_828 (and .def_516 .def_528)))
(let ((.def_523 (not b.counter.2__AT3)))
(let ((.def_829 (and .def_523 .def_828)))
(let ((.def_538 (not b.counter.3__AT3)))
(let ((.def_830 (and .def_538 .def_829)))
(let ((.def_825 (and .def_60 .def_824)))
(let ((.def_821 (not b.EVENT.0__AT4)))
(let ((.def_819 (not b.EVENT.1__AT4)))
(let ((.def_822 (or .def_819 .def_821)))
(let ((.def_6 (not b.counter.0__AT4)))
(let ((.def_4 (not b.counter.1__AT4)))
(let ((.def_812 (or .def_4 .def_6)))
(let ((.def_816 (or b.counter.3__AT4 .def_812)))
(let ((.def_813 (or b.counter.2__AT4 .def_812)))
(let ((.def_9 (not b.counter.2__AT4)))
(let ((.def_811 (or .def_6 .def_9)))
(let ((.def_814 (and .def_811 .def_813)))
(let ((.def_12 (not b.counter.3__AT4)))
(let ((.def_815 (or .def_12 .def_814)))
(let ((.def_817 (and .def_815 .def_816)))
(let ((.def_823 (and .def_817 .def_822)))
(let ((.def_826 (and .def_823 .def_825)))
(let ((.def_806 (<= 0.0 b.delta__AT3)))
(let ((.def_636 (not b.EVENT.0__AT3)))
(let ((.def_634 (not b.EVENT.1__AT3)))
(let ((.def_753 (and .def_634 .def_636)))
(let ((.def_757 (not .def_753)))
(let ((.def_807 (or .def_757 .def_806)))
(let ((.def_808 (or b.EVENT.1__AT3 .def_807)))
(let ((.def_745 (= b.counter.0__AT4 b.counter.0__AT3)))
(let ((.def_743 (= b.counter.1__AT4 b.counter.1__AT3)))
(let ((.def_741 (= b.counter.2__AT4 b.counter.2__AT3)))
(let ((.def_740 (= b.counter.3__AT4 b.counter.3__AT3)))
(let ((.def_742 (and .def_740 .def_741)))
(let ((.def_744 (and .def_742 .def_743)))
(let ((.def_746 (and .def_744 .def_745)))
(let ((.def_803 (or .def_746 .def_757)))
(let ((.def_804 (or b.EVENT.1__AT3 .def_803)))
(let ((.def_791 (* (- 10.0) b.y__AT4)))
(let ((.def_651 (* b.speed_y__AT3 b.delta__AT3)))
(let ((.def_652 (* 10.0 .def_651)))
(let ((.def_795 (+ .def_652 .def_791)))
(let ((.def_649 (* b.delta__AT3 b.delta__AT3)))
(let ((.def_650 (* (- 49.0) .def_649)))
(let ((.def_796 (+ .def_650 .def_795)))
(let ((.def_654 (* 10.0 b.y__AT3)))
(let ((.def_797 (+ .def_654 .def_796)))
(let ((.def_798 (= .def_797 0.0 )))
(let ((.def_787 (* (- 5.0) b.speed_y__AT4)))
(let ((.def_659 (* (- 49.0) b.delta__AT3)))
(let ((.def_788 (+ .def_659 .def_787)))
(let ((.def_660 (* 5.0 b.speed_y__AT3)))
(let ((.def_789 (+ .def_660 .def_788)))
(let ((.def_790 (= .def_789 0.0 )))
(let ((.def_799 (and .def_790 .def_798)))
(let ((.def_800 (or .def_757 .def_799)))
(let ((.def_751 (= b.y__AT3 b.y__AT4)))
(let ((.def_739 (= b.speed_y__AT3 b.speed_y__AT4)))
(let ((.def_784 (and .def_739 .def_751)))
(let ((.def_781 (= b.delta__AT3 0.0 )))
(let ((.def_782 (and .def_753 .def_781)))
(let ((.def_783 (not .def_782)))
(let ((.def_785 (or .def_783 .def_784)))
(let ((.def_786 (or b.EVENT.1__AT3 .def_785)))
(let ((.def_801 (and .def_786 .def_800)))
(let ((.def_763 (= b.time__AT3 b.time__AT4)))
(let ((.def_775 (and .def_751 .def_763)))
(let ((.def_776 (and .def_739 .def_775)))
(let ((.def_777 (and .def_746 .def_776)))
(let ((.def_778 (or .def_634 .def_777)))
(let ((.def_766 (* (- 1.0) b.time__AT4)))
(let ((.def_769 (+ b.delta__AT3 .def_766)))
(let ((.def_770 (+ b.time__AT3 .def_769)))
(let ((.def_771 (= .def_770 0.0 )))
(let ((.def_772 (or .def_757 .def_771)))
(let ((.def_773 (or b.EVENT.1__AT3 .def_772)))
(let ((.def_764 (or .def_753 .def_763)))
(let ((.def_765 (or b.EVENT.1__AT3 .def_764)))
(let ((.def_774 (and .def_765 .def_773)))
(let ((.def_779 (and .def_774 .def_778)))
(let ((.def_759 (= .def_757 b.event_is_timed__AT4)))
(let ((.def_756 (= b.event_is_timed__AT3 .def_753)))
(let ((.def_760 (and .def_756 .def_759)))
(let ((.def_747 (and .def_739 .def_746)))
(let ((.def_701 (= b.y__AT3 0.0 )))
(let ((.def_665 (<= 0.0 b.speed_y__AT3)))
(let ((.def_666 (not .def_665)))
(let ((.def_702 (and .def_666 .def_701)))
(let ((.def_748 (or .def_702 .def_747)))
(let ((.def_716 (or .def_6 b.counter.0__AT3)))
(let ((.def_715 (or b.counter.0__AT4 .def_528)))
(let ((.def_717 (and .def_715 .def_716)))
(let ((.def_718 (and .def_4 .def_717)))
(let ((.def_719 (or b.counter.1__AT3 .def_718)))
(let ((.def_714 (or b.counter.1__AT4 .def_516)))
(let ((.def_720 (and .def_714 .def_719)))
(let ((.def_731 (and .def_9 .def_720)))
(let ((.def_732 (or b.counter.2__AT3 .def_731)))
(let ((.def_726 (and .def_4 .def_528)))
(let ((.def_727 (or b.counter.1__AT3 .def_726)))
(let ((.def_728 (and .def_714 .def_727)))
(let ((.def_729 (and b.counter.2__AT4 .def_728)))
(let ((.def_730 (or .def_523 .def_729)))
(let ((.def_733 (and .def_730 .def_732)))
(let ((.def_734 (and b.counter.3__AT4 .def_733)))
(let ((.def_735 (or b.counter.3__AT3 .def_734)))
(let ((.def_721 (and b.counter.2__AT4 .def_720)))
(let ((.def_722 (or b.counter.2__AT3 .def_721)))
(let ((.def_710 (or b.counter.1__AT4 b.counter.1__AT3)))
(let ((.def_708 (and .def_4 b.counter.0__AT4)))
(let ((.def_709 (or .def_516 .def_708)))
(let ((.def_711 (and .def_709 .def_710)))
(let ((.def_712 (and .def_9 .def_711)))
(let ((.def_713 (or .def_523 .def_712)))
(let ((.def_723 (and .def_713 .def_722)))
(let ((.def_724 (and .def_12 .def_723)))
(let ((.def_725 (or .def_538 .def_724)))
(let ((.def_736 (and .def_725 .def_735)))
(let ((.def_704 (* (- 1.0) b.speed_y__AT3)))
(let ((.def_126 (* (- 1.0) speed_loss__AT0)))
(let ((.def_127 (+ 1.0 .def_126)))
(let ((.def_705 (* .def_127 .def_704)))
(let ((.def_707 (= .def_705 b.speed_y__AT4)))
(let ((.def_737 (and .def_707 .def_736)))
(let ((.def_703 (not .def_702)))
(let ((.def_738 (or .def_703 .def_737)))
(let ((.def_749 (and .def_738 .def_748)))
(let ((.def_752 (and .def_749 .def_751)))
(let ((.def_754 (or .def_752 .def_753)))
(let ((.def_755 (or b.EVENT.1__AT3 .def_754)))
(let ((.def_761 (and .def_755 .def_760)))
(let ((.def_780 (and .def_761 .def_779)))
(let ((.def_802 (and .def_780 .def_801)))
(let ((.def_805 (and .def_802 .def_804)))
(let ((.def_809 (and .def_805 .def_808)))
(let ((.def_810 (and .def_634 .def_809)))
(let ((.def_827 (and .def_810 .def_826)))
(let ((.def_831 (and .def_827 .def_830)))
(let ((.def_662 (+ .def_660 .def_659)))
(let ((.def_663 (<= 0.0 .def_662)))
(let ((.def_664 (not .def_663)))
(let ((.def_696 (or .def_664 .def_665)))
(let ((.def_679 (<= .def_662 0.0 )))
(let ((.def_677 (<= b.speed_y__AT3 0.0 )))
(let ((.def_678 (not .def_677)))
(let ((.def_695 (or .def_678 .def_679)))
(let ((.def_697 (and .def_695 .def_696)))
(let ((.def_692 (and .def_677 .def_679)))
(let ((.def_691 (and .def_663 .def_665)))
(let ((.def_693 (or .def_691 .def_692)))
(let ((.def_653 (+ .def_650 .def_652)))
(let ((.def_656 (+ .def_654 .def_653)))
(let ((.def_671 (<= .def_656 0.0 )))
(let ((.def_685 (not .def_671)))
(let ((.def_669 (<= b.y__AT3 0.0 )))
(let ((.def_686 (or .def_669 .def_685)))
(let ((.def_639 (<= 0.0 b.y__AT3)))
(let ((.def_683 (not .def_639)))
(let ((.def_657 (<= 0.0 .def_656)))
(let ((.def_684 (or .def_657 .def_683)))
(let ((.def_687 (and .def_684 .def_686)))
(let ((.def_680 (not .def_679)))
(let ((.def_681 (or .def_678 .def_680)))
(let ((.def_682 (not .def_681)))
(let ((.def_688 (or .def_682 .def_687)))
(let ((.def_673 (not .def_657)))
(let ((.def_674 (or .def_639 .def_673)))
(let ((.def_670 (not .def_669)))
(let ((.def_672 (or .def_670 .def_671)))
(let ((.def_675 (and .def_672 .def_674)))
(let ((.def_667 (or .def_664 .def_666)))
(let ((.def_668 (not .def_667)))
(let ((.def_676 (or .def_668 .def_675)))
(let ((.def_689 (and .def_676 .def_688)))
(let ((.def_658 (and .def_639 .def_657)))
(let ((.def_690 (and .def_658 .def_689)))
(let ((.def_694 (and .def_690 .def_693)))
(let ((.def_698 (and .def_694 .def_697)))
(let ((.def_699 (and .def_60 .def_698)))
(let ((.def_335 (not b.counter.0__AT2)))
(let ((.def_323 (not b.counter.1__AT2)))
(let ((.def_643 (and .def_323 .def_335)))
(let ((.def_330 (not b.counter.2__AT2)))
(let ((.def_644 (and .def_330 .def_643)))
(let ((.def_345 (not b.counter.3__AT2)))
(let ((.def_645 (and .def_345 .def_644)))
(let ((.def_640 (and .def_60 .def_639)))
(let ((.def_637 (or .def_634 .def_636)))
(let ((.def_627 (or .def_516 .def_528)))
(let ((.def_631 (or b.counter.3__AT3 .def_627)))
(let ((.def_628 (or b.counter.2__AT3 .def_627)))
(let ((.def_626 (or .def_523 .def_528)))
(let ((.def_629 (and .def_626 .def_628)))
(let ((.def_630 (or .def_538 .def_629)))
(let ((.def_632 (and .def_630 .def_631)))
(let ((.def_638 (and .def_632 .def_637)))
(let ((.def_641 (and .def_638 .def_640)))
(let ((.def_621 (<= 0.0 b.delta__AT2)))
(let ((.def_443 (not b.EVENT.0__AT2)))
(let ((.def_441 (not b.EVENT.1__AT2)))
(let ((.def_568 (and .def_441 .def_443)))
(let ((.def_572 (not .def_568)))
(let ((.def_622 (or .def_572 .def_621)))
(let ((.def_623 (or b.EVENT.1__AT2 .def_622)))
(let ((.def_560 (= b.counter.0__AT2 b.counter.0__AT3)))
(let ((.def_558 (= b.counter.1__AT2 b.counter.1__AT3)))
(let ((.def_556 (= b.counter.2__AT2 b.counter.2__AT3)))
(let ((.def_555 (= b.counter.3__AT2 b.counter.3__AT3)))
(let ((.def_557 (and .def_555 .def_556)))
(let ((.def_559 (and .def_557 .def_558)))
(let ((.def_561 (and .def_559 .def_560)))
(let ((.def_618 (or .def_561 .def_572)))
(let ((.def_619 (or b.EVENT.1__AT2 .def_618)))
(let ((.def_606 (* (- 10.0) b.y__AT3)))
(let ((.def_458 (* b.speed_y__AT2 b.delta__AT2)))
(let ((.def_459 (* 10.0 .def_458)))
(let ((.def_610 (+ .def_459 .def_606)))
(let ((.def_456 (* b.delta__AT2 b.delta__AT2)))
(let ((.def_457 (* (- 49.0) .def_456)))
(let ((.def_611 (+ .def_457 .def_610)))
(let ((.def_461 (* 10.0 b.y__AT2)))
(let ((.def_612 (+ .def_461 .def_611)))
(let ((.def_613 (= .def_612 0.0 )))
(let ((.def_602 (* (- 5.0) b.speed_y__AT3)))
(let ((.def_466 (* (- 49.0) b.delta__AT2)))
(let ((.def_603 (+ .def_466 .def_602)))
(let ((.def_467 (* 5.0 b.speed_y__AT2)))
(let ((.def_604 (+ .def_467 .def_603)))
(let ((.def_605 (= .def_604 0.0 )))
(let ((.def_614 (and .def_605 .def_613)))
(let ((.def_615 (or .def_572 .def_614)))
(let ((.def_566 (= b.y__AT2 b.y__AT3)))
(let ((.def_554 (= b.speed_y__AT2 b.speed_y__AT3)))
(let ((.def_599 (and .def_554 .def_566)))
(let ((.def_596 (= b.delta__AT2 0.0 )))
(let ((.def_597 (and .def_568 .def_596)))
(let ((.def_598 (not .def_597)))
(let ((.def_600 (or .def_598 .def_599)))
(let ((.def_601 (or b.EVENT.1__AT2 .def_600)))
(let ((.def_616 (and .def_601 .def_615)))
(let ((.def_578 (= b.time__AT2 b.time__AT3)))
(let ((.def_590 (and .def_566 .def_578)))
(let ((.def_591 (and .def_554 .def_590)))
(let ((.def_592 (and .def_561 .def_591)))
(let ((.def_593 (or .def_441 .def_592)))
(let ((.def_581 (* (- 1.0) b.time__AT3)))
(let ((.def_584 (+ b.delta__AT2 .def_581)))
(let ((.def_585 (+ b.time__AT2 .def_584)))
(let ((.def_586 (= .def_585 0.0 )))
(let ((.def_587 (or .def_572 .def_586)))
(let ((.def_588 (or b.EVENT.1__AT2 .def_587)))
(let ((.def_579 (or .def_568 .def_578)))
(let ((.def_580 (or b.EVENT.1__AT2 .def_579)))
(let ((.def_589 (and .def_580 .def_588)))
(let ((.def_594 (and .def_589 .def_593)))
(let ((.def_574 (= .def_572 b.event_is_timed__AT3)))
(let ((.def_571 (= b.event_is_timed__AT2 .def_568)))
(let ((.def_575 (and .def_571 .def_574)))
(let ((.def_562 (and .def_554 .def_561)))
(let ((.def_508 (= b.y__AT2 0.0 )))
(let ((.def_472 (<= 0.0 b.speed_y__AT2)))
(let ((.def_473 (not .def_472)))
(let ((.def_509 (and .def_473 .def_508)))
(let ((.def_563 (or .def_509 .def_562)))
(let ((.def_529 (or b.counter.0__AT2 .def_528)))
(let ((.def_527 (or .def_335 b.counter.0__AT3)))
(let ((.def_530 (and .def_527 .def_529)))
(let ((.def_531 (and .def_516 .def_530)))
(let ((.def_532 (or b.counter.1__AT2 .def_531)))
(let ((.def_526 (or .def_323 b.counter.1__AT3)))
(let ((.def_533 (and .def_526 .def_532)))
(let ((.def_546 (and .def_523 .def_533)))
(let ((.def_547 (or b.counter.2__AT2 .def_546)))
(let ((.def_541 (and .def_335 .def_516)))
(let ((.def_542 (or b.counter.1__AT2 .def_541)))
(let ((.def_543 (and .def_526 .def_542)))
(let ((.def_544 (and b.counter.2__AT3 .def_543)))
(let ((.def_545 (or .def_330 .def_544)))
(let ((.def_548 (and .def_545 .def_547)))
(let ((.def_549 (and b.counter.3__AT3 .def_548)))
(let ((.def_550 (or b.counter.3__AT2 .def_549)))
(let ((.def_534 (and b.counter.2__AT3 .def_533)))
(let ((.def_535 (or b.counter.2__AT2 .def_534)))
(let ((.def_520 (or b.counter.1__AT2 b.counter.1__AT3)))
(let ((.def_518 (and .def_516 b.counter.0__AT3)))
(let ((.def_519 (or .def_323 .def_518)))
(let ((.def_521 (and .def_519 .def_520)))
(let ((.def_524 (and .def_521 .def_523)))
(let ((.def_525 (or .def_330 .def_524)))
(let ((.def_536 (and .def_525 .def_535)))
(let ((.def_539 (and .def_536 .def_538)))
(let ((.def_540 (or .def_345 .def_539)))
(let ((.def_551 (and .def_540 .def_550)))
(let ((.def_511 (* (- 1.0) b.speed_y__AT2)))
(let ((.def_512 (* .def_127 .def_511)))
(let ((.def_514 (= .def_512 b.speed_y__AT3)))
(let ((.def_552 (and .def_514 .def_551)))
(let ((.def_510 (not .def_509)))
(let ((.def_553 (or .def_510 .def_552)))
(let ((.def_564 (and .def_553 .def_563)))
(let ((.def_567 (and .def_564 .def_566)))
(let ((.def_569 (or .def_567 .def_568)))
(let ((.def_570 (or b.EVENT.1__AT2 .def_569)))
(let ((.def_576 (and .def_570 .def_575)))
(let ((.def_595 (and .def_576 .def_594)))
(let ((.def_617 (and .def_595 .def_616)))
(let ((.def_620 (and .def_617 .def_619)))
(let ((.def_624 (and .def_620 .def_623)))
(let ((.def_625 (and .def_441 .def_624)))
(let ((.def_642 (and .def_625 .def_641)))
(let ((.def_646 (and .def_642 .def_645)))
(let ((.def_469 (+ .def_467 .def_466)))
(let ((.def_470 (<= 0.0 .def_469)))
(let ((.def_471 (not .def_470)))
(let ((.def_503 (or .def_471 .def_472)))
(let ((.def_486 (<= .def_469 0.0 )))
(let ((.def_484 (<= b.speed_y__AT2 0.0 )))
(let ((.def_485 (not .def_484)))
(let ((.def_502 (or .def_485 .def_486)))
(let ((.def_504 (and .def_502 .def_503)))
(let ((.def_499 (and .def_484 .def_486)))
(let ((.def_498 (and .def_470 .def_472)))
(let ((.def_500 (or .def_498 .def_499)))
(let ((.def_460 (+ .def_457 .def_459)))
(let ((.def_463 (+ .def_461 .def_460)))
(let ((.def_478 (<= .def_463 0.0 )))
(let ((.def_492 (not .def_478)))
(let ((.def_476 (<= b.y__AT2 0.0 )))
(let ((.def_493 (or .def_476 .def_492)))
(let ((.def_446 (<= 0.0 b.y__AT2)))
(let ((.def_490 (not .def_446)))
(let ((.def_464 (<= 0.0 .def_463)))
(let ((.def_491 (or .def_464 .def_490)))
(let ((.def_494 (and .def_491 .def_493)))
(let ((.def_487 (not .def_486)))
(let ((.def_488 (or .def_485 .def_487)))
(let ((.def_489 (not .def_488)))
(let ((.def_495 (or .def_489 .def_494)))
(let ((.def_480 (not .def_464)))
(let ((.def_481 (or .def_446 .def_480)))
(let ((.def_477 (not .def_476)))
(let ((.def_479 (or .def_477 .def_478)))
(let ((.def_482 (and .def_479 .def_481)))
(let ((.def_474 (or .def_471 .def_473)))
(let ((.def_475 (not .def_474)))
(let ((.def_483 (or .def_475 .def_482)))
(let ((.def_496 (and .def_483 .def_495)))
(let ((.def_465 (and .def_446 .def_464)))
(let ((.def_497 (and .def_465 .def_496)))
(let ((.def_501 (and .def_497 .def_500)))
(let ((.def_505 (and .def_501 .def_504)))
(let ((.def_506 (and .def_60 .def_505)))
(let ((.def_144 (not b.counter.0__AT1)))
(let ((.def_132 (not b.counter.1__AT1)))
(let ((.def_450 (and .def_132 .def_144)))
(let ((.def_139 (not b.counter.2__AT1)))
(let ((.def_451 (and .def_139 .def_450)))
(let ((.def_154 (not b.counter.3__AT1)))
(let ((.def_452 (and .def_154 .def_451)))
(let ((.def_447 (and .def_60 .def_446)))
(let ((.def_444 (or .def_441 .def_443)))
(let ((.def_434 (or .def_323 .def_335)))
(let ((.def_438 (or b.counter.3__AT2 .def_434)))
(let ((.def_435 (or b.counter.2__AT2 .def_434)))
(let ((.def_433 (or .def_330 .def_335)))
(let ((.def_436 (and .def_433 .def_435)))
(let ((.def_437 (or .def_345 .def_436)))
(let ((.def_439 (and .def_437 .def_438)))
(let ((.def_445 (and .def_439 .def_444)))
(let ((.def_448 (and .def_445 .def_447)))
(let ((.def_428 (<= 0.0 b.delta__AT1)))
(let ((.def_253 (not b.EVENT.0__AT1)))
(let ((.def_251 (not b.EVENT.1__AT1)))
(let ((.def_375 (and .def_251 .def_253)))
(let ((.def_379 (not .def_375)))
(let ((.def_429 (or .def_379 .def_428)))
(let ((.def_430 (or b.EVENT.1__AT1 .def_429)))
(let ((.def_367 (= b.counter.0__AT1 b.counter.0__AT2)))
(let ((.def_365 (= b.counter.1__AT1 b.counter.1__AT2)))
(let ((.def_363 (= b.counter.2__AT1 b.counter.2__AT2)))
(let ((.def_362 (= b.counter.3__AT1 b.counter.3__AT2)))
(let ((.def_364 (and .def_362 .def_363)))
(let ((.def_366 (and .def_364 .def_365)))
(let ((.def_368 (and .def_366 .def_367)))
(let ((.def_425 (or .def_368 .def_379)))
(let ((.def_426 (or b.EVENT.1__AT1 .def_425)))
(let ((.def_413 (* (- 10.0) b.y__AT2)))
(let ((.def_265 (* b.speed_y__AT1 b.delta__AT1)))
(let ((.def_266 (* 10.0 .def_265)))
(let ((.def_417 (+ .def_266 .def_413)))
(let ((.def_263 (* b.delta__AT1 b.delta__AT1)))
(let ((.def_264 (* (- 49.0) .def_263)))
(let ((.def_418 (+ .def_264 .def_417)))
(let ((.def_268 (* 10.0 b.y__AT1)))
(let ((.def_419 (+ .def_268 .def_418)))
(let ((.def_420 (= .def_419 0.0 )))
(let ((.def_409 (* (- 5.0) b.speed_y__AT2)))
(let ((.def_273 (* (- 49.0) b.delta__AT1)))
(let ((.def_410 (+ .def_273 .def_409)))
(let ((.def_274 (* 5.0 b.speed_y__AT1)))
(let ((.def_411 (+ .def_274 .def_410)))
(let ((.def_412 (= .def_411 0.0 )))
(let ((.def_421 (and .def_412 .def_420)))
(let ((.def_422 (or .def_379 .def_421)))
(let ((.def_373 (= b.y__AT1 b.y__AT2)))
(let ((.def_361 (= b.speed_y__AT1 b.speed_y__AT2)))
(let ((.def_406 (and .def_361 .def_373)))
(let ((.def_403 (= b.delta__AT1 0.0 )))
(let ((.def_404 (and .def_375 .def_403)))
(let ((.def_405 (not .def_404)))
(let ((.def_407 (or .def_405 .def_406)))
(let ((.def_408 (or b.EVENT.1__AT1 .def_407)))
(let ((.def_423 (and .def_408 .def_422)))
(let ((.def_385 (= b.time__AT1 b.time__AT2)))
(let ((.def_397 (and .def_373 .def_385)))
(let ((.def_398 (and .def_361 .def_397)))
(let ((.def_399 (and .def_368 .def_398)))
(let ((.def_400 (or .def_251 .def_399)))
(let ((.def_388 (* (- 1.0) b.time__AT2)))
(let ((.def_391 (+ b.delta__AT1 .def_388)))
(let ((.def_392 (+ b.time__AT1 .def_391)))
(let ((.def_393 (= .def_392 0.0 )))
(let ((.def_394 (or .def_379 .def_393)))
(let ((.def_395 (or b.EVENT.1__AT1 .def_394)))
(let ((.def_386 (or .def_375 .def_385)))
(let ((.def_387 (or b.EVENT.1__AT1 .def_386)))
(let ((.def_396 (and .def_387 .def_395)))
(let ((.def_401 (and .def_396 .def_400)))
(let ((.def_381 (= .def_379 b.event_is_timed__AT2)))
(let ((.def_378 (= b.event_is_timed__AT1 .def_375)))
(let ((.def_382 (and .def_378 .def_381)))
(let ((.def_369 (and .def_361 .def_368)))
(let ((.def_315 (= b.y__AT1 0.0 )))
(let ((.def_279 (<= 0.0 b.speed_y__AT1)))
(let ((.def_280 (not .def_279)))
(let ((.def_316 (and .def_280 .def_315)))
(let ((.def_370 (or .def_316 .def_369)))
(let ((.def_336 (or b.counter.0__AT1 .def_335)))
(let ((.def_334 (or .def_144 b.counter.0__AT2)))
(let ((.def_337 (and .def_334 .def_336)))
(let ((.def_338 (and .def_323 .def_337)))
(let ((.def_339 (or b.counter.1__AT1 .def_338)))
(let ((.def_333 (or .def_132 b.counter.1__AT2)))
(let ((.def_340 (and .def_333 .def_339)))
(let ((.def_353 (and .def_330 .def_340)))
(let ((.def_354 (or b.counter.2__AT1 .def_353)))
(let ((.def_348 (and .def_144 .def_323)))
(let ((.def_349 (or b.counter.1__AT1 .def_348)))
(let ((.def_350 (and .def_333 .def_349)))
(let ((.def_351 (and b.counter.2__AT2 .def_350)))
(let ((.def_352 (or .def_139 .def_351)))
(let ((.def_355 (and .def_352 .def_354)))
(let ((.def_356 (and b.counter.3__AT2 .def_355)))
(let ((.def_357 (or b.counter.3__AT1 .def_356)))
(let ((.def_341 (and b.counter.2__AT2 .def_340)))
(let ((.def_342 (or b.counter.2__AT1 .def_341)))
(let ((.def_327 (or b.counter.1__AT1 b.counter.1__AT2)))
(let ((.def_325 (and .def_323 b.counter.0__AT2)))
(let ((.def_326 (or .def_132 .def_325)))
(let ((.def_328 (and .def_326 .def_327)))
(let ((.def_331 (and .def_328 .def_330)))
(let ((.def_332 (or .def_139 .def_331)))
(let ((.def_343 (and .def_332 .def_342)))
(let ((.def_346 (and .def_343 .def_345)))
(let ((.def_347 (or .def_154 .def_346)))
(let ((.def_358 (and .def_347 .def_357)))
(let ((.def_318 (* (- 1.0) b.speed_y__AT1)))
(let ((.def_319 (* .def_127 .def_318)))
(let ((.def_321 (= .def_319 b.speed_y__AT2)))
(let ((.def_359 (and .def_321 .def_358)))
(let ((.def_317 (not .def_316)))
(let ((.def_360 (or .def_317 .def_359)))
(let ((.def_371 (and .def_360 .def_370)))
(let ((.def_374 (and .def_371 .def_373)))
(let ((.def_376 (or .def_374 .def_375)))
(let ((.def_377 (or b.EVENT.1__AT1 .def_376)))
(let ((.def_383 (and .def_377 .def_382)))
(let ((.def_402 (and .def_383 .def_401)))
(let ((.def_424 (and .def_402 .def_423)))
(let ((.def_427 (and .def_424 .def_426)))
(let ((.def_431 (and .def_427 .def_430)))
(let ((.def_432 (and .def_251 .def_431)))
(let ((.def_449 (and .def_432 .def_448)))
(let ((.def_453 (and .def_449 .def_452)))
(let ((.def_276 (+ .def_274 .def_273)))
(let ((.def_277 (<= 0.0 .def_276)))
(let ((.def_278 (not .def_277)))
(let ((.def_310 (or .def_278 .def_279)))
(let ((.def_293 (<= .def_276 0.0 )))
(let ((.def_291 (<= b.speed_y__AT1 0.0 )))
(let ((.def_292 (not .def_291)))
(let ((.def_309 (or .def_292 .def_293)))
(let ((.def_311 (and .def_309 .def_310)))
(let ((.def_306 (and .def_291 .def_293)))
(let ((.def_305 (and .def_277 .def_279)))
(let ((.def_307 (or .def_305 .def_306)))
(let ((.def_267 (+ .def_264 .def_266)))
(let ((.def_270 (+ .def_268 .def_267)))
(let ((.def_285 (<= .def_270 0.0 )))
(let ((.def_299 (not .def_285)))
(let ((.def_283 (<= b.y__AT1 0.0 )))
(let ((.def_300 (or .def_283 .def_299)))
(let ((.def_256 (<= 0.0 b.y__AT1)))
(let ((.def_297 (not .def_256)))
(let ((.def_271 (<= 0.0 .def_270)))
(let ((.def_298 (or .def_271 .def_297)))
(let ((.def_301 (and .def_298 .def_300)))
(let ((.def_294 (not .def_293)))
(let ((.def_295 (or .def_292 .def_294)))
(let ((.def_296 (not .def_295)))
(let ((.def_302 (or .def_296 .def_301)))
(let ((.def_287 (not .def_271)))
(let ((.def_288 (or .def_256 .def_287)))
(let ((.def_284 (not .def_283)))
(let ((.def_286 (or .def_284 .def_285)))
(let ((.def_289 (and .def_286 .def_288)))
(let ((.def_281 (or .def_278 .def_280)))
(let ((.def_282 (not .def_281)))
(let ((.def_290 (or .def_282 .def_289)))
(let ((.def_303 (and .def_290 .def_302)))
(let ((.def_272 (and .def_256 .def_271)))
(let ((.def_304 (and .def_272 .def_303)))
(let ((.def_308 (and .def_304 .def_307)))
(let ((.def_312 (and .def_308 .def_311)))
(let ((.def_313 (and .def_60 .def_312)))
(let ((.def_257 (and .def_60 .def_256)))
(let ((.def_254 (or .def_251 .def_253)))
(let ((.def_244 (or .def_132 .def_144)))
(let ((.def_248 (or b.counter.3__AT1 .def_244)))
(let ((.def_245 (or b.counter.2__AT1 .def_244)))
(let ((.def_243 (or .def_139 .def_144)))
(let ((.def_246 (and .def_243 .def_245)))
(let ((.def_247 (or .def_154 .def_246)))
(let ((.def_249 (and .def_247 .def_248)))
(let ((.def_255 (and .def_249 .def_254)))
(let ((.def_258 (and .def_255 .def_257)))
(let ((.def_238 (<= 0.0 b.delta__AT0)))
(let ((.def_49 (not b.EVENT.0__AT0)))
(let ((.def_47 (not b.EVENT.1__AT0)))
(let ((.def_184 (and .def_47 .def_49)))
(let ((.def_188 (not .def_184)))
(let ((.def_239 (or .def_188 .def_238)))
(let ((.def_240 (or b.EVENT.1__AT0 .def_239)))
(let ((.def_176 (= b.counter.0__AT0 b.counter.0__AT1)))
(let ((.def_174 (= b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_172 (= b.counter.2__AT0 b.counter.2__AT1)))
(let ((.def_171 (= b.counter.3__AT0 b.counter.3__AT1)))
(let ((.def_173 (and .def_171 .def_172)))
(let ((.def_175 (and .def_173 .def_174)))
(let ((.def_177 (and .def_175 .def_176)))
(let ((.def_235 (or .def_177 .def_188)))
(let ((.def_236 (or b.EVENT.1__AT0 .def_235)))
(let ((.def_224 (* (- 10.0) b.y__AT1)))
(let ((.def_70 (* b.speed_y__AT0 b.delta__AT0)))
(let ((.def_71 (* 10.0 .def_70)))
(let ((.def_227 (+ .def_71 .def_224)))
(let ((.def_66 (* b.delta__AT0 b.delta__AT0)))
(let ((.def_69 (* (- 49.0) .def_66)))
(let ((.def_228 (+ .def_69 .def_227)))
(let ((.def_73 (* 10.0 b.y__AT0)))
(let ((.def_229 (+ .def_73 .def_228)))
(let ((.def_230 (= .def_229 0.0 )))
(let ((.def_219 (* (- 5.0) b.speed_y__AT1)))
(let ((.def_78 (* (- 49.0) b.delta__AT0)))
(let ((.def_220 (+ .def_78 .def_219)))
(let ((.def_80 (* 5.0 b.speed_y__AT0)))
(let ((.def_221 (+ .def_80 .def_220)))
(let ((.def_222 (= .def_221 0.0 )))
(let ((.def_231 (and .def_222 .def_230)))
(let ((.def_232 (or .def_188 .def_231)))
(let ((.def_182 (= b.y__AT0 b.y__AT1)))
(let ((.def_170 (= b.speed_y__AT0 b.speed_y__AT1)))
(let ((.def_215 (and .def_170 .def_182)))
(let ((.def_212 (= b.delta__AT0 0.0 )))
(let ((.def_213 (and .def_184 .def_212)))
(let ((.def_214 (not .def_213)))
(let ((.def_216 (or .def_214 .def_215)))
(let ((.def_217 (or b.EVENT.1__AT0 .def_216)))
(let ((.def_233 (and .def_217 .def_232)))
(let ((.def_194 (= b.time__AT0 b.time__AT1)))
(let ((.def_206 (and .def_182 .def_194)))
(let ((.def_207 (and .def_170 .def_206)))
(let ((.def_208 (and .def_177 .def_207)))
(let ((.def_209 (or .def_47 .def_208)))
(let ((.def_197 (* (- 1.0) b.time__AT1)))
(let ((.def_200 (+ b.delta__AT0 .def_197)))
(let ((.def_201 (+ b.time__AT0 .def_200)))
(let ((.def_202 (= .def_201 0.0 )))
(let ((.def_203 (or .def_188 .def_202)))
(let ((.def_204 (or b.EVENT.1__AT0 .def_203)))
(let ((.def_195 (or .def_184 .def_194)))
(let ((.def_196 (or b.EVENT.1__AT0 .def_195)))
(let ((.def_205 (and .def_196 .def_204)))
(let ((.def_210 (and .def_205 .def_209)))
(let ((.def_190 (= .def_188 b.event_is_timed__AT1)))
(let ((.def_187 (= b.event_is_timed__AT0 .def_184)))
(let ((.def_191 (and .def_187 .def_190)))
(let ((.def_178 (and .def_170 .def_177)))
(let ((.def_121 (= b.y__AT0 0.0 )))
(let ((.def_85 (<= 0.0 b.speed_y__AT0)))
(let ((.def_86 (not .def_85)))
(let ((.def_122 (and .def_86 .def_121)))
(let ((.def_179 (or .def_122 .def_178)))
(let ((.def_145 (or b.counter.0__AT0 .def_144)))
(let ((.def_30 (not b.counter.0__AT0)))
(let ((.def_143 (or .def_30 b.counter.0__AT1)))
(let ((.def_146 (and .def_143 .def_145)))
(let ((.def_147 (and .def_132 .def_146)))
(let ((.def_148 (or b.counter.1__AT0 .def_147)))
(let ((.def_28 (not b.counter.1__AT0)))
(let ((.def_142 (or .def_28 b.counter.1__AT1)))
(let ((.def_149 (and .def_142 .def_148)))
(let ((.def_162 (and .def_139 .def_149)))
(let ((.def_163 (or b.counter.2__AT0 .def_162)))
(let ((.def_157 (and .def_30 .def_132)))
(let ((.def_158 (or b.counter.1__AT0 .def_157)))
(let ((.def_159 (and .def_142 .def_158)))
(let ((.def_160 (and b.counter.2__AT1 .def_159)))
(let ((.def_33 (not b.counter.2__AT0)))
(let ((.def_161 (or .def_33 .def_160)))
(let ((.def_164 (and .def_161 .def_163)))
(let ((.def_165 (and b.counter.3__AT1 .def_164)))
(let ((.def_166 (or b.counter.3__AT0 .def_165)))
(let ((.def_150 (and b.counter.2__AT1 .def_149)))
(let ((.def_151 (or b.counter.2__AT0 .def_150)))
(let ((.def_136 (or b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_134 (and .def_132 b.counter.0__AT1)))
(let ((.def_135 (or .def_28 .def_134)))
(let ((.def_137 (and .def_135 .def_136)))
(let ((.def_140 (and .def_137 .def_139)))
(let ((.def_141 (or .def_33 .def_140)))
(let ((.def_152 (and .def_141 .def_151)))
(let ((.def_155 (and .def_152 .def_154)))
(let ((.def_36 (not b.counter.3__AT0)))
(let ((.def_156 (or .def_36 .def_155)))
(let ((.def_167 (and .def_156 .def_166)))
(let ((.def_125 (* (- 1.0) b.speed_y__AT0)))
(let ((.def_128 (* .def_125 .def_127)))
(let ((.def_130 (= .def_128 b.speed_y__AT1)))
(let ((.def_168 (and .def_130 .def_167)))
(let ((.def_123 (not .def_122)))
(let ((.def_169 (or .def_123 .def_168)))
(let ((.def_180 (and .def_169 .def_179)))
(let ((.def_183 (and .def_180 .def_182)))
(let ((.def_185 (or .def_183 .def_184)))
(let ((.def_186 (or b.EVENT.1__AT0 .def_185)))
(let ((.def_192 (and .def_186 .def_191)))
(let ((.def_211 (and .def_192 .def_210)))
(let ((.def_234 (and .def_211 .def_233)))
(let ((.def_237 (and .def_234 .def_236)))
(let ((.def_241 (and .def_237 .def_240)))
(let ((.def_242 (and .def_47 .def_241)))
(let ((.def_259 (and .def_242 .def_258)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_34 (and .def_31 .def_33)))
(let ((.def_37 (and .def_34 .def_36)))
(let ((.def_260 (and .def_37 .def_259)))
(let ((.def_82 (+ .def_80 .def_78)))
(let ((.def_83 (<= 0.0 .def_82)))
(let ((.def_84 (not .def_83)))
(let ((.def_116 (or .def_84 .def_85)))
(let ((.def_99 (<= .def_82 0.0 )))
(let ((.def_97 (<= b.speed_y__AT0 0.0 )))
(let ((.def_98 (not .def_97)))
(let ((.def_115 (or .def_98 .def_99)))
(let ((.def_117 (and .def_115 .def_116)))
(let ((.def_112 (and .def_97 .def_99)))
(let ((.def_111 (and .def_83 .def_85)))
(let ((.def_113 (or .def_111 .def_112)))
(let ((.def_72 (+ .def_69 .def_71)))
(let ((.def_75 (+ .def_73 .def_72)))
(let ((.def_91 (<= .def_75 0.0 )))
(let ((.def_105 (not .def_91)))
(let ((.def_89 (<= b.y__AT0 0.0 )))
(let ((.def_106 (or .def_89 .def_105)))
(let ((.def_52 (<= 0.0 b.y__AT0)))
(let ((.def_103 (not .def_52)))
(let ((.def_76 (<= 0.0 .def_75)))
(let ((.def_104 (or .def_76 .def_103)))
(let ((.def_107 (and .def_104 .def_106)))
(let ((.def_100 (not .def_99)))
(let ((.def_101 (or .def_98 .def_100)))
(let ((.def_102 (not .def_101)))
(let ((.def_108 (or .def_102 .def_107)))
(let ((.def_93 (not .def_76)))
(let ((.def_94 (or .def_52 .def_93)))
(let ((.def_90 (not .def_89)))
(let ((.def_92 (or .def_90 .def_91)))
(let ((.def_95 (and .def_92 .def_94)))
(let ((.def_87 (or .def_84 .def_86)))
(let ((.def_88 (not .def_87)))
(let ((.def_96 (or .def_88 .def_95)))
(let ((.def_109 (and .def_96 .def_108)))
(let ((.def_77 (and .def_52 .def_76)))
(let ((.def_110 (and .def_77 .def_109)))
(let ((.def_114 (and .def_110 .def_113)))
(let ((.def_118 (and .def_114 .def_117)))
(let ((.def_119 (and .def_60 .def_118)))
(let ((.def_61 (and .def_52 .def_60)))
(let ((.def_50 (or .def_47 .def_49)))
(let ((.def_40 (or .def_28 .def_30)))
(let ((.def_44 (or b.counter.3__AT0 .def_40)))
(let ((.def_41 (or b.counter.2__AT0 .def_40)))
(let ((.def_39 (or .def_30 .def_33)))
(let ((.def_42 (and .def_39 .def_41)))
(let ((.def_43 (or .def_36 .def_42)))
(let ((.def_45 (and .def_43 .def_44)))
(let ((.def_51 (and .def_45 .def_50)))
(let ((.def_62 (and .def_51 .def_61)))
(let ((.def_25 (= b.speed_y__AT0 0.0 )))
(let ((.def_22 (= b.y__AT0 10.0 )))
(let ((.def_17 (= b.time__AT0 0.0 )))
(let ((.def_19 (and .def_17 b.event_is_timed__AT0)))
(let ((.def_23 (and .def_19 .def_22)))
(let ((.def_26 (and .def_23 .def_25)))
(let ((.def_38 (and .def_26 .def_37)))
(let ((.def_63 (and .def_38 .def_62)))
(let ((.def_7 (and .def_4 .def_6)))
(let ((.def_10 (and .def_7 .def_9)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_14 (not .def_13)))
(let ((.def_64 (and .def_14 .def_63)))
(let ((.def_120 (and .def_64 .def_119)))
(let ((.def_261 (and .def_120 .def_260)))
(let ((.def_314 (and .def_261 .def_313)))
(let ((.def_454 (and .def_314 .def_453)))
(let ((.def_507 (and .def_454 .def_506)))
(let ((.def_647 (and .def_507 .def_646)))
(let ((.def_700 (and .def_647 .def_699)))
(let ((.def_832 (and .def_700 .def_831)))
(let ((.def_885 (and .def_832 .def_884)))
.def_885)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
