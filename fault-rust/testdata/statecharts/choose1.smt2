(set-logic QF_NRA)
(declare-fun choose1_a_choice_0 () Bool)
(declare-fun choose1_a_option1_0 () Bool)
(declare-fun choose1_a_option2_0 () Bool)
(declare-fun choose1_a_choice_1 () Bool)
(declare-fun choose1_a_option1_1 () Bool)
(declare-fun choose1_a_option2_1 () Bool)
(declare-fun choose1_a_option1_2 () Bool)
(declare-fun choose1_a_option2_2 () Bool)
(declare-fun choose1_a_option2_3 () Bool)
(declare-fun choose1_a_option1_3 () Bool)
(declare-fun choose1_a_choice__state-%8_0 () Bool)
(declare-fun choose1_a_choice__state-%8_1 () Bool)
(declare-fun choose1_a_option1_4 () Bool)
(declare-fun choose1_a_option2_4 () Bool)
(declare-fun block3true_0 () Bool)
(declare-fun block3false_0 () Bool)
(declare-fun choose1_a_option1_5 () Bool)
(declare-fun choose1_a_option1_6 () Bool)
(declare-fun block7true_0 () Bool)
(declare-fun block7false_0 () Bool)
(declare-fun choose1_a_option2_5 () Bool)
(declare-fun choose1_a_option2_6 () Bool)
(declare-fun block11true_0 () Bool)
(declare-fun block11false_0 () Bool)
(assert (= choose1_a_choice_0 false))
(assert (= choose1_a_option1_0 false))
(assert (= choose1_a_option2_0 false))
(assert (= choose1_a_choice_1 true))

(assert (=> choose1_a_choice__state-%8_0 (and (= choose1_a_option1_1 true) (not (= choose1_a_option2_1 true)))))
(assert (=> choose1_a_choice__state-%8_1 (and (not (= choose1_a_option1_2 true)) (= choose1_a_option2_2 true))))
(assert (= choose1_a_choice__state-%8_0 (and (= choose1_a_option2_3 choose1_a_option2_1)
(= choose1_a_option1_3 choose1_a_option1_1))))
(assert (= choose1_a_choice__state-%8_1 (and (= choose1_a_option1_3 choose1_a_option1_2)
(= choose1_a_option2_3 choose1_a_option2_2))))
(assert (or (and choose1_a_choice__state-%8_0
(not choose1_a_choice__state-%8_1))
(and (not choose1_a_choice__state-%8_0)
choose1_a_choice__state-%8_1)))

(assert (ite (= choose1_a_choice_1 true) (and (= block3true_0 true) (= block3false_0 false) (and (= choose1_a_option1_4 choose1_a_option1_3) (= choose1_a_option2_4 choose1_a_option2_3))) (and (= block3true_0 false) (= block3false_0 true) (and (= choose1_a_option1_4 choose1_a_option1_0)
(= choose1_a_option2_4 choose1_a_option2_0)))))
(assert (or (and block3true_0
(not block3false_0))
(and (not block3true_0)
block3false_0)))


(assert (= choose1_a_option1_5 true))

(assert (ite (= choose1_a_option1_4 true) (and (= block7true_0 true) (= block7false_0 false) (= choose1_a_option1_6 choose1_a_option1_5)) (and (= block7true_0 false) (= block7false_0 true) (= choose1_a_option1_6 choose1_a_option1_4))))
(assert (or (and block7true_0
(not block7false_0))
(and (not block7true_0)
block7false_0)))


(assert (= choose1_a_option2_5 true))

(assert (ite (= choose1_a_option2_4 true) (and (= block11true_0 true) (= block11false_0 false) (= choose1_a_option2_6 choose1_a_option2_5)) (and (= block11true_0 false) (= block11false_0 true) (= choose1_a_option2_6 choose1_a_option2_4))))
(assert (or (and block11true_0
(not block11false_0))
(and (not block11true_0)
block11false_0)))

