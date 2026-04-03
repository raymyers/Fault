(set-logic QF_NRA)
(declare-fun ador_a_choice_0 () Bool)
(declare-fun ador_a_option1_0 () Bool)
(declare-fun ador_a_option2_0 () Bool)
(declare-fun ador_a_choice_1 () Bool)
(declare-fun ador_a_option1_1 () Bool)
(declare-fun ador_a_option2_1 () Bool)
(declare-fun ador_a_option1_2 () Bool)
(declare-fun ador_a_option2_2 () Bool)
(declare-fun ador_a_choice__state-%8_0 () Bool)
(declare-fun ador_a_choice__state-%8_1 () Bool)
(declare-fun ador_a_option1_3 () Bool)
(declare-fun ador_a_option2_3 () Bool)
(declare-fun block3true_0 () Bool)
(declare-fun block3false_0 () Bool)
(declare-fun ador_a_option1_4 () Bool)
(declare-fun ador_a_option1_5 () Bool)
(declare-fun block7true_0 () Bool)
(declare-fun block7false_0 () Bool)
(declare-fun ador_a_option2_4 () Bool)
(declare-fun ador_a_option2_5 () Bool)
(declare-fun block11true_0 () Bool)
(declare-fun block11false_0 () Bool)
(assert (= ador_a_choice_0 false))
(assert (= ador_a_option1_0 false))
(assert (= ador_a_option2_0 false))
(assert (= ador_a_choice_1 true))

(assert (=> ador_a_choice__state-%8_0 (= ador_a_option1_1 true)))
(assert (=> ador_a_choice__state-%8_1 (= ador_a_option2_1 true)))
(assert (= ador_a_choice__state-%8_0 (and (= ador_a_option1_2 ador_a_option1_1)
(= ador_a_option2_2 ador_a_option2_0))))
(assert (= ador_a_choice__state-%8_1 (and (= ador_a_option2_2 ador_a_option2_1)
(= ador_a_option1_2 ador_a_option1_0))))
(assert (or (and ador_a_choice__state-%8_0
(not ador_a_choice__state-%8_1))
(and (not ador_a_choice__state-%8_0)
ador_a_choice__state-%8_1)))

(assert (ite (= ador_a_choice_1 true) (and (= block3true_0 true) (= block3false_0 false) (and (= ador_a_option1_3 ador_a_option1_2) (= ador_a_option2_3 ador_a_option2_2))) (and (= block3true_0 false) (= block3false_0 true) (and (= ador_a_option1_3 ador_a_option1_0)
(= ador_a_option2_3 ador_a_option2_0)))))
(assert (or (and block3true_0
(not block3false_0))
(and (not block3true_0)
block3false_0)))


(assert (= ador_a_option1_4 true))

(assert (ite (= ador_a_option1_3 true) (and (= block7true_0 true) (= block7false_0 false) (= ador_a_option1_5 ador_a_option1_4)) (and (= block7true_0 false) (= block7false_0 true) (= ador_a_option1_5 ador_a_option1_3))))
(assert (or (and block7true_0
(not block7false_0))
(and (not block7true_0)
block7false_0)))


(assert (= ador_a_option2_4 true))

(assert (ite (= ador_a_option2_3 true) (and (= block11true_0 true) (= block11false_0 false) (= ador_a_option2_5 ador_a_option2_4)) (and (= block11true_0 false) (= block11false_0 true) (= ador_a_option2_5 ador_a_option2_3))))
(assert (or (and block11true_0
(not block11false_0))
(and (not block11true_0)
block11false_0)))

