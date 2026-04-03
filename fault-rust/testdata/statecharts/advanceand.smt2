(set-logic QF_NRA)
(declare-fun adand_a_choice_0 () Bool)
(declare-fun adand_a_option1_0 () Bool)
(declare-fun adand_a_option2_0 () Bool)
(declare-fun adand_a_option3_0 () Bool)
(declare-fun adand_a_choice_1 () Bool)
(declare-fun adand_a_option1_1 () Bool)
(declare-fun adand_a_option2_1 () Bool)
(declare-fun adand_a_option3_1 () Bool)
(declare-fun adand_a_option1_2 () Bool)
(declare-fun adand_a_option2_2 () Bool)
(declare-fun adand_a_option3_2 () Bool)
(declare-fun block3true_0 () Bool)
(declare-fun block3false_0 () Bool)
(declare-fun adand_a_option1_3 () Bool)
(declare-fun adand_a_option1_4 () Bool)
(declare-fun block7true_0 () Bool)
(declare-fun block7false_0 () Bool)
(declare-fun adand_a_option2_3 () Bool)
(declare-fun adand_a_option2_4 () Bool)
(declare-fun block11true_0 () Bool)
(declare-fun block11false_0 () Bool)
(declare-fun adand_a_option3_3 () Bool)
(declare-fun adand_a_option3_4 () Bool)
(declare-fun block14true_0 () Bool)
(declare-fun block14false_0 () Bool)
(assert (= adand_a_choice_0 false))
(assert (= adand_a_option1_0 false))
(assert (= adand_a_option2_0 false))
(assert (= adand_a_option3_0 false))
(assert (= adand_a_choice_1 true))

(assert (and (= adand_a_option1_1 true) (= adand_a_option2_1 true) (= adand_a_option3_1 true)))

(assert (ite (= adand_a_choice_1 true) (and (= block3true_0 true) (= block3false_0 false) (and (= adand_a_option1_2 adand_a_option1_1) (= adand_a_option2_2 adand_a_option2_1) (= adand_a_option3_2 adand_a_option3_1))) (and (= block3true_0 false) (= block3false_0 true) (and (= adand_a_option1_2 adand_a_option1_0)
(= adand_a_option2_2 adand_a_option2_0)
(= adand_a_option3_2 adand_a_option3_0)))))
(assert (or (and block3true_0
(not block3false_0))
(and (not block3true_0)
block3false_0)))


(assert (= adand_a_option1_3 true))

(assert (ite (= adand_a_option1_2 true) (and (= block7true_0 true) (= block7false_0 false) (= adand_a_option1_4 adand_a_option1_3)) (and (= block7true_0 false) (= block7false_0 true) (= adand_a_option1_4 adand_a_option1_2))))
(assert (or (and block7true_0
(not block7false_0))
(and (not block7true_0)
block7false_0)))


(assert (= adand_a_option2_3 true))

(assert (ite (= adand_a_option2_2 true) (and (= block11true_0 true) (= block11false_0 false) (= adand_a_option2_4 adand_a_option2_3)) (and (= block11true_0 false) (= block11false_0 true) (= adand_a_option2_4 adand_a_option2_2))))
(assert (or (and block11true_0
(not block11false_0))
(and (not block11true_0)
block11false_0)))


(assert (= adand_a_option3_3 true))

(assert (ite (= adand_a_option3_2 true) (and (= block14true_0 true) (= block14false_0 false) (= adand_a_option3_4 adand_a_option3_3)) (and (= block14true_0 false) (= block14false_0 true) (= adand_a_option3_4 adand_a_option3_2))))
(assert (or (and block14true_0
(not block14false_0))
(and (not block14true_0)
block14false_0)))

