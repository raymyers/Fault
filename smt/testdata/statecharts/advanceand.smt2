(set-logic QF_NRA)
(declare-fun adand_a_option1_1 () Bool)
(declare-fun adand_a_choice_2 () Bool)
(declare-fun adand_a_option2_1 () Bool)
(declare-fun adand_a_choice_3 () Bool)
(declare-fun adand_a_option3_1 () Bool)
(declare-fun adand_a_choice_4 () Bool)
(declare-fun adand_a_option1_2 () Bool)
(declare-fun adand_a_choice_5 () Bool)
(declare-fun adand_a_option2_2 () Bool)
(declare-fun adand_a_option3_2 () Bool)
(declare-fun adand_a_choice_0 () Bool)
(declare-fun adand_a_option1_0 () Bool)
(declare-fun adand_a_option2_0 () Bool)
(declare-fun adand_a_option3_0 () Bool)
(declare-fun adand_a_choice_1 () Bool)(assert (= adand_a_choice_0 false))
(assert (= adand_a_option1_0 false))
(assert (= adand_a_option2_0 false))
(assert (= adand_a_option3_0 false))
(assert (= adand_a_choice_1 true))
(assert (and (= adand_a_option1_1 true)(= adand_a_choice_2 false)(= adand_a_option2_1 true)(= adand_a_choice_3 false)(= adand_a_option3_1 true)(= adand_a_choice_4 false)))
(assert (ite (= adand_a_choice_1 true) (and (= adand_a_option1_2 adand_a_option1_1) (= adand_a_choice_5 adand_a_choice_4) (= adand_a_option2_2 adand_a_option2_1) (= adand_a_option3_2 adand_a_option3_1)) (and (= adand_a_option1_2 adand_a_option1_0) (= adand_a_choice_5 adand_a_choice_1) (= adand_a_option2_2 adand_a_option2_0) (= adand_a_option3_2 adand_a_option3_0))))