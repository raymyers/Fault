(set-logic QF_NRA)
(declare-fun simpleA_l_vault_value_0 () Real)
(declare-fun simpleA_l_vault_value_1 () Real)
(declare-fun simpleA_l_vault_value_2 () Real)
(declare-fun block3true_1 () Bool)
(declare-fun block3false_1 () Bool)
(assert (= simpleA_l_vault_value_0 30.0))

(assert (= simpleA_l_vault_value_1 (+ simpleA_l_vault_value_0 (- simpleA_l_vault_value_0 2.0))))

(assert (ite (> simpleA_l_vault_value_0 4.0) (and (= block3true_1 true) (= block3false_1 false) (= simpleA_l_vault_value_2 simpleA_l_vault_value_1)) (and (= block3true_1 false) (= block3false_1 true) (= simpleA_l_vault_value_2 simpleA_l_vault_value_0))))
(assert (or (and block3true_1
(not block3false_1))
(and (not block3true_1)
block3false_1)))

