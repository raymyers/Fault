(set-logic QF_NRA)
(declare-fun condwe_t_base_value_2 () Real)
(declare-fun condwe_t_base_value_4 () Real)
(declare-fun condwe_t_base_cond_0 () Real)
(declare-fun condwe_t_base_value_0 () Real)
(declare-fun condwe_t_base_value_1 () Real)
(declare-fun condwe_t_base_value_3 () Real)
(assert (= condwe_t_base_cond_0 1.0))
(assert (= condwe_t_base_value_0 10.0))
(assert (= condwe_t_base_value_1 (- condwe_t_base_value_0 30.0)))
(assert (ite (> condwe_t_base_cond_0 0.0) (= condwe_t_base_value_2 condwe_t_base_value_1) (= condwe_t_base_value_2 condwe_t_base_value_0)))
(assert (= condwe_t_base_value_3 (+ condwe_t_base_value_2 20.0)))
(assert (ite (and (> condwe_t_base_cond_0 0.0) (< condwe_t_base_cond_0 4.0)) (= condwe_t_base_value_4 condwe_t_base_value_3) (= condwe_t_base_value_4 condwe_t_base_value_2)))