(set-logic QF_NRA)
(declare-fun asserts_test_target_value_0 () Real)
(declare-fun asserts_test_target_value_1 () Real)
(declare-fun asserts_test_target_value_2 () Real)
(declare-fun asserts_test_target_value_3 () Real)
(declare-fun asserts_test_target_value_4 () Real)
(assert (= asserts_test_target_value_0 40.0))

(assert (= asserts_test_target_value_1 (- asserts_test_target_value_0 (/ asserts_test_target_value_0 2.0))))


(assert (= asserts_test_target_value_2 (- asserts_test_target_value_1 (/ asserts_test_target_value_1 2.0))))


(assert (= asserts_test_target_value_3 (- asserts_test_target_value_2 (/ asserts_test_target_value_2 2.0))))


(assert (= asserts_test_target_value_4 (- asserts_test_target_value_3 (/ asserts_test_target_value_3 2.0))))

(assert (or (not (= asserts_test_target_value_0 40)) (not (= asserts_test_target_value_1 40)) (not (= asserts_test_target_value_2 40)) (not (= asserts_test_target_value_3 40)) (not (= asserts_test_target_value_4 40))))
(assert (and (> asserts_test_target_value_0 2) (> asserts_test_target_value_1 2) (> asserts_test_target_value_2 2) (> asserts_test_target_value_3 2) (> asserts_test_target_value_4 2)))
