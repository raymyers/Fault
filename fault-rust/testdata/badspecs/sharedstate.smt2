(set-logic QF_NRA)
(declare-fun sharedstate_shared_v_0 () Real)
(declare-fun sharedstate_shared_v_1 () Real)
(declare-fun sharedstate_shared_v_2 () Real)
(declare-fun sharedstate_shared_v_3 () Real)
(declare-fun @__run_0 () Bool)
(declare-fun sharedstate_shared_v_4 () Real)
(declare-fun sharedstate_shared_v_5 () Real)
(declare-fun sharedstate_shared_v_6 () Real)
(declare-fun @__run_1 () Bool)
(declare-fun sharedstate_shared_v_7 () Real)
(declare-fun sharedstate_shared_v_8 () Real)
(declare-fun sharedstate_shared_v_9 () Real)
(declare-fun sharedstate_shared_v_10 () Real)
(declare-fun sharedstate_shared_v_11 () Real)
(declare-fun sharedstate_shared_v_12 () Real)
(declare-fun sharedstate_shared_v_13 () Real)
(declare-fun sharedstate_shared_v_14 () Real)
(declare-fun sharedstate_shared_v_15 () Real)
(declare-fun sharedstate_shared_v_16 () Real)
(declare-fun sharedstate_shared_v_17 () Real)
(declare-fun sharedstate_shared_v_18 () Real)
(declare-fun sharedstate_shared_v_19 () Real)
(declare-fun sharedstate_shared_v_20 () Real)
(declare-fun sharedstate_shared_v_21 () Real)
(declare-fun sharedstate_shared_v_22 () Real)
(declare-fun sharedstate_shared_v_23 () Real)
(declare-fun sharedstate_shared_v_24 () Real)
(declare-fun sharedstate_shared_v_25 () Real)
(declare-fun sharedstate_shared_v_26 () Real)
(declare-fun sharedstate_shared_v_27 () Real)
(declare-fun sharedstate_shared_v_28 () Real)
(declare-fun sharedstate_shared_v_29 () Real)
(declare-fun sharedstate_shared_v_30 () Real)
(assert (= sharedstate_shared_v_0 10.0))

(assert (= sharedstate_shared_v_1 (+ sharedstate_shared_v_0 (+ sharedstate_shared_v_0 1.0))))


(assert (= sharedstate_shared_v_2 (+ sharedstate_shared_v_1 (- sharedstate_shared_v_1 1.0))))

(assert (= @__run_0 (= sharedstate_shared_v_3 sharedstate_shared_v_2)))

(assert (= sharedstate_shared_v_4 (+ sharedstate_shared_v_3 (- sharedstate_shared_v_0 1.0))))


(assert (= sharedstate_shared_v_5 (+ sharedstate_shared_v_4 (+ sharedstate_shared_v_4 1.0))))

(assert (= @__run_1 (and (= sharedstate_shared_v_6 sharedstate_shared_v_2)
(= sharedstate_shared_v_6 sharedstate_shared_v_5))))
(assert (or (and @__run_0
(not @__run_1))
(and (not @__run_0)
@__run_1)))

(assert (= sharedstate_shared_v_7 (+ sharedstate_shared_v_6 (+ sharedstate_shared_v_6 1.0))))


(assert (= sharedstate_shared_v_8 (+ sharedstate_shared_v_7 (- sharedstate_shared_v_7 1.0))))

(assert (= @__run_0 (= sharedstate_shared_v_9 sharedstate_shared_v_8)))

(assert (= sharedstate_shared_v_10 (+ sharedstate_shared_v_9 (- sharedstate_shared_v_6 1.0))))


(assert (= sharedstate_shared_v_11 (+ sharedstate_shared_v_10 (+ sharedstate_shared_v_10 1.0))))

(assert (= @__run_1 (and (= sharedstate_shared_v_12 sharedstate_shared_v_8)
(= sharedstate_shared_v_12 sharedstate_shared_v_11))))
(assert (or (and @__run_0
(not @__run_1))
(and (not @__run_0)
@__run_1)))

(assert (= sharedstate_shared_v_13 (+ sharedstate_shared_v_12 (+ sharedstate_shared_v_12 1.0))))


(assert (= sharedstate_shared_v_14 (+ sharedstate_shared_v_13 (- sharedstate_shared_v_13 1.0))))

(assert (= @__run_0 (= sharedstate_shared_v_15 sharedstate_shared_v_14)))

(assert (= sharedstate_shared_v_16 (+ sharedstate_shared_v_15 (- sharedstate_shared_v_12 1.0))))


(assert (= sharedstate_shared_v_17 (+ sharedstate_shared_v_16 (+ sharedstate_shared_v_16 1.0))))

(assert (= @__run_1 (and (= sharedstate_shared_v_18 sharedstate_shared_v_14)
(= sharedstate_shared_v_18 sharedstate_shared_v_17))))
(assert (or (and @__run_0
(not @__run_1))
(and (not @__run_0)
@__run_1)))

(assert (= sharedstate_shared_v_19 (+ sharedstate_shared_v_18 (+ sharedstate_shared_v_18 1.0))))


(assert (= sharedstate_shared_v_20 (+ sharedstate_shared_v_19 (- sharedstate_shared_v_19 1.0))))

(assert (= @__run_0 (= sharedstate_shared_v_21 sharedstate_shared_v_20)))

(assert (= sharedstate_shared_v_22 (+ sharedstate_shared_v_21 (- sharedstate_shared_v_18 1.0))))


(assert (= sharedstate_shared_v_23 (+ sharedstate_shared_v_22 (+ sharedstate_shared_v_22 1.0))))

(assert (= @__run_1 (and (= sharedstate_shared_v_24 sharedstate_shared_v_20)
(= sharedstate_shared_v_24 sharedstate_shared_v_23))))
(assert (or (and @__run_0
(not @__run_1))
(and (not @__run_0)
@__run_1)))

(assert (= sharedstate_shared_v_25 (+ sharedstate_shared_v_24 (+ sharedstate_shared_v_24 1.0))))


(assert (= sharedstate_shared_v_26 (+ sharedstate_shared_v_25 (- sharedstate_shared_v_25 1.0))))

(assert (= @__run_0 (= sharedstate_shared_v_27 sharedstate_shared_v_26)))

(assert (= sharedstate_shared_v_28 (+ sharedstate_shared_v_27 (- sharedstate_shared_v_24 1.0))))


(assert (= sharedstate_shared_v_29 (+ sharedstate_shared_v_28 (+ sharedstate_shared_v_28 1.0))))

(assert (= @__run_1 (and (= sharedstate_shared_v_30 sharedstate_shared_v_26)
(= sharedstate_shared_v_30 sharedstate_shared_v_29))))
(assert (or (and @__run_0
(not @__run_1))
(and (not @__run_0)
@__run_1)))
