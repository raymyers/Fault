(declare-fun bathtub_drawn_water_level_0 () Real)
        (declare-fun bathtub_drawn_water_level_1 () Real)
        (declare-fun bathtub_drawn_water_level_2 () Real)
        (declare-fun bathtub_drawn_water_level_3 () Real)
        (declare-fun bathtub_drawn_water_level_4 () Real)
        (declare-fun bathtub_drawn_water_level_5 () Real)
        (declare-fun bathtub_drawn_water_level_6 () Real)
        (declare-fun bathtub_drawn_water_level_7 () Real)
        (declare-fun bathtub_drawn_water_level_8 () Real)
        (declare-fun bathtub_drawn_water_level_9 () Real)
        (declare-fun bathtub_drawn_water_level_10 () Real)
        (declare-fun bathtub_drawn_water_level_11 () Real)
        (declare-fun bathtub_drawn_water_level_12 () Real)
        (declare-fun bathtub_drawn_water_level_13 () Real)
        (declare-fun bathtub_drawn_water_level_14 () Real)
        (declare-fun bathtub_drawn_water_level_15 () Real)
        (assert (= bathtub_drawn_water_level_0 5.0))
        (assert (= bathtub_drawn_water_level_1 (- bathtub_drawn_water_level_0 20.0)))
        (assert (= bathtub_drawn_water_level_2 (+ bathtub_drawn_water_level_1 10.0)))
        (assert (= bathtub_drawn_water_level_3 (+ bathtub_drawn_water_level_0 10.0)))
        (assert (= bathtub_drawn_water_level_4 (- bathtub_drawn_water_level_3 20.0)))
        (assert (or (= bathtub_drawn_water_level_5 bathtub_drawn_water_level_2) (= bathtub_drawn_water_level_5 bathtub_drawn_water_level_4)))
        (assert (= bathtub_drawn_water_level_6 (- bathtub_drawn_water_level_5 20.0)))
        (assert (= bathtub_drawn_water_level_7 (+ bathtub_drawn_water_level_6 10.0)))
        (assert (= bathtub_drawn_water_level_8 (+ bathtub_drawn_water_level_5 10.0)))
        (assert (= bathtub_drawn_water_level_9 (- bathtub_drawn_water_level_8 20.0)))
        (assert (or (= bathtub_drawn_water_level_10 bathtub_drawn_water_level_7) (= bathtub_drawn_water_level_10 bathtub_drawn_water_level_9)))
        (assert (= bathtub_drawn_water_level_11 (- bathtub_drawn_water_level_10 20.0)))
        (assert (= bathtub_drawn_water_level_12 (+ bathtub_drawn_water_level_11 10.0)))
        (assert (= bathtub_drawn_water_level_13 (+ bathtub_drawn_water_level_10 10.0)))
        (assert (= bathtub_drawn_water_level_14 (- bathtub_drawn_water_level_13 20.0)))
        (assert (or (= bathtub_drawn_water_level_15 bathtub_drawn_water_level_12) (= bathtub_drawn_water_level_15 bathtub_drawn_water_level_14)))
        (check-sat)
        (get-model)
