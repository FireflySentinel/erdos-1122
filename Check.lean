import Erdos1122

/-!
The expected axiom sets are checked by Lean itself. Changing a dependency to
an admitted proof or adding an unlisted axiom makes this file fail to compile.
-/

/-- info: 'Erdos1122.clip_finite_tail_error_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.clip_finite_tail_error_sq

/-- info: 'Erdos1122.weighted_clipped_square_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.weighted_clipped_square_bounds

/-- info: 'Erdos1122.quadratic_projection_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.quadratic_projection_identity

/-- info: 'Erdos1122.quadratic_projection_is_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.quadratic_projection_is_minimum

/-- info: 'Erdos1122.quadratic_projection_lower_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.quadratic_projection_lower_of_bounds

/-- info: 'Erdos1122.weighted_moment_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.weighted_moment_interpolation

/-- info: 'Erdos1122.window_average_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.window_average_contraction

/-- info: 'Erdos1122.average_comparison_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.average_comparison_square

/-- info: 'Erdos1122.total_variation_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.total_variation_identity

/-- info: 'Erdos1122.total_variation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.total_variation_le

/-- info: 'Erdos1122.sum_square_window_discrepancy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.sum_square_window_discrepancy_le
