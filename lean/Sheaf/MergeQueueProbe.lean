module

/-! Merge-queue probe (2026-10-19): a deliberately failing module that nothing imports. The global build is
expected to be red in this module only, and the lander to drop this change from the candidate. -/

public theorem mergeQueueProbe : (1 : Nat) = 2 := by rfl
