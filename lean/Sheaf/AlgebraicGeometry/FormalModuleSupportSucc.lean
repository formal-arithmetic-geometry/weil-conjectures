module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! Consecutive levels of a coherent formal module have equal support.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 30.26.11 (Tag 0CYV).
(blueprint: lem-weil-pbc-formal-system-support-succ)
-/

@[expose] public section

universe u

open Opposite

namespace AlgebraicGeometry

/-- Consecutive support equality, reducing the constant-support theorem to induction.

The proof identifies the stalk at level `n` with the quotient of the stalk at level
`n + 1` by the `n`th ideal power, and uses the annihilation condition to show that
this quotient vanishes exactly when the original stalk vanishes. This is the
consecutive-level step in the proof of the constant-support theorem.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 30.26.11 (Tag 0CYV),
first sentence of the proof of (1).
(blueprint: lem-weil-pbc-formal-system-support-succ). -/
theorem formalModule_support_succ {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (n : ℕ) :
    {x : X | ¬ Subsingleton ((F.obj.obj (op (n + 1))).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk x)} := by
  sorry

end AlgebraicGeometry
