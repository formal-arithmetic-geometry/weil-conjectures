/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects

/-! # Realization of a finite-coefficient exceptional adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- A single finite coefficient ring has a constructible exceptional adjunction with
an ordinary-etale realization that retains the specified compact-support counit.
Source: blueprint latest, sec-smooth-purity, sk-lem-sp-reduction-exceptional.proof.md,
Steps 3--4 (blueprint: lem-sp-reduction-exceptional-realization).

Proof: the field hypothesis makes X, Y and Z Noetherian. Realization identifies the
intrinsic Dctf property with the fixed-module bounded constructible finite-Tor property.
The finite-ring etale/pro-etale comparison equivalence supplies a functorial etale
origin and its natural comparison. Choose the ordinary exceptional right adjoint for
this fixed compactification. Its values on those origins remain bounded constructible
of finite Tor amplitude by exceptional preservation. Apply compact-support comparison,
comparison full faithfulness, and the ordinary adjunction to obtain the natural Hom
bijection on the intrinsic full subcategories. Its inverse at the identity is the
counit. This constructs the intrinsic right functor, adjunction, and output comparison.
The defining Hom bijection gives precisely reductionRealizationCounitEquation;
there is no independent choice of a counit or of an output isomorphism. -/
theorem reductionExceptionalRealization_exists
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (_hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (_hf : j ≫ p = f)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj)) :
    ∃ (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
      (adj : reductionCtfCompactSupport A j p hF ⊣ G),
      Nonempty (ReductionExceptionalRealization A j p hF G adj) := by
  sorry

end AlgebraicGeometry.ProEtale
