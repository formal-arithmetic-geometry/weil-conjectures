/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation

/-! # Exactness of the affine closed Cech presentation on the closed fibre

Source: the matching-relations calculation in Steps 1--3 of
`lem-sp-proetale-closed-affine-cech-presentation-exact`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The affine closed Cech presentation is exact after restriction to the closed fibre.

Source: Steps 1--3 of `lem-sp-proetale-closed-affine-cech-presentation-exact`.
(blueprint: lem-sp-proetale-closed-affine-cech-closed-exact).

Proof: Apply the closed restriction to the representing short complex. For a
closed-side coefficient sheaf N, the inverse/direct-image adjunction identifies
Hom(i^* T_j,N) with Hom(T_j,i_*N). The invertible closed counit identifies
i^*i_*N with N. Weakly etale base change for P and V then identifies these
Hom groups, naturally with both boundary arrows, with Cech cochains on the
base-changed covering family on the closed fibre. Its free module resolution
is exact in positive degrees: on a generator the insertion of its first lift
contracts the augmented nerve. Module sheafification is exact. Yoneda identifies
the three restricted representing objects and the arrows with the three terms
of that sheafified free resolution, so exactness transports. Empty lift sets
contribute zero free modules; the argument includes the zero ring and empty
closed fibre.
-/
theorem closedAffineCech_closed_restriction_exact
    (A : Type u) [CommRing A] [Finite A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) (hV : IsAffine V.left)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology P.left V)
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A b P V U) q) :
    (T.complex.map (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) b.closedComplement)).Exact := by
  sorry

end AlgebraicGeometry.Scheme
