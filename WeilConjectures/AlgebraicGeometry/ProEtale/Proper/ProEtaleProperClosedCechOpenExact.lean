/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Exactness of the proper closed Čech presentation on the complementary open

Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Over the proper scheme `P = B ×_D W` itself, the closed Čech presentation of a finite
cover with affine Čech intersections is exact after restriction to the open part
`B ×_D E`.

Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`
(the analogue of `closedAffineCech_open_restriction_exact` for the non-affine object `P`).

Remarks: by the corepresenting property and `b^* ⊣ b_*`, this is equivalent to positive
Čech exactness of `P^* z_* z^* b_* J` on the cover `U` for every injective `J` on the open
`B ×_D E`, i.e. to the case `I = b_* J` of `exactAt_proper_closed_injective_cech`. Since all
Čech intersections are affine, this amounts to the vanishing of the positive cohomology of
`z^* b_* J` on the closed fibre `P_Z`, an instance of proper base change for the henselian
pair `(Γ(W), J_W)`; this is why properness, `hW` and `hspecializes` are needed.

Proof plan: as for `closedAffineCech_open_restriction_exact`, use the retained lift
presentation of the three degrees and contract the lifted nerve locally by insertion of a
chosen local lift. Properness and `hspecializes` show that every point of `P` specializes
into the closed fibre, so henselian lifts of a cover of the closed fibre cover `P`. -/
theorem properClosedCech_open_restriction_exact
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z))
    {n : ℕ} (U : Fin n → Over (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)))
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology ((proEtaleBaseChange p).obj W).left
        (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)))
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A (pullback.fst p i) ((proEtaleBaseChange p).obj W)
        (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)) U) q) :
    (T.complex.map (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i))).Exact := by
  sorry

end AlgebraicGeometry.Scheme
