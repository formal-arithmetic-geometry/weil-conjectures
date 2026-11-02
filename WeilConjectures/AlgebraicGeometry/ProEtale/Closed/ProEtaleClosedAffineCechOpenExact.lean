/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective

/-! # Exactness of the affine closed Cech presentation on the complementary open

Source: the matching-relations calculation in Steps 1--3 of
`lem-sp-proetale-closed-affine-cech-presentation-exact`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

-- The affineness and covering hypotheses are the geometric input of the remaining step.
set_option linter.unusedVariables false in
/-- Positive Čech exactness of the closed push-pull of an ambient injective, for a finite
affine pro-étale cover of an affine object, after pro-étale localization.

This is the geometric core of the affine closed Čech calculation: for an injective `I`
on `B`, the Čech complex of `P^* i_* i^* I` (with `i = b.closedComplement`) on the cover
`U` of `V` is exact in positive degrees. Equivalently, `i^* I` has vanishing higher Čech
cohomology on finite affine covers of the affine closed fibre `V ×_B Z`.

Source: the affine matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.
(blueprint: lem-sp-proetale-closed-injective-affine-cech).

Remaining input: this is not proved here. It is equivalent, through the corepresenting
short complexes of `exists_closedCech_corepresentingShortComplex`, to the exactness of
`closedAffineCech_open_restriction_exact` (the closed-fibre half being formal), and it
implies vanishing of the higher pro-étale cohomology of `i^* I` on affine objects of the
closed fibre.

Status of the remaining input. Taking `B` affine, `P = 𝟙`, `V = T^h` (the henselization of
an affine `T` over the closed fibre) and the single cover `W^h → T^h` for a weakly
contractible affine cover `W → T`, the statement is equivalent to
`H^q(T, i^* I) = 0` for `q ≥ 1`, all affine `T` and all injective `I`. Here `H^q` is derived
pro-étale cohomology. It is the pro-étale form of Gabber's affine analogue of proper base
change, but for arbitrary injective sheaves, which need not come from the étale site. With
`L` the left adjoint of `i^*` on module sheaves, this is `L_q (Λ[T]) = 0`. The stalk of
`L_q (Λ[T])` at a geometric point `x` of the open complement is the `q`-th homology of the
simplicial set of `x`-points of `v W_•`. Here `W_•` is a hypercover of `T` by weakly
contractible affines and `v` is `closedSiteLift`, which gives the henselization. The
henselization `v` preserves covers but not fibre products: `v (T₁ ×_T T₂)` is the
henselization of `v T₁ ×_{v T} v T₂`, not the product itself. So this simplicial set is not a
hypercover, and its acyclicity is a genuine geometric statement. It is not available in this
library and may be false when the closed fibre has dimension at least `2`. The following
routes fail: `i^*` preserving injectives, the evaluation formula `(i^* F)(T) = F(v T)` for
affine `T` that are not weakly contractible, and Čech arguments on the cover `{v T_a}`. -/
theorem exactAt_closedCechCoefficientFunctor_obj_of_injective
    (A : Type u) [CommRing A] [Finite A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) (hV : IsAffine V.left)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology P.left V)
    (q : ℕ) (I : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [Injective I] :
    ((closedCechCoefficientFunctor A b P V U).obj I).ExactAt (q + 1) := by
  sorry

/-- The affine closed Cech presentation is exact after restriction to the complementary open.

Source: Steps 1--3 of `lem-sp-proetale-closed-affine-cech-presentation-exact`.
(blueprint: lem-sp-proetale-closed-affine-cech-open-exact).

Proof: it suffices that every map from b^*T_2 to an injective N that vanishes on
b^*T_1 factors through b^*T_3. By the adjunction b^* ⊣ b_* these maps are maps
from T_j to b_*N, and by the corepresenting property they are Cech cochains of
the coefficient sheaf P^*i_*i^*b_*N. Since b^* is exact, b_* preserves injectives,
so `exactAt_closedCechCoefficientFunctor_obj_of_injective` gives exactness of that
Čech complex in degree q+1, which is the required factorization. -/
theorem closedAffineCech_open_restriction_exact
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
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) b)).Exact := by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let adj := ProEtale.upperStarLowerStarAdjunction Λ b
  refine ShortComplex.exact_of_forall_injective _ fun J _ φ hφ ↦ ?_
  let φ' := adj.homEquiv _ _ φ
  have hφ' : T.complex.f ≫ φ' = 0 := by
    rw [← adj.homEquiv_naturality_left]
    exact (adj.homEquiv _ _).symm.injective (by simpa using hφ)
  have : (ProEtale.lowerStar Λ b).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have : Injective ((ProEtale.lowerStar Λ b).obj J) :=
    Functor.PreservesInjectiveObjects.injective_obj (F := ProEtale.lowerStar Λ b) inferInstance
  have hex := exactAt_closedCechCoefficientFunctor_obj_of_injective A b P V hV U hU hcover q
    ((ProEtale.lowerStar Λ b).obj J)
  have hsc := (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)).1 hex
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1 hsc
    (T.middle _ φ') (by
      change ((closedCechCoefficientFunctor A b P V U).obj _).d (q + 1) (q + 2) _ = 0
      rw [← T.first_boundary, hφ', map_zero])
  refine ⟨(adj.homEquiv _ _).symm ((T.last _).symm c), ?_⟩
  change (ProEtale.upperStar Λ b).map T.complex.g ≫ _ = φ
  rw [← adj.homEquiv_naturality_left_symm]
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply (T.middle _).injective
  rw [T.last_boundary, AddEquiv.apply_symm_apply]
  exact hc

end AlgebraicGeometry.Scheme
