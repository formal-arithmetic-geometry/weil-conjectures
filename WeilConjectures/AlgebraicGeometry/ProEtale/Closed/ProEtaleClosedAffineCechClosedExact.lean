/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

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

-- The affineness and covering hypotheses are not needed on the closed side.
set_option linter.unusedVariables false in
/-- The affine closed Cech presentation is exact after restriction to the closed fibre.

Source: Steps 1--3 of `lem-sp-proetale-closed-affine-cech-presentation-exact`.
(blueprint: lem-sp-proetale-closed-affine-cech-closed-exact).

Proof: it suffices that every map from i^*T_2 to an injective J that vanishes on
i^*T_1 factors through i^*T_3. By the adjunction i^* -| i_* these maps are maps
from T_j to i_*J, and by the corepresenting property they are Cech cochains of
the coefficient sheaf P^*i_*i^*i_*J. The closed counit i^*i_*J -> J is invertible,
and i_* and P^* preserve injectives, so that sheaf is injective. The Cech complex
of an injective presheaf is exact in positive degrees, which gives the factorization.
The affineness and covering hypotheses are not used. -/
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
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let i := b.closedComplement
  let adj := ProEtale.upperStarLowerStarAdjunction Λ i
  refine ShortComplex.exact_of_forall_injective _ fun J _ φ hφ ↦ ?_
  let φ' := adj.homEquiv _ _ φ
  have hφ' : T.complex.f ≫ φ' = 0 := by
    rw [← adj.homEquiv_naturality_left]
    exact (adj.homEquiv _ _).symm.injective (by simpa using hφ)
  -- The Čech complex of the closed push-pull of `i_* J` is exact in positive degrees.
  have hinj : Injective ((ProEtale.upperStar Λ P.hom).obj ((ProEtale.lowerStar Λ i).obj
      ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J)))) := by
    have : IsIso adj.counit := ProEtale.isIso_upperStarLowerStarAdjunction_counit Λ i
    have : Injective ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J)) :=
      Injective.of_iso (asIso (adj.counit.app J)).symm inferInstance
    have : (ProEtale.lowerStar Λ i).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
    have : Injective ((ProEtale.lowerStar Λ i).obj
        ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J))) :=
      Functor.PreservesInjectiveObjects.injective_obj (F := ProEtale.lowerStar Λ i) inferInstance
    exact ProEtale.injective_upperStar_obj_of_weaklyEtale Λ P.hom _
  have hex : ((closedCechCoefficientFunctor A b P V U).obj
      ((ProEtale.lowerStar Λ i).obj J)).ExactAt (q + 1) := by
    obtain ⟨G, hG⟩ : ∃ G, G = (ProEtale.upperStar Λ P.hom).obj ((ProEtale.lowerStar Λ i).obj
        ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J))) := ⟨_, rfl⟩
    rw [← hG] at hinj
    have : Injective G.obj := (sheafificationAdjunction _ _).map_injective _ hinj
    have h := Presheaf.exactAt_categoricalCech_of_injective G.obj U q
    subst hG
    exact h
  have hsc := (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)).1 hex
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1 hsc
    (T.middle _ φ') (by
      change ((closedCechCoefficientFunctor A b P V U).obj _).d (q + 1) (q + 2) _ = 0
      rw [← T.first_boundary, hφ', map_zero])
  refine ⟨(adj.homEquiv _ _).symm ((T.last _).symm c), ?_⟩
  change (ProEtale.upperStar Λ i).map T.complex.g ≫ _ = φ
  rw [← adj.homEquiv_naturality_left_symm]
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply (T.middle _).injective
  rw [T.last_boundary, AddEquiv.apply_symm_apply]
  exact hc

end AlgebraicGeometry.Scheme
