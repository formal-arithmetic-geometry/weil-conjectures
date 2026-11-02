/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedAffineCechPresentationExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The affine Čech step for a closed restriction of an injective

Source: the affine matching-relations step in the proper closed-injective calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The closed push-pull of an ambient injective has positive Čech exactness on
finite affine pro-étale covers of affine objects, after arbitrary pro-étale localization.
Source: Step 1 and the affine matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.
(blueprint: lem-sp-proetale-closed-injective-affine-cech).

Proof: by `exists_closedCech_corepresentingShortComplex`, the Čech degrees q,
q+1, q+2 of `closedCechCoefficientFunctor A b P V U` are corepresented, naturally
in the ambient sheaf, by a short complex `T` whose two arrows transpose the Čech
differentials; by `closedAffineCech_corepresentingShortComplex_exact` (the
geometric matching-relations calculation) `T` is exact. A degree-(q+1) cocycle
c of the Čech complex of `I` is a map f from the middle object of `T` to `I`
whose composite with the first arrow vanishes by the first boundary identity.
Since `I` is injective and `T` exact, f extends along the last arrow
(`ShortComplex.Exact.descToInjective`); the last universal property turns the
extension into a degree-q cochain whose differential is c by the second
boundary identity. This is an affine statement and does not use properness or
a boundary condition. -/
theorem exactAt_closed_injective_affine_cech
    (A : Type u) [CommRing A] [Finite A]
    {B O : Scheme.{u}} (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt)
    (I : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) [Injective I] :
    let F := (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.hom).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) b.closedComplement).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          b.closedComplement).obj I))
    ∀ (V : P.left.ProEt), IsAffine V.left →
      ∀ {n : ℕ} (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
          IsAffine (Presheaf.cechNerveObj U y).left.left) →
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ ProEt.topology P.left V →
        ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ F.obj)).ExactAt (q + 1) :=
  by
    dsimp only
    intro V hV n U hU hcover q
    let H := closedCechCoefficientFunctor A b P V U
    obtain ⟨T⟩ := exists_closedCech_corepresentingShortComplex A b P V U q
    have hex := closedAffineCech_corepresentingShortComplex_exact A b P V hV U hU
      hcover q T
    change (H.obj I).ExactAt (q + 1)
    rw [HomologicalComplex.exactAt_iff' (H.obj I) q (q + 1) (q + 2)
      (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    let f := (T.middle I).symm c
    have hf : T.complex.f ≫ f = 0 := by
      apply (T.first I).injective
      rw [map_zero, T.first_boundary]
      change (H.obj I).d (q + 1) (q + 2) ((T.middle I) ((T.middle I).symm c)) = 0
      rw [AddEquiv.apply_symm_apply]
      exact hc
    refine ⟨T.last I (hex.descToInjective f hf), ?_⟩
    change (H.obj I).d q (q + 1) _ = c
    rw [← T.last_boundary, hex.comp_descToInjective]
    exact (T.middle I).apply_symm_apply c

end AlgebraicGeometry.Scheme
