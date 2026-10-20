/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry

/-! # Evaluation formula for the canonical internal compact-support adjunction

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).

## Main statements

* `internalAdjunctionEvaluation` states the tensor--Hom transpose formula for the
  canonical compact-support internal adjunction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace CategoryTheory

private theorem conjugate_uncurry
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {C₀ : C} {M : D} (f : C₀ ⟶ R₁.obj M) :
    (a₂.homEquiv _ _).symm (f ≫ (conjugateEquiv a₁ a₂ α).app M) =
      α.app C₀ ≫ (a₁.homEquiv _ _).symm f := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← α.naturality_assoc]

end CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The mate calculation identifying the named internal-adjunction isomorphism with its
projection, tensor, and exceptional-counit representative.
Source: the displayed Hom-bijection calculation in the proof of
`lem-asd-internal-adjunction-evaluation`.
Proof: Expand the parametrized conjugate and apply conjugateEquiv counit naturality to obtain
projection followed by tensor transpose and exceptional counit.
(blueprint: lem-asd-internal-adjunction-evaluation-mate-core).
-/
theorem internalAdjunctionEvaluation_mate_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (K Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶
      (R((f)_*[ModuleCat A])).obj
        (((RHom(X)[ModuleCat A]).obj (op M)).obj
          ((R(f)^![ModuleCat A]).obj K))) :
    ((derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)).homEquiv
        Q K).symm
      (h ≫ (((derivedHomRightDerivedLowerShriekIsoOfFinite A f).app (op M)).app K).hom) =
      ((projectionMap (ModuleCat A) f).app M).app Q ≫
        (R(f)_![ModuleCat A]).map
          (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
              (L((f)^*[ModuleCat A]).obj Q)
              ((R(f)^![ModuleCat A]).obj K)).symm
            (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv
                Q (((RHom(X)[ModuleCat A]).obj (op M)).obj
                  ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K := by
  let := isIso_projectionMap_of_finite A f
  simp only [derivedHomRightDerivedLowerShriekIsoOfFinite,
    derivedHomRightDerivedLowerShriekIso, Iso.app_hom,
    ParametrizedAdjunction.conjugateIso, NatIso.ofComponents_hom_app,
    conjugateIsoEquiv_apply_hom, ParametrizedAdjunction.precomp_adj,
    derivedTensorHomAdjunction, asIso_hom]
  -- Abstract the projection component before normalizing its functor types. This avoids
  -- unfolding the compactification and the derived functors during mate matching.
  generalize hα : (projectionMap (ModuleCat A) f).app M = α
  change ((derivedTensor (ModuleCat A) S).obj ((R(f)_![ModuleCat A]).obj M) ⟶
    L((f)^*[ModuleCat A]) ⋙ (derivedTensor (ModuleCat A) X).obj M ⋙
      R(f)_![ModuleCat A]) at α
  change ((derivedTensorHomAdjunction (ModuleCat A)
      ((R(f)_![ModuleCat A]).obj M)).homEquiv Q K).symm
    (h ≫ (conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).comp
        ((derivedTensorHomAdjunction (ModuleCat A) M).comp
          (rightDerivedUpperShriekAdjunction (ModuleCat A) f)))
      (derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M))
      α).app K) =
    α.app Q ≫ (R(f)_![ModuleCat A]).map
      (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
        (L((f)^*[ModuleCat A]).obj Q) ((R(f)^![ModuleCat A]).obj K)).symm
        (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv Q
          (((RHom(X)[ModuleCat A]).obj (op M)).obj
            ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K
  have e := conjugate_uncurry
    ((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).comp
      ((derivedTensorHomAdjunction (ModuleCat A) M).comp
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f)))
    (derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)) α h
  simpa only [Adjunction.comp_homEquiv, Equiv.symm_trans, Equiv.trans_apply,
    Adjunction.homEquiv_counit, Functor.comp_obj, Category.assoc] using e

/-- The tensor--Hom transpose of the canonical compact-support internal adjunction.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).
-/
theorem internalAdjunctionEvaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (K Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶
      (R((f)_*[ModuleCat A])).obj
        (((RHom(X)[ModuleCat A]).obj (op M)).obj
          ((R(f)^![ModuleCat A]).obj K))) :
    ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
      ((derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)).homEquiv
        Q K).symm
      (h ≫ (((derivedHomRightDerivedLowerShriekIsoOfFinite A f).app (op M)).app K).hom) =
      ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
        ((projectionMap (ModuleCat A) f).app M).app Q ≫
        (R(f)_![ModuleCat A]).map
          (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
              (L((f)^*[ModuleCat A]).obj Q)
              ((R(f)^![ModuleCat A]).obj K)).symm
            (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv
                Q (((RHom(X)[ModuleCat A]).obj (op M)).obj
                  ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K := by
  rw [internalAdjunctionEvaluation_mate_core A f M K Q h]

end AlgebraicGeometry.Etale
