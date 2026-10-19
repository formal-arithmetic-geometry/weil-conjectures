/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Canonical direct-image mate in fixed coefficients

Source: blueprint, prop-weil-pbc-comparison-direct-image, first proof paragraph;
Stacks Project, Tags 099R and 0B65
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).

## Main definitions and statements

* `fixedComparisonPullbackPlus`: the canonical termwise pullback comparison.
* `fixedComparisonDirectImageMatePlus`: the canonical derived direct-image mate.
* `isIso_fixedComparisonDirectImageMatePlus`: its qcqs invertibility.
* `fixedComparisonDirectImageMatePlus_counit`: its specified counit normalization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [EnoughInjectives D] [EnoughInjectives D']
  {l : C ⥤ D} {r : D ⥤ C} {p : C' ⥤ D'} {t : D' ⥤ C'}
  {a : C ⥤ C'} {b : D ⥤ D'}
  [l.Additive] [r.Additive] [p.Additive] [t.Additive] [a.Additive] [b.Additive]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]

-- This calculation follows the proved helper in
-- Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit.
private theorem derived_mate_eq (e : l ⊣ r) (d : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv e d σ.hom).natTrans =
      (mateEquiv e.derivedPlus d.derivedPlus θ.hom).natTrans := by
  dsimp only
  let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
  have hθ (N : HomotopyCategory.Plus C) :
      θ.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        D+(b).map (l.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        b.mapDerivedCategoryPlusFactorsh.hom.app (l.mapHomotopyCategoryPlus.obj N) =
      D+(p).map (a.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        p.mapDerivedCategoryPlusFactorsh.hom.app (a.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh l b N]
    rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N]
    rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh a p N]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Functor.rightDerived_ext (R+(r) ⋙ D+(a))
    (Functor.whiskerRight r.rightDerivedFunctorPlusUnit D+(a) ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso D)
  apply NatTrans.ext
  funext M
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (mateEquiv e d σ.hom).natTrans) M
  have hm := Adjunction.derivedPlus_mateEquiv_app_fac e d σ.hom θ.hom hθ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf ⊢
  rw [hf, hm]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

end

namespace AlgebraicGeometry.ProEtale

/-- The pullback comparison, induced termwise from the specified sheaf comparison.
Exact pro-etale pullback is its own left derived functor.
Source: Stacks Tags 099R and 0B65; blueprint comparison-direct-image proof
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate). -/
noncomputable def fixedComparisonPullbackPlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)).symm ≪≫
  Functor.mapDerivedCategoryPlusNatIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
  Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)

/-- The canonical derived direct-image mate of the underived counit comparison.
Its data is the existing right-derived base-change transformation, with its universal
property normalization, not a chosen isomorphism between the endpoints.
Source: Stacks Tags 099R and 0B65; blueprint comparison-direct-image proof
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate). -/
noncomputable def fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))

/-- Invertibility of the specified mate for a qcqs morphism.
Source: Stacks Tag 099R; blueprint comparison-direct-image proof
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).

Proof: the canonical underived comparison is invertible for qcqs f by
`isIso_lowerStarComparisonUpperStarBaseChange`. The comparison pullback of every
injective etale sheaf is acyclic for the pro-etale direct image by
`rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective`. Apply the general
right-derived base-change invertibility theorem to this actual underived map.
Thus it is the specified transformation, rather than an arbitrary comparison,
that is invertible. -/
theorem isIso_fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (fixedComparisonDirectImageMatePlus Λ f) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)
  exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)))
    (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
      (ModuleCat.{u + 1} Λ) f I)

section

variable (Λ : Type (u + 1)) [CommRing Λ]

-- The underived mate calculation is shared with the proof of
-- AlgebraicGeometry.ProEtale.comparison_counit.
private theorem underived_comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj K) ≫ t) h

private theorem underived_comparison_mate {U V : Scheme.{u}} (f : U ⟶ V) :
    lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ) =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom).natTrans := by
  apply NatTrans.ext
  funext K
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
    underived_comparison_counit Λ f K

end

/-- The specified counit-mate normalization. It also characterizes the named component
as the adjoint transpose of the pulled-back etale counit after inverse pullback comparison.
Source: Stacks Tag 0B65; blueprint comparison-direct-image proof, first paragraph
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).

Proof: the iterated-mate identity identifies the underived direct-image comparison
as the mate of the specified pullback comparison. On bounded-below homotopy categories,
the factorization equations for the induced pullback comparison verify the hypothesis of
`Adjunction.derivedPlus_mateEquiv_app_fac`. Compare its conclusion with the defining
factorization of derived base change. Uniqueness of right-derived transformations gives
the derived mate identity. Identify the restricted adjunctions with `derivedPlus`, apply
`mateEquiv_counit`, and cancel the inverse pullback comparison. Compatibility of the
induced natural isomorphism with inversion is checked through the faithful inclusion
of D+ into the unbounded derived category. Naturality is built into the transformation. -/
theorem fixedComparisonDirectImageMatePlus_counit (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fixedComparisonPullbackPlus Λ f).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ f).app K) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f
  let θ := (Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
  have hb : fixedComparisonDirectImageMatePlus Λ f =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus θ.hom).natTrans := by
    unfold fixedComparisonDirectImageMatePlus
    rw [underived_comparison_mate, derived_mate_eq]
  rw [hb, mateEquiv_counit]
  have hθ : (fixedComparisonPullbackPlus Λ f).hom = θ.inv := by
    have hσ : (Functor.mapDerivedCategoryPlusNatIso σ.symm).hom =
        (Functor.mapDerivedCategoryPlusNatIso σ).inv := by
      apply NatTrans.ext
      funext X
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.mapDerivedCategoryNatIso_symm]
      have h : DerivedCategory.Plus.ι.mapIso
          ((Functor.mapDerivedCategoryPlusNatIso σ).app X) =
          (Functor.mapDerivedCategoryNatIso σ).app X.obj :=
        Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app σ X)
      exact (congrArg Iso.inv h).symm
    simp only [fixedComparisonPullbackPlus, θ, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, hσ, Category.assoc, σ]
  rw [hθ]
  change θ.inv.app _ ≫ θ.hom.app _ ≫ _ = _
  rw [Iso.inv_hom_id_app_assoc]


end AlgebraicGeometry.ProEtale

