/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeCompactification
public import WeilConjectures.WeilSheaf.SmoothPurityOpenFieldBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekIso

/-!
# The compact-support base change of an open immersion on bounded constructible complexes (A)

Let `j : U ⟶ X` be an open immersion of separated `k₁`-schemes of finite type, `j' : U' ⟶ X'`
an open immersion over `k₂`, and `πU : U' ⟶ U`, `πX : X' ⟶ X` morphisms of schemes forming a
cartesian square `j' ≫ πX = πU ≫ j`. This file provides

* `openImmersionLowerShriekBaseChangeIso`: the compact-support base change isomorphism
  `Rj_! ⋙ πX^* ≅ πU^* ⋙ Rj'_!` on bounded constructible `ℚ̄_ℓ`-complexes, the **restriction** of
  the ambient `ProEtale.CondensedRing.openImmersionLowerShriekMapDerivedCategoryBaseChangeIso`
  (`D(j_!) ⋙ D(πX^*) ≅ D(πU^*) ⋙ D(j'_!)`) through `Rj_! ≅ j_!`
  (`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`) and the
  identifications `L(π^*) ≅ D(π^*)` of the derived pullbacks with the levelwise ones;
* `isIso_upperShriekMateOfMap_app_of_isOpenImmersion`: for **any** compact-support base change
  isomorphism `bc` of an open immersion, the exceptional base change map `πU^* Rj^! N ⟶ Rj'^! πX^* N`
  (the mate of `bc` under `Rj_! ⊣ Rj^!`, `Rj'_! ⊣ Rj'^!`) is invertible at every `N`. This is
  `isIso_smoothExceptionalMate_of_isOpenImmersion` (full faithfulness of `Rj_!` and the pullback
  composition isomorphism, no compatibility hypothesis `hEx` on the mate is needed) in the form
  consumed by `isIso_smoothUnitBaseChange_paste`;
* `isIso_smoothUnitBaseChange_toPoint_structure`: A1' over a point, the exceptional base change
  map at the unit of the structure morphism `a_X : X ⟶ Spec k` along the geometric fibre, for
  the pasted compact-support base change isomorphism `compactificationLowerShriekBaseChange`
  of the restricted open-immersion base change and the proper base change of the
  compactification: invertible, with no hypothesis beyond the trivialization `e` of
  `π^* ℚ̄_ℓ` over the point.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section UpperStarOfMapCompatibility

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pullback along a morphism of schemes on bounded constructible complexes is
compatible with the inclusions: the restriction `boundedConstructibleUpperStarOfMap` of
`L(g^*)`. -/
def boundedConstructibleUpperStarOfMapCompatibility (g : Y.left ⟶ X.left) :
    boundedConstructibleUpperStarOfMap l (X := X) (Y := Y) g ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((g)^*⟦Profinite.padicAlgClRingObj l⟧) :=
  ObjectProperty.liftCompιIso _ _ _

end UpperStarOfMapCompatibility

section OpenImmersion

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U X : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {U' X' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (j' : U' ⟶ X') [IsOpenImmersion j'.left]
  {πU : U'.left ⟶ U.left} {πX : X'.left ⟶ X.left}
  (hsq : IsPullback j'.left πU πX j.left)

/-- The ambient base change isomorphism `D(j_!) ⋙ D(πX^*) ≅ D(πU^*) ⋙ D(j'_!)` read on the
inclusions of the bounded constructible complexes:
`(Rj_! ⋙ πX^*) ⋙ ι ≅ (πU^* ⋙ Rj'_!) ⋙ ι`. -/
def openImmersionLowerShriekBaseChangeIsoAux :
    (boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πX) ⋙
        (boundedConstructible _).ι ≅
      (boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j') ⋙
        (boundedConstructible _).ι :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarOfMapCompatibility l πX) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j) _ ≪≫
        boundedConstructibleOpenImmersionLowerShriekCompatibility _ l j) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ πX) ≪≫
        openImmersionLowerShriekMapDerivedCategoryBaseChangeIso _ hsq ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ πU).symm _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleUpperStarOfMapCompatibility l πU).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((boundedConstructibleOpenImmersionLowerShriekCompatibility _ l j').symm ≪≫
        Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j').symm _) ≪≫
    (Functor.associator _ _ _).symm

/-- **The compact-support base change isomorphism of an open immersion on bounded constructible
complexes**, `Rj_! ⋙ πX^* ≅ πU^* ⋙ Rj'_!`: the restriction of the ambient
`openImmersionLowerShriekMapDerivedCategoryBaseChangeIso` along the fully faithful inclusions. -/
def openImmersionLowerShriekBaseChangeIso :
    boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πX ≅
      boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j' :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (openImmersionLowerShriekBaseChangeIsoAux l j j' hsq)

/-- The restricted base change isomorphism is, on the underlying complexes, the ambient one. -/
lemma openImmersionLowerShriekBaseChangeIso_hom_app_hom
    (A : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj l⟧) :
    ((openImmersionLowerShriekBaseChangeIso l j j' hsq).hom.app A).hom =
      (openImmersionLowerShriekBaseChangeIsoAux l j j' hsq).hom.app A :=
  congrArg (fun t ↦ t.app A)
    (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).map_preimage
      (openImmersionLowerShriekBaseChangeIsoAux l j j' hsq).hom)

/-- **The exceptional base change map of an open immersion is invertible at every object**, for
any compact-support base change isomorphism `bc` of the open immersion: `Rj_!` is fully faithful
and the pullbacks commute, so the mate of `bc` under `Rj_! ⊣ Rj^!` and `Rj'_! ⊣ Rj'^!` is
invertible (`isIso_smoothExceptionalMate_of_isOpenImmersion`). No compatibility of `bc` with the
adjunctions `Rj_! ⊣ j^*` is needed. -/
theorem isIso_upperShriekMateOfMap_app_of_isOpenImmersion
    (bc : boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πX ≅
      boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j')
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((upperShriekMateOfMap l j j' bc).app N) := by
  have h := isIso_smoothExceptionalMate_of_isOpenImmersion l j j' hsq.flip.toCommSq bc N
  rw [← IsIso.Iso.inv_hom bc] at h
  exact h

end OpenImmersion

section Compactification

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The compact-support base change isomorphism, along the geometric fibre, of the open immersion
`j : X ⟶ X^c` of the chosen compactification of the structure morphism of `X`: the restriction of
the ambient one. -/
abbrev structureCompactificationOpenBaseChange :
    boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
        boundedConstructibleUpperStarOfMap l
          (structureCompactification X).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l
          (geometricFiberOverMap (structureCompactification X).overI) :=
  openImmersionLowerShriekBaseChangeIso l (structureCompactification X).overI
    (geometricFiberOverMap (structureCompactification X).overI)
    (isPullback_geometricFiberOverMap (structureCompactification X).overI).flip

variable {X}

/-- `isIso_smoothUnitBaseChange_structureCompactification` without the hypothesis `hEx`: the
exceptional base change map of the open immersion is invertible for any `bcj`
(`isIso_upperShriekMateOfMap_app_of_isOpenImmersion`). -/
theorem isIso_smoothUnitBaseChange_structureCompactification'
    (bcj : boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
        boundedConstructibleUpperStarOfMap l
          (structureCompactification X).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l
          (geometricFiberOverMap (structureCompactification X).overI))
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l
      ((structureCompactification X).overI ≫ (structureCompactification X).overG)
      (geometricFiberOverMap (structureCompactification X).overI ≫
        geometricFiberOverMap (structureCompactification X).overG)
      (pasteLowerShriekBaseChange l (structureCompactification X).overI
        (structureCompactification X).overG _ _ bcj
        (properLowerShriekBaseChangeOfMap l (structureCompactification X).overG
          (geometricFiberOverMap (structureCompactification X).overG)
          (isPullback_geometricFiberOverMap (structureCompactification X).overG))) e) := by
  haveI := isIso_upperShriekMateOfMap_app_of_isOpenImmersion l (structureCompactification X).overI
    (geometricFiberOverMap (structureCompactification X).overI)
    (isPullback_geometricFiberOverMap (structureCompactification X).overI).flip bcj
    ((boundedConstructibleUpperShriek l (structureCompactification X).overG).obj (𝟙_ _))
  haveI := isIso_smoothUnitBaseChange_of_proper_point l (structureCompactification X).overG
    (geometricFiberOverMap (structureCompactification X).overG) (isPullback_point_geometricFiber X)
    (isPullback_geometricFiberOverMap (structureCompactification X).overG) e
  exact isIso_smoothUnitBaseChange_paste l (structureCompactification X).overI
    (structureCompactification X).overG _ _ bcj _ e

/-- `isIso_smoothUnitBaseChange_toPoint` without the hypothesis `hEx`. -/
theorem isIso_smoothUnitBaseChange_toPoint'
    (bcj : boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
        boundedConstructibleUpperStarOfMap l
          (structureCompactification X).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l
          (geometricFiberOverMap (structureCompactification X).overI))
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l (toPoint X) (geometricFiberOverMap (toPoint X))
      (compactificationLowerShriekBaseChange l bcj) e) := by
  haveI := isIso_smoothUnitBaseChange_structureCompactification' l bcj e
  exact isIso_smoothUnitBaseChange_of_eq l (structureCompactification X).overI_overG
    (by rw [← geometricFiberOverMap_comp, (structureCompactification X).overI_overG]) _ e

/-- **A1' over a point, fully instantiated**: the exceptional base change map at the unit of the
structure morphism `a_X : X ⟶ Spec k` along the geometric fibre is invertible for the pasted
compact-support base change isomorphism of the restricted open-immersion base change
`structureCompactificationOpenBaseChange` and the proper base change of the compactification. -/
theorem isIso_smoothUnitBaseChange_toPoint_structure
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l (toPoint X) (geometricFiberOverMap (toPoint X))
      (compactificationLowerShriekBaseChange l (structureCompactificationOpenBaseChange l X)) e) :=
  isIso_smoothUnitBaseChange_toPoint' l _ e

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
