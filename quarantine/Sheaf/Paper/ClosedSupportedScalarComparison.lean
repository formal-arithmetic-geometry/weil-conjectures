/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # The supported closed-unit scalar comparison

Source: blueprint main-20261015, det-prop-scalar-six-pullback, proof (1)--(2),
closed-unit expansion; Stacks proetale.tex, Tags 09AA, 09BM and 09AH.
(blueprint: lem-sfb-closed-supported-scalar-comparison).

The small pro-etale sites are represented by the existing equivalent AsSmall models.
The scalar comparisons are precisely ScalarPullback.θ_h, with its specified action mate.
No arbitrary comparison morphism or identification of the original site universes is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w uX uU uZ vX vU vZ wX wU wZ
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace SheafOfModules.ScalarPullback

/-- A presentation of the conclusions of the assumed unbounded open/closed calculus.
All four adjunction maps are pinned on complexes to the ordinary maps, exactly as in
`CategoryTheory.exactOpenClosedUnboundedCalculus`; the triangle identities are fields
of the two adjunctions. This packages hypotheses, without choosing new functors.
Source: blueprint det-prop-scalar-six-pullback (2), supported-unit construction.
(blueprint: lem-sfb-closed-supported-scalar-comparison). -/
structure ClosedScalarCalculus
    {AX : Type uX} {AU : Type uU} {AZ : Type uZ}
    [Category.{vX} AX] [Category.{vU} AU] [Category.{vZ} AZ]
    [Abelian AX] [Abelian AU] [Abelian AZ]
    [HasDerivedCategory.{wX} AX] [HasDerivedCategory.{wU} AU]
    [HasDerivedCategory.{wZ} AZ]
    (J : AU ⥤ AX) (P : AX ⥤ AU) (Q : AX ⥤ AZ) (I : AZ ⥤ AX)
    [J.Additive] [P.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (a : J ⊣ P) (b : Q ⊣ I) where
  openAdjunction : J.mapDerivedCategory ⊣ P.mapDerivedCategory
  closedAdjunction : Q.mapDerivedCategory ⊣ I.mapDerivedCategory
  openUnit : ∀ K : CochainComplex AU ℤ,
    openAdjunction.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        P.mapDerivedCategoryFactors.inv.app ((J.mapHomologicalComplex (.up ℤ)).obj K) ≫
        P.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app K)
  openCounit : ∀ K : CochainComplex AX ℤ,
    openAdjunction.counit.app (DerivedCategory.Q.obj K) =
      J.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
        J.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K)
  closedUnit : ∀ K : CochainComplex AX ℤ,
    closedAdjunction.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        I.mapDerivedCategoryFactors.inv.app ((Q.mapHomologicalComplex (.up ℤ)).obj K) ≫
        I.mapDerivedCategory.map (Q.mapDerivedCategoryFactors.inv.app K)
  closedCounit : ∀ K : CochainComplex AZ ℤ,
    closedAdjunction.counit.app (DerivedCategory.Q.obj K) =
      Q.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app K) ≫
        Q.mapDerivedCategoryFactors.hom.app ((I.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).counit.app K)
  openUnitIso : IsIso openAdjunction.unit
  closedCounitIso : IsIso closedAdjunction.counit
  openClosedZero : ∀ M : DerivedCategory AZ,
    IsZero (P.mapDerivedCategory.obj (I.mapDerivedCategory.obj M))
  closedOpenZero : ∀ M : DerivedCategory AU,
    IsZero (Q.mapDerivedCategory.obj (J.mapDerivedCategory.obj M))
  jointlyReflect : ∀ (K L : DerivedCategory AX) (f : K ⟶ L),
    IsIso (P.mapDerivedCategory.map f) → IsIso (Q.mapDerivedCategory.map f) → IsIso f
  supportedUnit : ∀ H : DerivedCategory AX,
    IsZero (P.mapDerivedCategory.obj H) → IsIso (closedAdjunction.unit.app H)
  closedFaithful : ∀ K L : DerivedCategory AX,
    I.mapDerivedCategory.essImage K → I.mapDerivedCategory.essImage L →
      Function.Bijective (fun f : K ⟶ L ↦ Q.mapDerivedCategory.map f)

/-- The supported-unit formula as a natural transformation. It is the transpose of
inverse theta followed by the scalar image of the old closed counit. Whiskering the
existing adjunction constructs its naturality, without a postponed definition law.
Source: blueprint det-prop-scalar-six-pullback (2), closed-unit formula.
(blueprint: lem-sfb-closed-supported-scalar-comparison). -/
def closedScalarMap
    {AX : Type uX} {AZ : Type uZ} {BX : Type uU} {BZ : Type vX}
    [Category.{vU} AX] [Category.{vZ} AZ] [Category.{wX} BX] [Category.{wU} BZ]
    {QA : AX ⥤ AZ} {IA : AZ ⥤ AX} {QB : BX ⥤ BZ} {IB : BZ ⥤ BX}
    (bA : QA ⊣ IA) (bB : QB ⊣ IB) (TX : AX ⥤ BX) (TZ : AZ ⥤ BZ)
    (θ : QA ⋙ TZ ≅ TX ⋙ QB) : IA ⋙ TX ⟶ TZ ⋙ IB :=
  ((bB.whiskerRight AZ).homEquiv (IA ⋙ TX) TZ)
    ((Functor.associator IA TX QB).hom ≫ Functor.whiskerLeft IA θ.inv ≫
      (Functor.associator IA QA TZ).inv ≫ Functor.whiskerRight bA.counit TZ ≫
        (Functor.leftUnitor TZ).hom)

section Scheme

variable {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  {AX BX : Sheaf (proEtaleModelTopology X) CommRingCat.{u + 1}}
  {AZ BZ : Sheaf (proEtaleModelTopology Z) CommRingCat.{u + 1}}
  {AU BU : Sheaf (proEtaleModelTopology U) CommRingCat.{u + 1}}
  (φX : AX ⟶ BX) (φZ : AZ ⟶ BZ) (φU : AU ⟶ BU)
  (Li : Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
    Sheaf (proEtaleModelTopology Z) (Type (u + 1)))
  (Lj : Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
    Sheaf (proEtaleModelTopology U) (Type (u + 1)))
  (adji : Li ⊣ (proEtaleModelBaseChange i).sheafPushforwardContinuous
    (Type (u + 1)) (proEtaleModelTopology X) (proEtaleModelTopology Z))
  (adjj : Lj ⊣ (proEtaleModelBaseChange j).sheafPushforwardContinuous
    (Type (u + 1)) (proEtaleModelTopology X) (proEtaleModelTopology U))
  [PreservesFiniteLimits Li] [PreservesFiniteLimits Lj]
  (iA : InverseImage Li AX AZ) (iB : InverseImage Li BX BZ)
  (jA : InverseImage Lj AX AU) (jB : InverseImage Lj BX BU)
  (hi : Li.map ((sheafCompose (proEtaleModelTopology X)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).map φX) ≫
      (inverseRing iB).hom = (inverseRing iA).hom ≫
        (sheafCompose (proEtaleModelTopology Z)
          (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).map φZ)
  (hj : Lj.map ((sheafCompose (proEtaleModelTopology X)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).map φX) ≫
      (inverseRing jB).hom = (inverseRing jA).hom ≫
        (sheafCompose (proEtaleModelTopology U)
          (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).map φU)
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [HasDerivedCategory.{w} (Modules AZ)] [HasDerivedCategory.{w} (Modules BZ)]
  [HasDerivedCategory.{w} (Modules AU)] [HasDerivedCategory.{w} (Modules BU)]
  [(inverseModules iA).Additive] [(inverseModules iB).Additive]
  [(inverseModules jA).Additive] [(inverseModules jB).Additive]
  [PreservesFiniteLimits (inverseModules iA)] [PreservesFiniteColimits (inverseModules iA)]
  [PreservesFiniteLimits (inverseModules iB)] [PreservesFiniteColimits (inverseModules iB)]
  [PreservesFiniteLimits (inverseModules jA)] [PreservesFiniteColimits (inverseModules jA)]
  [PreservesFiniteLimits (inverseModules jB)] [PreservesFiniteColimits (inverseModules jB)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]
  [PreservesFiniteLimits (restriction φZ)] [PreservesFiniteColimits (restriction φZ)]
  [PreservesFiniteLimits (restriction φU)] [PreservesFiniteColimits (restriction φU)]
  (mX : DerivedChangeOfRingsCochainModel.{u + 1, u + 1, u + 1, w, w} φX)
  (mZ : DerivedChangeOfRingsCochainModel.{u + 1, u + 1, u + 1, w, w} φZ)
  (mU : DerivedChangeOfRingsCochainModel.{u + 1, u + 1, u + 1, w, w} φU)
  (aX : mX.E ⊣ restriction φX) (aZ : mZ.E ⊣ restriction φZ)
  (aU : mU.E ⊣ restriction φU)
  (dX : mX.T ⊣ (restriction φX).mapDerivedCategory)
  (dZ : mZ.T ⊣ (restriction φZ).mapDerivedCategory)
  (dU : mU.T ⊣ (restriction φU).mapDerivedCategory)
  (normX : AdjunctionNormalized mX aX dX) (normZ : AdjunctionNormalized mZ aZ dZ)
  (normU : AdjunctionNormalized mU aU dU)
  (JA : Modules AU ⥤ Modules AX) (IA : Modules AZ ⥤ Modules AX)
  (JB : Modules BU ⥤ Modules BX) (IB : Modules BZ ⥤ Modules BX)
  [JA.Additive] [IA.Additive] [JB.Additive] [IB.Additive]
  [PreservesFiniteLimits JA] [PreservesFiniteColimits JA]
  [PreservesFiniteLimits IA] [PreservesFiniteColimits IA]
  [PreservesFiniteLimits JB] [PreservesFiniteColimits JB]
  [PreservesFiniteLimits IB] [PreservesFiniteColimits IB]
  (oa : JA ⊣ inverseModules jA) (ca : inverseModules iA ⊣ IA)
  (ob : JB ⊣ inverseModules jB) (cb : inverseModules iB ⊣ IB)
  (calA : ClosedScalarCalculus JA (inverseModules jA) (inverseModules iA) IA oa ca)
  (calB : ClosedScalarCalculus JB (inverseModules jB) (inverseModules iB) IB ob cb)
  [thetaI : IsIso (θ_h iA iB hi inferInstance dX dZ)]
  [thetaJ : IsIso (θ_h jA jB hj inferInstance dX dU)]

include i j hij adji adjj normX normZ normU hj thetaI thetaJ in
/-- The canonical new-coefficient-linear supported closed comparison is invertible,
has zero open restriction, and is uniquely characterized by its closed normalization.
The component equation writes the supported-unit formula with Lean's composition order.
The two zero-object clauses express the support assertion as well as the zero map.

Source: blueprint main-20261015 det-prop-scalar-six-pullback (1)--(2), closed-unit
expansion; Stacks proetale.tex Tags 09AA, 09BM, 09AH.
(blueprint: lem-sfb-closed-supported-scalar-comparison).

Proof: (1) The assumed calculus gives P_A I_A = 0 and P_B I_B = 0. The specified
open scalar comparison identifies P_B T_X I_A M with T_U P_A I_A M. The scalar
adjunction makes T_U of a zero object initial and hence zero, so both source and
target have zero open restriction. (2) The supported closed unit is invertible on
H = T_X I_A M. The old closed counit and inverse theta are invertible, and their
scalar and closed direct images are invertible. Their composite is the displayed
delta. All factors live in the B-module derived categories and are natural.
(3) Naturality of the closed counit and its left triangle identity give precisely
Q_B(delta) followed by epsilon_B equal to inverse theta followed by T_Z(epsilon_A).
(4) For any f : H -> I_B N, unit naturality and the right triangle give
eta_H followed by I_B(Q_B(f) followed by epsilon_N) equal to f. Thus a morphism
satisfying the normalization must equal delta. These are exactly the four proof
steps of this node, using the unbounded calculus, K-flat scalar normalization and
derived coefficient adjunction dependencies. No flatness or bound is used. -/
theorem closed_supported_scalar_comparison :
    IsIso (closedScalarMap calA.closedAdjunction calB.closedAdjunction mX.T mZ.T
      (asIso (θ_h iA iB hi inferInstance dX dZ))) ∧
    ∀ M : DerivedCategory (Modules AZ),
      (closedScalarMap calA.closedAdjunction calB.closedAdjunction mX.T mZ.T
          (asIso (θ_h iA iB hi inferInstance dX dZ))).app M =
        calB.closedAdjunction.unit.app (mX.T.obj (IA.mapDerivedCategory.obj M)) ≫
          IB.mapDerivedCategory.map
            (inv ((θ_h iA iB hi inferInstance dX dZ).app (IA.mapDerivedCategory.obj M))) ≫
          IB.mapDerivedCategory.map (mZ.T.map (calA.closedAdjunction.counit.app M)) ∧
      IsZero ((inverseModules jB).mapDerivedCategory.obj
        (mX.T.obj (IA.mapDerivedCategory.obj M))) ∧
      IsZero ((inverseModules jB).mapDerivedCategory.obj
        (IB.mapDerivedCategory.obj (mZ.T.obj M))) ∧
      (inverseModules jB).mapDerivedCategory.map
        ((closedScalarMap calA.closedAdjunction calB.closedAdjunction mX.T mZ.T
          (asIso (θ_h iA iB hi inferInstance dX dZ))).app M) = 0 ∧
      (inverseModules iB).mapDerivedCategory.map
          ((closedScalarMap calA.closedAdjunction calB.closedAdjunction mX.T mZ.T
            (asIso (θ_h iA iB hi inferInstance dX dZ))).app M) ≫
          calB.closedAdjunction.counit.app (mZ.T.obj M) =
        inv ((θ_h iA iB hi inferInstance dX dZ).app (IA.mapDerivedCategory.obj M)) ≫
          mZ.T.map (calA.closedAdjunction.counit.app M) ∧
      ∀ f : mX.T.obj (IA.mapDerivedCategory.obj M) ⟶
          IB.mapDerivedCategory.obj (mZ.T.obj M),
        (inverseModules iB).mapDerivedCategory.map f ≫
            calB.closedAdjunction.counit.app (mZ.T.obj M) =
          inv ((θ_h iA iB hi inferInstance dX dZ).app (IA.mapDerivedCategory.obj M)) ≫
            mZ.T.map (calA.closedAdjunction.counit.app M) →
        f = (closedScalarMap calA.closedAdjunction calB.closedAdjunction mX.T mZ.T
          (asIso (θ_h iA iB hi inferInstance dX dZ))).app M := by
  sorry

end Scheme
end SheafOfModules.ScalarPullback
