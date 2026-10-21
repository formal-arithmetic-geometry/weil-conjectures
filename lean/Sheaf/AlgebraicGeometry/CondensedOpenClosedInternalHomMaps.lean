/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
public import Sheaf.Topology.ProfiniteCondensedRing

/-!
# Open and closed formulas for internal derived Hom

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.13, internal
adjunction calculation; Stacks Project Tag 08JB
(blueprint: lem-sfb-open-closed-internal-hom-formulas).

All categories are ordinary unbounded derived categories of modules over the pulled-back
commutative condensed coefficient ring. Support inverse image is canonically identified
with the recorded upper star by `supportPullbackIsoUpperStar`. No completion or finiteness
condition on a derived input is imposed. The theorem includes the evaluation normalization
of both isomorphisms, as well as simultaneous naturality in both arguments.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The open extension/restriction adjunction, using the canonical alpha transport.
Source: Stacks Tag 09BN (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportDerivedAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⊣
      (supportPullback Λ j).mapDerivedCategory :=
  ((openImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (supportPullbackIsoUpperStar Λ j).symm).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (supportPullback Λ j).rightDerivedFunctorIsoMapDerivedCategory

/-- Closed inverse/direct-image adjunction, both functors exact and applied termwise.
Source: Stacks Tag 09AA (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def closedPullbackDerivedAdjunction {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (supportPullback Λ i).mapDerivedCategory ⊣ (lowerStar Λ i).mapDerivedCategory :=
  (supportPullbackAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory

/-- Open projection map: the adjunct of unit tensor identity followed by inverse tensor
comparison. Source: proof step 3 (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportProjection {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    (T : DerivedCategory (supportModules Λ X)) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (((derivedTensor Λ U).obj L).obj ((supportPullback Λ j).mapDerivedCategory.obj T)) ⟶
      ((derivedTensor Λ X).obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T :=
  ((openSupportDerivedAdjunction Λ j).homEquiv
    (((derivedTensor Λ U).obj L).obj ((supportPullback Λ j).mapDerivedCategory.obj T))
    (((derivedTensor Λ X).obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T)).symm
    (((derivedTensor Λ U).map ((openSupportDerivedAdjunction Λ j).unit.app L)).app
        ((supportPullback Λ j).mapDerivedCategory.obj T) ≫
      (supportDerivedTensorComparison Λ j
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) T).inv)

/-- Closed projection map: closed unit followed by pullback tensor comparison and closed
counit. Source: proof step 3 (blueprint: lem-sfb-open-closed-internal-hom-formulas).
Its direction uses the unit of i^* adjoint to i_*, never a nonexistent counit i_*i^* -> id. -/
noncomputable def closedSupportProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (P : DerivedCategory (supportModules Λ Z))
    (T : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj ((supportPullback Λ i).mapDerivedCategory.obj T)) :=
  (closedPullbackDerivedAdjunction Λ i).unit.app
      (((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T) ≫
    (lowerStar Λ i).mapDerivedCategory.map
      ((supportDerivedTensorComparison Λ i
        ((lowerStar Λ i).mapDerivedCategory.obj P) T).hom ≫
        ((derivedTensor Λ Z).map ((closedPullbackDerivedAdjunction Λ i).counit.app P)).app
          ((supportPullback Λ i).mapDerivedCategory.obj T))

/-- Open internal-Hom comparison determined by projection and evaluation transposes.
Source: proof steps 9 and 11 (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportHomMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    (N : DerivedCategory (supportModules Λ X)) :
    ((derivedHom Λ X).obj
      (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N ⟶
    (lowerStar Λ j).rightDerivedFunctor.obj
      (((derivedHom Λ U).obj (op L)).obj
        ((supportPullback Λ j).mapDerivedCategory.obj N)) :=
  let H := ((derivedHom Λ X).obj
    (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N
  let rH := (supportPullback Λ j).mapDerivedCategory.obj H
  let rN := (supportPullback Λ j).mapDerivedCategory.obj N
  (closedSupportOpenDerivedAdjunction Λ j).homEquiv H
    (((derivedHom Λ U).obj (op L)).obj rN)
    ((derivedTensorHomAdjunction Λ L).homEquiv rH rN
      ((openSupportDerivedAdjunction Λ j).homEquiv (((derivedTensor Λ U).obj L).obj rH) N
        (openSupportProjection Λ j L H ≫
          (derivedTensorHomAdjunction Λ
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).counit.app N)))

/-- Closed internal-Hom comparison using an inverse of the canonical closed projection.
Source: proof steps 10 and 11 (blueprint: lem-sfb-open-closed-internal-hom-formulas).
The theorem supplies its inverse projection as an isomorphism with specified hom. -/
noncomputable def closedSupportHomMap {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) (N : DerivedCategory (supportModules Λ X))
    (χ : (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj
          ((supportPullback Λ i).mapDerivedCategory.obj
            (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N))) ⟶
      ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)) :
    (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedHom Λ Z).obj (op P)).obj ((closedSupport Λ i j).rightDerivedFunctor.obj N)) :=
  let H := ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N
  let rH := (supportPullback Λ i).mapDerivedCategory.obj H
  let iN := (closedSupport Λ i j).rightDerivedFunctor.obj N
  (closedPullbackDerivedAdjunction Λ i).homEquiv H
    (((derivedHom Λ Z).obj (op P)).obj iN)
    ((derivedTensorHomAdjunction Λ P).homEquiv rH iN
      ((closedSupportDerivedAdjunction Λ i j hij).homEquiv (((derivedTensor Λ Z).obj P).obj rH) N
        (χ ≫ (derivedTensorHomAdjunction Λ
          ((lowerStar Λ i).mapDerivedCategory.obj P)).counit.app N)))

end AlgebraicGeometry.ProEtale.CondensedRing
