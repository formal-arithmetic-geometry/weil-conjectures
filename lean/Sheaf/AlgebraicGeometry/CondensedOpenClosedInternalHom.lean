/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
public import Sheaf.Topology.ProfiniteCondensedRing

import Sheaf.Paper.ModuleObjects
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

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

/-- The two internal sheaf-valued derived-Hom formulas, normalized by evaluation and all
adjunction transposes, natural contravariantly in L,P and covariantly in N.
Source: Bhatt--Scholze Lemma 6.7.13, formal internal-adjunction calculation, and Stacks
Tag 08JB (blueprint: lem-sfb-open-closed-internal-hom-formulas).

Proof plan (the eleven steps of the node):
1. Identify module objects with sectionwise modules over B_T=p_T^*Lambda. The relative
   tensor coequalizer imposes bm tensor n = m tensor bn. Alpha is invertible, identifying
   supportPullback with the recorded upperStar, and the lower-star and lower-shriek
   actions with their ringed-site actions.
2. Pro-etale open/closed localization gives exact j!,i*,i^*,j^*, the two restriction
   identities, mixed vanishing, and the short exact localization sequence. Hence the
   two restrictions detect isomorphisms, without global qcqs assumptions.
3. The open unit gives openSupportProjection. The closed unit, pullback tensor map,
   and closed counit give closedSupportProjection. Restricting to U,Z proves both
   are isomorphisms; the inverse of the latter has the required projection direction.
4. Each of j!,j^*,i*,i^* preserves coproducts by its left adjunction; for i* use its
   support right adjoint. Ringed-site module categories have these small colimits.
5. Sum the projection comparisons over p+q=n. Naturality intertwines both differential
   terms with the same (-1)^p sign. Signed symmetry squares to the identity, since
   (-1)^((p+1)q)=(-1)^(pq+q) and (-1)^(p(q+1)+p)=(-1)^pq.
6. For e=j! or i* and r=j^* or i^*, test K-flatness against acyclic complexes using
   eC tensor Q = e(C tensor rQ), exactness, re=id, and signed symmetry. The same
   exact-functor composite shows preservation of flat terms in both directions.
7. Resolve both inputs by flat-term K-flat complexes. The total-complex comparisons
   descend separately along both resolving-class localization equivalences. Naturality
   respects chain homotopies and inverses of quasi-isomorphisms, so is unbounded.
8. Use actual units/counits of j! adjoint to j^*, j^* adjoint to Rj*, i^* adjoint
   to exact i*, and exact i* adjoint to RclosedSupport. Exact functors are termwise;
   homotopy adjunction and localization preserve the triangle identities.
9. For every derived test object T, tensor-Hom, open projection, open adjunction,
   tensor-Hom and j^* adjoint to Rj* identify Hom(T,H_X(j!L,N)) with
   Hom(T,Rj*H_U(L,j^*N)), naturally in T,L,N.
10. Similarly closed projection, i* adjoint to RclosedSupport, tensor-Hom and
    i^* adjoint to i* identify Hom(T,H_X(i*P,N)) with Hom(T,i*H_Z(P,Ri!N)).
11. Apply these bijections to identities to construct inverse object maps. Naturality
    in the test object proves their inverse identities; naturality in L,P,N proves
    the equations below. Transposing evaluation gives exactly openSupportHomMap and
    closedSupportHomMap with the inverse closed projection, fixing the normalization. -/
theorem openClosedInternalHomFormulas {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ (p : ∀ (P : DerivedCategory (supportModules Λ Z))
        (T : DerivedCategory (supportModules Λ X)),
        ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ≅
          (lowerStar Λ i).mapDerivedCategory.obj
            (((derivedTensor Λ Z).obj P).obj
              ((supportPullback Λ i).mapDerivedCategory.obj T)))
      (o : ∀ (L : DerivedCategory (supportModules Λ U))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj
          (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N) ≅
        (lowerStar Λ j).rightDerivedFunctor.obj
          (((derivedHom Λ U).obj (op L)).obj
            ((supportPullback Λ j).mapDerivedCategory.obj N)))
      (c : ∀ (P : DerivedCategory (supportModules Λ Z))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ≅
        (lowerStar Λ i).mapDerivedCategory.obj
          (((derivedHom Λ Z).obj (op P)).obj
            ((closedSupport Λ i j).rightDerivedFunctor.obj N))),
      (∀ P T, (p P T).hom = closedSupportProjection Λ i P T) ∧
      (∀ L N, (o L N).hom = openSupportHomMap Λ j L N) ∧
      (∀ P N, (c P N).hom = closedSupportHomMap Λ i j hij P N
        (p P (((derivedHom Λ X).obj
          (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)).inv) ∧
      (∀ (L L' : DerivedCategory (supportModules Λ U))
          (N N' : DerivedCategory (supportModules Λ X)) (a : L' ⟶ L) (b : N ⟶ N'),
        (((derivedHom Λ X).map
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj
            (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L'))).map b) ≫
          (o L' N').hom =
        (o L N).hom ≫ (lowerStar Λ j).rightDerivedFunctor.map
          (((derivedHom Λ U).map a.op).app
              ((supportPullback Λ j).mapDerivedCategory.obj N) ≫
            ((derivedHom Λ U).obj (op L')).map
              ((supportPullback Λ j).mapDerivedCategory.map b))) ∧
      (∀ (P P' : DerivedCategory (supportModules Λ Z))
          (N N' : DerivedCategory (supportModules Λ X)) (a : P' ⟶ P) (b : N ⟶ N'),
        (((derivedHom Λ X).map ((lowerStar Λ i).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P'))).map b) ≫
          (c P' N').hom =
        (c P N).hom ≫ (lowerStar Λ i).mapDerivedCategory.map
          (((derivedHom Λ Z).map a.op).app ((closedSupport Λ i j).rightDerivedFunctor.obj N) ≫
            ((derivedHom Λ Z).obj (op P')).map
              ((closedSupport Λ i j).rightDerivedFunctor.map b))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
