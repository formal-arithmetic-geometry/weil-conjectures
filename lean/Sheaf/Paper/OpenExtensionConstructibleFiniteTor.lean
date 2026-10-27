/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.SixFunctors.OpenImmersionTensorProjection
import Sheaf.Paper.OpenExtensionConstantModelConstructible
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Open extension preserves constructibility and specified Tor bounds

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md, proof (3)
(blueprint: lem-sfb-open-extension-zero-constructible-finite-tor).

The categories are the ordinary unbounded derived categories of internal modules.
Constant scalar-model constructibility and general ring-object constructibility are
kept distinct. The cohomology and Tor intervals are independent.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem torAmplitudeIn_iff_derivedTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    DerivedCategory.torAmplitudeIn _ a b K ↔ ∀ N,
      DerivedCategory.homologyConcentratedIn a b
        (((derivedTensor Λ X).obj K).obj ((DerivedCategory.singleFunctor _ 0).obj N)) := by
  delta DerivedCategory.torAmplitudeIn derivedTensor CategoryTheory.Mod.derivedMonoidalCategory
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  rfl

private theorem finiteStratification_models {X : Scheme.{u}}
    (S : Scheme.Stratification X) (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (hP : ∀ t : Fin S.n, P (S.domain t) (S.immersion t)) :
    ∃ T : Scheme.FiniteLocallyClosedStratification X,
      (∀ t : Fin T.n, Topology.IsConstructible (T.stratum t)) ∧
      ∀ t : Fin T.n, P (T.domain t) (T.immersion t) := by
  let T : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨T, S.isConstructible_stratum, hP⟩

attribute [local irreducible] derivedTensor

/-- Exact open extension preserves bounded constant-model constructibility, finite Tor
amplitude, the supplied cohomological interval, and the supplied Tor interval. Its output
is also bounded constructible in the general locally-finitely-presented ring-object sense.
No admissibility or completeness hypothesis is imposed on the condensed coefficient ring.

Source: blueprint main-20261015, det-sf-comp-composition-interchange.proof.md, proof (3);
lem-sfb-dc-open-lower-shriek-preserves.proof.md; det-lem-int-tensor-projection.proof.md,
open immersions and derived version
(blueprint: lem-sfb-open-extension-zero-constructible-finite-tor).

Proof: finite type over the field and quasi-compactness make U and X Noetherian.
For every cohomology module use the proved module-level extension theorem, which
adjoins the reduced closed complement with its zero scalar model. Transport the
resulting models through the exact-functor homology isomorphism; exactness also
preserves boundedness and the specified cohomology interval. For any test module N,
the open projection isomorphism and the exact pullback comparison on N[0] identify
the tensor of the extended complex with the extension of A tensor j^*N. Exactness
preserves its cohomology interval [a,b], giving the stated Tor interval. Finally,
finite constant local models imply local finite presentation. Restriction along
the inverse coefficient isomorphism transports this to the general ring-object
constructibility predicate on the same stratification. -/
theorem openExtension_constructible_finiteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (A : ConstantModelConstructibleFiniteTor Λ U.left)
    (m n a b : ℤ)
    (hcoh : DerivedCategory.homologyConcentratedIn m n A.obj)
    (htor : DerivedCategory.torAmplitudeIn _ a b A.obj) :
    (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) ∧
    DerivedCategory.homologyConcentratedIn m n
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) ∧
    DerivedCategory.torAmplitudeIn _ a b
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) ∧
    boundedConstructible (condensedRingObj Λ X.left)
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) := by
  classical
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : IsNoetherian U.left := ⟨⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  let : U.left.Over (Spec (.of k)) := ⟨U.hom⟩
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (U.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType U.hom›
  have : QuasiCompact (U.left ↘ Spec (.of k)) := ‹QuasiCompact U.hom›
  have : IsSeparated (U.left ↘ Spec (.of k)) := ‹IsSeparated U.hom›
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  have : j.left.IsOver (Spec (.of k)) := ⟨j.w⟩
  let F := openImmersionLowerShriek Λ j.left
  have extend (M) (hM : IsConstantModelConstructible Λ U.left M) :
      IsConstantModelConstructible Λ X.left (F.obj M) := by
    obtain ⟨S, hS⟩ := (show IsConstantModelConstructible Λ U.left M =
      IsFiniteConstantStratified Λ U.left M from
        if_pos ⟨inferInstance, inferInstance⟩).mp hM
    obtain ⟨T, hT, hmodels⟩ := finiteStratification_models S
      (fun Y f ↦ HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M)) hS
    have h := constantModelConstructible_openImmersionLowerShriek ℓ (ringChar k)
      (Fact.out : ringChar k ≠ ℓ) k Λ (U := U.left) (X := X.left) j.left M T hT hmodels
    set_option backward.isDefEq.respectTransparency true in
      exact h.1
  have hc : constantModelBoundedConstructible Λ X.left
      (F.mapDerivedCategory.obj A.obj) := by
    refine ⟨F.bounded_mapDerivedCategory_obj A.property.1.1, fun q ↦ ?_⟩
    let e := (F.mapDerivedCategoryHomologyFunctorIso q).app A.obj
    have h := extend _ (A.property.1.2 q)
    obtain ⟨S, hS⟩ := (show IsConstantModelConstructible Λ X.left _ =
      IsFiniteConstantStratified Λ X.left _ from
        if_pos ⟨inferInstance, inferInstance⟩).mp h
    apply (show IsConstantModelConstructible Λ X.left _ =
      IsFiniteConstantStratified Λ X.left _ from if_pos ⟨inferInstance, inferInstance⟩).mpr
    refine ⟨S, fun t ↦ ?_⟩
    obtain ⟨C, hC⟩ := hS t
    refine ⟨C, fun r ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hC r
    exact ⟨P, hP, ⟨(upperStar Λ (C.f r)).mapIso
      ((upperStar Λ (S.immersion t)).mapIso e.symm) ≪≫ eP⟩⟩
  have hp := openImmersionTensorProjection (S := U.left) (X := X.left) Λ k j.left
  let projection := Classical.choice hp
  have ht : DerivedCategory.torAmplitudeIn _ a b (F.mapDerivedCategory.obj A.obj) := by
    apply (torAmplitudeIn_iff_derivedTensor Λ X.left a b _).mpr
    intro N
    have eN := (projection.app A.obj).app ((DerivedCategory.singleFunctor _ 0).obj N)
    change ((derivedTensor Λ X.left).obj (F.mapDerivedCategory.obj A.obj)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      F.mapDerivedCategory.obj (((derivedTensor Λ U.left).obj A.obj).obj
        ((upperStar Λ j.left).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj N))) at eN
    let es := ((upperStar Λ j.left).mapDerivedCategorySingleFunctor 0).app N
    have h := F.homologyConcentratedIn_mapDerivedCategory_obj
      ((torAmplitudeIn_iff_derivedTensor Λ U.left a b A.obj).mp htor
        ((upperStar Λ j.left).obj N))
    exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (eN ≪≫ F.mapDerivedCategory.mapIso
        (((derivedTensor Λ U.left).obj A.obj).mapIso es)).symm h
  refine ⟨⟨hc, a, b, ht⟩,
    F.homologyConcentratedIn_mapDerivedCategory_obj hcoh, ht, hc.1, ?_⟩
  intro q
  obtain ⟨S, hS⟩ := (show IsConstantModelConstructible Λ X.left _ =
    IsFiniteConstantStratified Λ X.left _ from
      if_pos ⟨inferInstance, inferInstance⟩).mp (hc.2 q)
  refine ⟨S, fun t ↦ ?_⟩
  let α := condensedPullbackHom Λ (S.immersion t)
  apply localFinitePresentation_of_comap (inv α)
  have h := HasFiniteConstantLocalModel.isLocallyFinitelyPresented Λ _ (hS t)
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((ProEtale.upperStar Ab.{u + 1} (S.immersion t)).mapMod
      (condensedRingObj Λ X.left)).obj
      ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj A.obj)))
  unfold upperStar at h
  exact localFinitePresentation_of_iso e h

end AlgebraicGeometry.ProEtale.CondensedRing
