/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteEtaleGenerator
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FiniteExtensionClosure
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite-coefficient generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-route-sfb-finite-scalar-generation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard upperStarFromPoint CondensedRing.upperStar
  CategoryTheory.Sheaf.monoidalCategory

set_option maxHeartbeats 2000000 in
-- The composite realization carries large canonical coefficient and derived-category instances.
attribute [-instance] CategoryTheory.Sheaf.monoidalCategory in
/-- The proof of `sfbFiniteScalarGeneration`, elaborated without the generic sheaf
monoidal instance so that shift-additivity instance search stays small.
Source: blueprint det-prop-scalar-six-ctf (1), generators
(blueprint: lem-route-sfb-finite-scalar-generation). -/
private theorem sfbFiniteScalarGeneration_aux {Λ : ScalarSixRing.{u}}
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := {}
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let := heR
  let B := ULift.{u + 1} A
  let R := sfbFiniteScalarRealization A e eR X.left
  let P := sfbPerfectScalarGenerator Λ X
  let G : ObjectProperty (Etale.DerivedCategoryModule B X.left) := fun M ↦
    ∃ (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
      (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)),
      FlatModelEtaleLisseProjective B L ∧
      Nonempty (M ≅ (DerivedCategory.singleFunctor _ 0).obj
        ((flatModelEtaleExtension B a ha).obj L))
  have generators : ∀ M, G M → P (R.obj M) := by
    rintro M ⟨S, a, ha, L, hL, ⟨i⟩⟩
    obtain ⟨T, b, hb, Q, hQ, ⟨j⟩⟩ :=
      sfbFiniteScalarEtaleGenerator A e eR X S a ha L hL
    exact ⟨T, b, hb, Q, hQ, ⟨R.mapIso i ≪≫ j⟩⟩
  let : Zero (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    HasZeroObject.zero' _
  let L₀ : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} B) := 0
  have hL₀ : FlatModelEtaleLisseProjective B L₀ := by
    refine ⟨IsLocallyConstantSheaf.of_isZero (isZero_zero _), fun Ω _ _ x ↦ ?_⟩
    have hz := Functor.map_isZero ((pointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} B)) (isZero_zero _)
    have := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, inferInstance⟩
  have hG₀ : G ((DerivedCategory.singleFunctor _ 0).obj
      ((flatModelEtaleExtension B (𝟙 X.left) inferInstance).obj L₀)) :=
    ⟨X.left, 𝟙 X.left, inferInstance, L₀, hL₀, ⟨Iso.refl _⟩⟩
  let : G.Nonempty := ⟨_, hG₀⟩
  let : P.Nonempty := ⟨_, generators _ hG₀⟩
  let (_ : ℤ) : MonObj (condensedRingObj Λ.X X.left) :=
    (upperStarFromPoint X.left).monObjObj Λ.X
  let (_ : ℤ) : MonObj (condensedRingObj (Profinite.continuousMapRingObj A) X.left) :=
    (upperStarFromPoint X.left).monObjObj (Profinite.continuousMapRingObj A)
  have : ∀ n : ℤ, (shiftFunctor
      (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) n).Additive :=
    fun _ ↦ inferInstance
  have : ∀ n : ℤ, (shiftFunctor
      (DerivedCategory (ModuleRingedComparison.internalModules
        (Profinite.continuousMapRingObj A) X.left)) n).Additive :=
    fun _ ↦ inferInstance
  let : (shriekCoefficientTransport e.symm X.left).IsTriangulated :=
    (shriekCoefficientIso_transport e.symm X.left).2.1
  let : R.CommShift ℤ := inferInstance
  have : R.IsTriangulated := inferInstance
  obtain ⟨M, hM, ⟨i⟩⟩ := sfbFiniteScalarEtaleOrigin A e eR X K
  have hgen : G.triangEnvelope M := by
    apply Eq.mp (congrFun (etale_flatConstructible_thickGeneration X.left B) M)
    obtain ⟨hc, ht⟩ := hM
    obtain ⟨a, b, hab, hv⟩ := hc.2
    obtain ⟨c, d, htor⟩ := ht
    refine ⟨hc.1, ⟨a, b, hab, hv⟩, min c d, d, min_le_right _ _, ?_⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (htor.mono (min_le_left c d) le_rfl)
  have : (P.triangEnvelope.inverseImage R).IsStableUnderRetracts :=
    ⟨fun r h ↦ P.triangEnvelope.prop_of_retract (r.map R) h⟩
  have hinc : G ≤ P.triangEnvelope.inverseImage R := fun M hM ↦
    P.le_triangEnvelope _ (generators M hM)
  have hR : P.triangEnvelope (R.obj M) :=
    (ObjectProperty.triangEnvelope_le_iff G).mpr hinc M hgen
  exact ObjectProperty.triangEnvelope_le_finiteExtensions P K.obj
    (P.triangEnvelope.prop_of_iso i hR)


/-- Finite-coefficient generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-route-sfb-finite-scalar-generation).

Proof in words: choose the finite-discrete constant-ring isomorphism eR and let R_X be the
specified realization sfbFiniteScalarRealization (étale comparison pullback, constant-ring
module encoding, restriction along e). By sfbFiniteScalarEtaleOrigin, K.obj ≅ R_X(M) for an
étale bounded constructible finite-Tor M. Since X is Noetherian, the étale thick-generation
clause of etale_flatConstructible_thickGeneration (Tor interval normalized with min) puts M
in the thick envelope of the étale generators a_!L[0], L lisse with finite projective stalks;
the zero sheaf is such a generator, so the class is nonempty. R_X is triangulated, and by
sfbFiniteScalarEtaleGenerator it sends each generator to a canonical scalar-perfect
generator, so the inverse image of the scalar thick envelope is thick and contains the
étale generators: R_X(M), hence K.obj, lies in the scalar thick envelope. Finally
triangEnvelope_le_finiteExtensions turns thick-envelope membership into a retract of an
n-fold extension product of shifted generators. The zero ring and empty strata need no
exclusion. -/
theorem sfbFiniteScalarGeneration {Λ : ScalarSixRing.{u}}
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj :=
  sfbFiniteScalarGeneration_aux A e X K

end AlgebraicGeometry.ProEtale.CondensedRing
