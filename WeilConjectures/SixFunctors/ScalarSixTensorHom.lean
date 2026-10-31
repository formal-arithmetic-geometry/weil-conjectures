/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtf
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

import WeilConjectures.SixFunctors.ScalarSixHomThick
import WeilConjectures.SixFunctors.ScalarSixHomGenerators
import WeilConjectures.SixFunctors.ListedCoefficientCtf
import WeilConjectures.SixFunctors.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ScalarSixAdmissibleThickness
import WeilConjectures.CategoryTheory.DerivedCategory.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory

/-! # Coefficient comparison for tensor and internal Hom

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/,
det-prop-scalar-six-tensor-hom.md, clauses (1)--(2)
(blueprint: det-prop-scalar-six-tensor-hom).

The tensorator is the existing K-flat derived extension-of-scalars tensorator.
The internal-Hom arrow is its evaluation mate, rather than an arbitrary isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical scalar internal-Hom comparison, the mate of the tensorator.
The library uses left evaluation `K ⊗ RHom(K,M) → M`. Under the Koszul symmetry,
its mate is equally the right-evaluation transpose in the blueprint: first apply
`scalarSixTensorIso` inversely and then scalar extension of evaluation.
Source: blueprint det-prop-scalar-six-tensor-hom (2), definition of v
(blueprint: det-prop-scalar-six-tensor-hom). -/
def scalarSixHomComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a X).obj (((derivedHom Λ.X X).obj (.op K)).obj M) ⟶
      ((derivedHom Λ'.X X).obj (.op ((scalarSixChange a X).obj K))).obj
        ((scalarSixChange a X).obj M) :=
  (Functor.LaxMonoidal.ihomComparison (scalarSixChange a X) K).natTrans.app M

set_option maxHeartbeats 1200000 in
-- Generation, inverse-image thickness, and coefficient transport share large native instances.
/-- Scalar extension is symmetric monoidal on the ambient unbounded categories, and
its evaluation-defined internal-Hom comparison is an isomorphism in Dctf for Dctf
arguments. The braided witness uses the canonical monoidal structure above and the
Koszul braidings of the existing symmetric derived structures.
Source: blueprint det-prop-scalar-six-tensor-hom (1)--(2)
(blueprint: det-prop-scalar-six-tensor-hom).

Proof:
1. Apply the existing derived braided extension-of-scalars construction. Its
underlying monoidal structure is definitionally scalarSixChangeMonoidal.
2. For fixed M let I be the invertibility locus of the native scalar Hom mate,
and let D be the intersection of bounded constructibility and finite Tor amplitude.
The native exactness calculation makes I triangulated; naturality makes it closed
under retracts. Admissible coefficient thickness and finite-Tor thickness make D
thick. Native contravariant Hom exactness makes the inverse image of D thick.
3. Intersect I with that inverse image. The locally closed generator calculation
puts every scalar-perfect generator in this intersection. The finite-coefficient
and nonfinite-coefficient generation theorems, respectively, express each K in
Dctf as a retract of a finite extension of shifts of these generators. Thus the
specified Hom mate is invertible and the unextended internal Hom belongs to Dctf.
4. Apply listedCoefficientCtf to that unextended Hom. The isomorphism from step 3
then transports bounded constructibility and finite Tor amplitude to the target.
The two remaining calculations are stated separately in ScalarSixHomThick and
ScalarSixHomGenerators; the assembly here uses exactly their displayed arrows. -/
theorem scalarSixTensorHom (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (∃ b : @Functor.Braided
      (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) _ _
      (DerivedCategory.braidedCategory' _)
      (DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X.left)) _ _
      (DerivedCategory.braidedCategory' _) (scalarSixChange a X.left),
      b.toMonoidal = scalarSixChangeMonoidal a X.left) ∧
    ∀ K M : ConstantModelConstructibleFiniteTor Λ.X X.left,
      IsIso (scalarSixHomComparison a X.left K.obj M.obj) ∧
      (constantModelBoundedConstructible Λ'.X X.left
        ((scalarSixChange a X.left).obj
          (((derivedHom Λ.X X.left).obj (.op K.obj)).obj M.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((scalarSixChange a X.left).obj
            (((derivedHom Λ.X X.left).obj (.op K.obj)).obj M.obj))) ∧
      (constantModelBoundedConstructible Λ'.X X.left
        (((derivedHom Λ'.X X.left).obj (.op ((scalarSixChange a X.left).obj K.obj))).obj
          ((scalarSixChange a X.left).obj M.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          (((derivedHom Λ'.X X.left).obj (.op ((scalarSixChange a X.left).obj K.obj))).obj
            ((scalarSixChange a X.left).obj M.obj))) := by
  constructor
  · let := Mod.extendScalarsMonoidal
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)
    refine ⟨(Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)).leftDerivedFunctorBraided
        (Mod.extendScalars_map_braiding_hom_δ _), rfl⟩
  · intro K M
    obtain ⟨hΛ, _, hchange⟩ := listedCoefficientCtf ell a _ha
    let I : ObjectProperty
        (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :=
      fun J ↦ IsIso (scalarSixHomComparison a X.left J M.obj)
    obtain ⟨hIt, hIr⟩ := scalarSixHom_isoLocus a X.left M.obj
    have : I.IsTriangulated := hIt
    have : I.IsStableUnderRetracts := hIr
    let D := constantModelBoundedConstructible Λ.X X.left ⊓
      DerivedCategory.finiteTorAmplitude (ModuleRingedComparison.internalModules Λ.X X.left)
    obtain ⟨hbc, hbcr⟩ := sfbAdmissibleConstructibleThickness ell Λ hΛ k X
    have : (constantModelBoundedConstructible Λ.X X.left).IsTriangulated := hbc
    have : (constantModelBoundedConstructible Λ.X X.left).IsStableUnderRetracts := hbcr
    have ht := constantModelConstructibleFiniteTor_wellDefined Λ.X X.left
    have : (DerivedCategory.finiteTorAmplitude
        (ModuleRingedComparison.internalModules Λ.X X.left)).IsTriangulated :=
      ht.2.2.2.2.2.2.2.1
    have : (DerivedCategory.finiteTorAmplitude
        (ModuleRingedComparison.internalModules Λ.X X.left)).IsStableUnderRetracts :=
      ht.2.2.2.2.2.2.2.2
    have : D.IsTriangulated := inferInstance
    have : D.IsStableUnderRetracts := ⟨fun r h ↦
      ⟨(constantModelBoundedConstructible Λ.X X.left).prop_of_retract r h.1,
        (DerivedCategory.finiteTorAmplitude _).prop_of_retract r h.2⟩⟩
    let H := (derivedHom Λ.X X.left).flip.obj M.obj
    obtain ⟨sH, hH⟩ := DerivedCategory.nativeInternalHom_contravariant_exact
      (ModuleRingedComparison.internalModules Λ.X X.left) M.obj
    let : H.CommShift ℤ := sH
    have : H.IsTriangulated := hH
    let R := (D.inverseImage H).unop
    have : R.IsTriangulated := inferInstance
    have : R.IsStableUnderRetracts := ⟨fun r h ↦ D.prop_of_retract (r.op.map H) h⟩
    let Q := I ⊓ R
    have : Q.IsTriangulated := inferInstance
    have : Q.IsStableUnderRetracts :=
      ⟨fun r h ↦ ⟨I.prop_of_retract r h.1, R.prop_of_retract r h.2⟩⟩
    have hgen : sfbPerfectScalarGenerator Λ X ≤ Q := by
      rintro J ⟨S, b, hb, P, hP, ⟨e⟩⟩
      exact Q.prop_of_iso e.symm (scalarSixHom_generator ell k a _ha X M S b hb P hP)
    have hgeneration : ∃ n : ℕ,
        (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
          ).retractClosure K.obj := by
      rcases hΛ with hfinite | hother
      · obtain ⟨A, hA, tA, dA, rA, hf, hn, ⟨e⟩⟩ := hfinite
        let := hA
        let := tA
        let := dA
        let := rA
        let := hf
        exact sfbFiniteScalarGeneration A e X K
      · exact sfbNonfiniteScalarGeneration ell hother k X K
    obtain ⟨n, hn⟩ := hgeneration
    have hclosure : (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure ≤ Q := by
      apply (ObjectProperty.retractClosure_le_iff _ Q).mpr
      apply ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂
      exact (ObjectProperty.shiftClosure_le_iff _ Q).mpr hgen
    obtain ⟨hi, hh⟩ := hclosure _ hn
    have hsource := hchange k X _ hh
    have : IsIso (scalarSixHomComparison a X.left K.obj M.obj) := hi
    have htarget := (constantModelConstructibleFiniteTor_wellDefined Λ'.X X.left)
    have : (constantModelBoundedConstructible Λ'.X X.left).IsClosedUnderIsomorphisms :=
      htarget.2.1
    have : (DerivedCategory.finiteTorAmplitude
        (ModuleRingedComparison.internalModules Λ'.X X.left)).IsClosedUnderIsomorphisms :=
      htarget.2.2.2.1
    refine ⟨hi, hsource, ?_⟩
    let e := asIso (scalarSixHomComparison a X.left K.obj M.obj)
    exact ⟨(constantModelBoundedConstructible Λ'.X X.left).prop_of_iso e hsource.1,
      (DerivedCategory.finiteTorAmplitude _).prop_of_iso e hsource.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing
