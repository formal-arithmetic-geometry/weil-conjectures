/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Ordinary pro-etale operations with arbitrary constant coefficients

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules, and Tag 0H7J
(blueprint: def-weil-pbc-proetale-operations).

This supplies the arbitrary-constant-ring specialization of the published ring-sheaf
operations. The intrinsic finite-coefficient interface remains available.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The specified constant-section comparison is invertible for arbitrary rings.
Source: Stacks, Tag 0H7J (blueprint: def-weil-pbc-proetale-operations).
Proof: on sheaves of sets, inverse image preserves colimits and finite limits.
The underlying set sheaf of the constant ring is the coproduct of terminal set sheaves
indexed by its underlying set. Finite-product preservation transports its ring operations,
so inverse image preserves the constant ring sheaf. The comparison sends each constant
section to itself, so sheafification uniqueness identifies it with the specified map.
This is the canonical coefficient identification for the ordinary module operations. -/
theorem proEtaleConstantRingComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : IsIso (proEtaleCoefficientInverseImageMap f A) := by
  sorry

attribute [instance] proEtaleConstantRingComparison_isIso

/-- The coefficient identification fixed by the constant-section map, with no finiteness.
Source: Stacks, Tag 0H7J (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleConstantRingComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing Y A) ≅
      proEtaleConstantRing X A :=
  asIso (proEtaleCoefficientInverseImageMap f A)

/-- Ordinary module inverse image in the intrinsic constant-ring presentation.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev proEtaleConstantRingPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- Ordinary module direct image with the adjoint constant-section scalar action.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev proEtaleConstantRingPushforward (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleDirectImage f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- The tensor-unit-normalized adjunction of the arbitrary constant-ring operations.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev proEtaleConstantRingAdjunction (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f :=
  proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- Exact termwise descent to the same ordinary unbounded intrinsic derived category.
Source: Stacks, Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev proEtaleConstantRingDerivedPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  (proEtaleConstantRingPullback A f).mapDerivedCategory

end AlgebraicGeometry.Scheme
