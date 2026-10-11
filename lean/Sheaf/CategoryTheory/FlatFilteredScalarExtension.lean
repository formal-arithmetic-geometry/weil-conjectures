/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Scalar extension of filtered complexes

Source: Stacks Project, Homology, Tag 012K; Cohomology of Schemes, Tag 02KH
(blueprint: def-pc-flat-filtered-scalar-extension).
-/

universe uS vS wS

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {A : Type uS} {B : Type vS} [CommRing A] [CommRing B]

/-- The usual tensor scalar-extension functor, with additivity exposed globally.
Source: Stacks, Tag 02KH (blueprint: def-pc-flat-filtered-scalar-extension). -/
noncomputable abbrev filteredScalarFunctor (φ : A →+* B) :=
  extendScalars.{uS, vS, max uS vS wS} φ

/-- Additivity of tensor scalar extension follows from its adjunction.
Source: Stacks, Tag 02KH (blueprint: def-pc-flat-filtered-scalar-extension). -/
noncomputable instance filteredScalarFunctor_additive (φ : A →+* B) :
    (filteredScalarFunctor.{uS, vS, wS} φ).Additive :=
  (extendRestrictScalarsAdj.{max uS wS, uS, vS} φ).left_adjoint_additive

/-- The scalar-extension adjunction at the common module universe.
Source: Stacks, Tag 02KH (blueprint: def-pc-flat-filtered-scalar-extension). -/
noncomputable instance filteredScalarFunctor_isLeftAdjoint (φ : A →+* B) :
    (filteredScalarFunctor.{uS, vS, wS} φ).IsLeftAdjoint :=
  (extendRestrictScalarsAdj.{max uS wS, uS, vS} φ).isLeftAdjoint

/-- Termwise scalar extension, also for the bigraded page complexes.
Source: Stacks, Tag 02KH (blueprint: def-pc-flat-filtered-scalar-extension). -/
noncomputable def filteredScalarComplex (φ : A →+* B)
    {ι : Type*} (c : ComplexShape ι) :=
  (filteredScalarFunctor.{uS, vS, wS} φ).mapHomologicalComplex c

/-- The induced filtration consists of the images of the tensored step inclusions.
Flatness makes these maps monomorphisms, so these are the actual tensored subcomplexes.
Source: Stacks, Tags 012K and 02KH (blueprint: def-pc-flat-filtered-scalar-extension). -/
noncomputable def filteredScalarObject (φ : A →+* B)
    (U : FilteredObject (CochainComplex (ModuleCat.{max uS vS wS} A) ℤ)) :
    FilteredObject (CochainComplex (ModuleCat.{max uS vS wS} B) ℤ) where
  obj := (filteredScalarComplex.{uS, vS, wS} φ (.up ℤ)).obj U.obj
  filtration := {
    step := fun p ↦ imageSubobject
      ((filteredScalarComplex.{uS, vS, wS} φ (.up ℤ)).map (U.filtration.step p).arrow)
    antitone_step := by
      intro p q hpq
      have h := U.filtration.antitone_step hpq
      dsimp only
      rw [← Subobject.ofLE_arrow h, Functor.map_comp]
      exact imageSubobject_comp_le _ _ }

/-- Scalar extension preserves a finite filtration.
Source: Stacks, Tags 012K and 02KH (blueprint: def-pc-flat-filtered-scalar-extension).
Proof: choose the indices where the original filtration is the full and zero subcomplex.
At the first index the inclusion is an isomorphism, hence so is its tensor extension;
its image is the full object. At the second the inclusion has zero source, tensor
extension preserves zero objects, and its image is zero. The image inclusions are
antitone by factorization of consecutive step maps, as in filteredScalarObject. -/
theorem filteredScalarObject_isFinite (φ : A →+* B)
    (U : FilteredObject (CochainComplex (ModuleCat.{max uS vS wS} A) ℤ))
    (hU : U.filtration.IsFinite) :
    (filteredScalarObject.{uS, vS, wS} φ U).filtration.IsFinite := by
  sorry

/-- Exactness of flat scalar extension at arbitrary module universes.
The existing Mathlib theorem specializes to modules in the ring universe.
Source: Stacks, Tag 02KH (blueprint: def-pc-flat-filtered-scalar-extension).
Proof: injectivity is preserved because B is a flat A-module; tensor is right exact
by its extension-restriction adjunction. Hence tensor preserves kernels and cokernels
of module maps, degree by degree, and therefore finite limits in an abelian category.
This argument is independent of the universes of the rings and module carriers. -/
theorem filteredScalarFunctor_preservesFiniteLimits (φ : A →+* B) (hφ : φ.Flat) :
    PreservesFiniteLimits (filteredScalarFunctor.{uS, vS, wS} φ) := by
  sorry

/-- The canonical flat cohomology comparison, inverse to exact-functor homology comparison.
This applies to ordinary and bigraded complexes alike.
Source: Stacks, Tag 02KH (blueprint: def-pc-flat-filtered-scalar-extension). -/
noncomputable def flatFilteredHomologyIso (φ : A →+* B) (hφ : φ.Flat)
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{max uS vS wS} A) c) (i : ι) :
    (filteredScalarFunctor.{uS, vS, wS} φ).obj (K.homology i) ≅
      ((filteredScalarComplex.{uS, vS, wS} φ c).obj K).homology i := by
  letI : PreservesFiniteLimits (filteredScalarFunctor.{uS, vS, wS} φ) :=
    filteredScalarFunctor_preservesFiniteLimits φ hφ
  exact ((K.sc i).mapHomologyIso (filteredScalarFunctor.{uS, vS, wS} φ)).symm

end ModuleCat
