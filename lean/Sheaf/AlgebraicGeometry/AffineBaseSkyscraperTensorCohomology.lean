/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.AffineRelativeStalkResolutionIso
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import WeilConjectures.Topology.RingedModuleSkyscraper
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Cohomology of the affine base-skyscraper tensor test

Source: Stacks Project, perfect.tex, Tag 0DHY, the affine stalk argument, and
cohomology.tex, Tag 09U9, exact stalks commuting with cohomology.
(blueprint: lem-trf-affine-base-skyscraper-tensor-cohomology).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u wB wT

open CategoryTheory

namespace AlgebraicGeometry

/-- For an arbitrary complex over A and an arbitrary R_p-module L, the actual stalk
of the cohomology of the relative derived tensor with the inverse image of the base
skyscraper is the cohomology of the localized module derived tensor. Scalars on the
left are restricted along the specified affine inverse-image germ map e_x.
No flatness, finiteness or boundedness hypothesis is imposed.

Source: Stacks Project, perfect.tex, Tag 0DHY, affine stalk argument; cohomology.tex,
Tag 09U9, exact stalks commute with cohomology.
(blueprint: lem-trf-affine-base-skyscraper-tensor-cohomology).

Proof:
1. Use the exact stalk-and-scalar-transport functor S_x of
   lem-trf-affine-relative-stalk-resolution-iso. Exactness preserves the kernel of d^i,
   the image of d^(i-1), and their quotient, giving S_x H^i(K) ≅ H^i(S_x K).
   Applied termwise it also preserves quasi-isomorphisms, so this identification is
   independent of the representative of K. Its left side is the actual module stalk
   with scalars restricted along e_x.
2. Specialize the derived comparison of lem-trf-affine-relative-stalk-resolution-iso
   to G = i_(f(x),*) L, using the affine germ identification on its coefficients.
   Apply H^i to that comparison and its inverse, then compose with Step 1.
   The result is an R_p-module isomorphism. Only degrees i-1, i, i+1 enter Step 1,
   so the argument works for every integer i and unbounded complexes. The sheaf
   and module tensor objects used here are the dependency's K-flat derived tensors.
-/
theorem nonempty_affineBaseSkyscraperTensorCohomologyIso
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (x : PrimeSpectrum A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    [HasDerivedCategory.{wB} (RingedSpace.Modules (AffineRelativeStalk.ringedSpace φ))]
    [HasDerivedCategory.{wT}
      (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal))]
    (L : ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal))
    (i : ℤ) :
    Nonempty
      ((AffineRelativeStalk.stalkFunctor φ x).obj
          ((DerivedCategory.homologyFunctor
            (RingedSpace.Modules (AffineRelativeStalk.ringedSpace φ)) i).obj
              (AffineRelativeStalk.tensorWithInverseImage φ M
                (AffineRelativeStalk.skyscraper φ x L))) ≅
        (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)) i).obj
            (AffineRelativeStalk.localizedTensor φ x M L)) := by
  sorry

end AlgebraicGeometry
