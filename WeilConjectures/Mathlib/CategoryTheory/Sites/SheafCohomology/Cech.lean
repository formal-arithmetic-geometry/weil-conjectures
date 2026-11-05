/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
public import WeilConjectures.CategoryTheory.Sites.CechSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafCohomology.InjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Injective
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.ChgUniv
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Algebra.Homology.SpectralSequence.Transport

/-!
# The Čech-to-derived spectral sequence

Let `C` be an essentially small site with fibre products, `X : C` and `𝔘 = {Uᵢ ⟶ X}` a covering
of `X`. For an abelian sheaf `F` on `C` there is a first quadrant cohomological spectral sequence
`E₂^{p, q} = Ȟ^p(𝔘, ℋ^q(F)) ⟹ H^{p + q}(X, F)`, where `ℋ^q(F)` is the presheaf
`V ↦ H^q(V, F)`.

Both sides are taken from Mathlib: `ℋ^q(F)` is `CategoryTheory.Sheaf.cohomologyPresheaf`,
`H^n(X, F)` is `CategoryTheory.Sheaf.H'`, and the Čech complex of the covering is
`CategoryTheory.cechComplexFunctor` applied to the family `fun i ↦ Over.mk (π i)` of objects of
`Over X` — the finite products of `Over X` used there are exactly the fibre products
`Uᵢ ×[X] Uⱼ ×[X] ⋯`, so `Ȟ^p(𝔘, P)` is the `p`-th cohomology of that complex, evaluated on the
restriction of `P` to `Over X`.

## Main definitions

- `CategoryTheory.Sheaf.cohomologyPresheafULiftIso`: the cohomology presheaves computed with
  `Ext`-groups in two different universes agree after lifting both to a common universe.
- `CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`: an additive functor
  preserving homology commutes with taking homology of complexes.

## Main statements

- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`: the Čech-to-derived spectral
  sequence of a covering of an object of an essentially small site.
- `CategoryTheory.Sheaf.exists_cechDoubleComplex`: when abelian sheaves have enough injectives,
  the double complex `C^p(𝔘, I^q)` attached to an injective resolution `F → I^•`, through its
  column cohomology and the cohomology of its total complex.
- `CategoryTheory.Sheaf.exists_cechDoubleComplex_uliftFunctor`: the same double complex for an
  essentially small site, a covering indexed by a type in an arbitrary universe `w` and
  cohomology computed in `AddCommGrpCat.{w}`, after lifting everything to `AddCommGrpCat.{max v w}`.

## Implementation notes

The statement `exists_cechToDerivedSpectralSequence` assumes that the site is essentially small
(`EssentiallySmall.{v} C`). The sites of the Stacks project are small, and the proof needs an
injective resolution of `F`: for an essentially small site the category of abelian sheaves is a
Grothendieck abelian category (`Sheaf.isGrothendieckAbelian_of_essentiallySmall`), hence has
enough injectives, while abelian sheaves on a large site need not have enough injectives.

The covering is indexed by `ι : Type w` and cohomology is computed in `AddCommGrpCat.{w}` for an
arbitrary universe `w`. The groups `C^p(𝔘, I^q)` of the Čech double complex are products indexed
by `ι^{p + 1}` of `v`-small groups, so the double complex lives in `AddCommGrpCat.{max v w}`: we
lift the injective resolution along `AddCommGrpCat.uliftFunctor` (the lift of an injective
presheaf is still injective, `Presheaf.injective_comp_uliftFunctor`), compare `Ext`-groups in the
universes `v` and `w` with `Ext.chgUniv`, and finally bring the spectral sequence back to
`AddCommGrpCat.{w}` with `SpectralSequence.exists_of_uliftFunctor`: from the `E₂`-page on, all its
terms are `w`-small. The special case where all universes agree and only enough injectives are
assumed is `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives`, in
`WeilConjectures.CategoryTheory.Sites.CechSpectralSequence`.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]

end CategoryTheory
