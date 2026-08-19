/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# The small affine étale site, in `CostructuredArrow` form

`AlgebraicGeometry.Scheme.AffineEtale` is a `def`, so mathlib's
`EssentiallySmall.{u} S.AffineEtale` is not found by instance search for the unfolded
`MorphismProperty.CostructuredArrow @Etale ⊤ Scheme.Spec S`, which is the form in which
the small affine `P`-site appears in `Mathlib.AlgebraicGeometry.Sites.Affine` (and hence
in the general-`P` statements of `WeilConjectures.CategoryTheory.GrothendieckAbelian`).
This file records the unfolded instance.

Note that it is the *affine* small étale site that is essentially small: the small étale
site `S.Etale` itself is **not**, see the module docstring of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The small affine étale site of `S`, in the `MorphismProperty.CostructuredArrow` form
used by `Mathlib.AlgebraicGeometry.Sites.Affine`, is essentially small. This is mathlib's
`EssentiallySmall.{u} S.AffineEtale` with `S.AffineEtale` unfolded. -/
instance essentiallySmall_costructuredArrow_spec_etale (S : Scheme.{u}) :
    EssentiallySmall.{u} (MorphismProperty.CostructuredArrow @Etale ⊤ Scheme.Spec S) :=
  inferInstanceAs (EssentiallySmall.{u} S.AffineEtale)

end AlgebraicGeometry.Scheme
