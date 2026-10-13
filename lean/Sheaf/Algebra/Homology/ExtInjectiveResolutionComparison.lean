/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Computing projective Ext using an injective resolution

Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite

namespace ModuleCat

/-- The complex `Hom(X,K)` as a functor contravariant in the module `X`.
Source: Stacks Project, Tag 0954, the Hom complexes used to compute local cohomology.
(blueprint: lem-sbc-ext-injective-resolution-comparison). -/
def homComplexDiagram {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj X := (((linearCoyoneda R (ModuleCat.{u} R)).obj X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  map f := (NatTrans.mapHomologicalComplex
    ((linearCoyoneda R (ModuleCat.{u} R)).map f) (ComplexShape.up ℕ)).app K
  map_id X := by
    ext n g
    rfl
  map_comp f g := by
    ext n h
    rfl

/-- Projectively defined Ext is the cohomology of Hom into an injective
resolution, naturally in the first argument.
Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2, the injective-resolution
computation of the Ext terms.
(blueprint: lem-sbc-ext-injective-resolution-comparison).

Proof: For a module X, choose a projective resolution P of X. Form the
first-quadrant double complex Hom(P,E). The augmentation from Hom(P,M)
is a quasi-isomorphism on total complexes because each P term is projective
and the augmented injective resolution is exact. The augmentation from
Hom(X,E) is likewise a quasi-isomorphism because each E term is injective
and the augmented projective resolution is exact. To check these two
quasi-isomorphisms directly, take the augmented total complex for each edge.
Its rows or columns are exact, including the augmentation in degree -1.
In a fixed total degree a cocycle has finitely many components. In the
column-exact case its component of smallest horizontal degree is a vertical
cycle. Lift it through the vertical differential and subtract the total
boundary of that lift. This removes that component and introduces at most
one in the next horizontal degree, one vertical degree lower. Repeat until
the vertical degree is -1, where injectivity of the augmentation forces the
remaining component to vanish. Thus the augmented total complex is acyclic.
Interchanging horizontal and vertical gives the row-exact case. The standard
sign in the total differential only changes the signs of the chosen lifts.
Consequently both edge maps induce cohomology isomorphisms. Mathlib's
ProjectiveResolution.isoExt identifies the first cohomology model with Ext.
For a morphism X' → X, lift it to the chosen projective resolutions.
The induced map of double complexes commutes with both augmentations, so
the resulting cohomology isomorphisms commute with precomposition.
Any two projective lifts are chain homotopic, and applying Hom and taking
cohomology kills their difference. The comparison is thus independent of
the lifts and supplies a natural isomorphism in X. In degree zero both
augmentations identify the kernels with Hom(X,M); zero modules cause no
exception. -/
theorem nonempty_ext_iso_injectiveResolution_homology
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (E : InjectiveResolution M) (q : ℕ) :
    Nonempty ((Ext R (ModuleCat.{u} R) q).flip.obj M ≅
      homComplexDiagram E.cocomplex ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q) := by sorry

end ModuleCat
