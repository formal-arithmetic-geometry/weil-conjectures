/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Spaces
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Binary contracted products of Zariski torsors

Source: blueprint `sec-curve-estimates/sk-prop-hilbert90/lem-sc-torsor-h1.md`,
contracted-product group law (blueprint: def-sc-binary-contracted-product-presentation).
-/

@[expose] public section

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Torsor

/-- A sheaf quotient presentation of `P ∧ Q = (P × Q)/G`. The quotient is invariant under
`(x,y) ↦ (g+x,-g+y)` and its residual action comes from the first factor. Universality
against all sheaves of sets specifies the sheaf quotient, rather than the sectionwise
orbit presheaf. Source: blueprint `lem-sc-torsor-h1`, contracted-product group law.
(blueprint: def-sc-binary-contracted-product-presentation) -/
structure BinaryContractedProductPresentation (X : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}}
    (P Q R : Torsor G) where
  quotient (U : (Opens X)ᵒᵖ) : P.sheaf.obj.obj U → Q.sheaf.obj.obj U → R.sheaf.obj.obj U
  natural {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
      (x : P.sheaf.obj.obj U) (y : Q.sheaf.obj.obj U) :
    R.sheaf.obj.map f (quotient U x y) =
      quotient V (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y)
  invariant (U : (Opens X)ᵒᵖ) (g : G.obj.obj U)
      (x : P.sheaf.obj.obj U) (y : Q.sheaf.obj.obj U) :
    quotient U (P.vadd U g x) (Q.vadd U (-g) y) = quotient U x y
  equivariant (U : (Opens X)ᵒᵖ) (g : G.obj.obj U)
      (x : P.sheaf.obj.obj U) (y : Q.sheaf.obj.obj U) :
    quotient U (P.vadd U g x) y = R.vadd U g (quotient U x y)
  universal (F : Sheaf (Opens.grothendieckTopology X) (Type w))
      (a : ∀ U : (Opens X)ᵒᵖ, P.sheaf.obj.obj U → Q.sheaf.obj.obj U → F.obj.obj U)
      (hn : ∀ ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V)
        (x : P.sheaf.obj.obj U) (y : Q.sheaf.obj.obj U),
        F.obj.map f (a U x y) = a V (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y))
      (hi : ∀ (U : (Opens X)ᵒᵖ) (g : G.obj.obj U)
        (x : P.sheaf.obj.obj U) (y : Q.sheaf.obj.obj U),
        a U (P.vadd U g x) (Q.vadd U (-g) y) = a U x y) :
    ∃! l : R.sheaf ⟶ F, ∀ (U : (Opens X)ᵒᵖ)
      (x : P.sheaf.obj.obj U) (y : Q.sheaf.obj.obj U),
      l.hom.app U (quotient U x y) = a U x y

end CategoryTheory.Sheaf.Torsor
