/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Spaces
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# The contracted product of a torsor under change of coefficients

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ;
blueprint pushout-fibre quotient argument
(blueprint: def-sc-zariski-contracted-product-presentation).
-/

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Torsor

/-- A presentation of `T ∧ᴳ G'` as the sheaf quotient of `T × G'` by
`g • (t, h) = (g +ᵥ t, h - φ(g))`. The natural quotient map is invariant under that action
and equivariant for translation on the second factor. Its universal property against every
sheaf of sets is exactly the universal property of the sheafification of the orbit presheaf.
Source: Stacks, Lemma 02FQ; the blueprint's pushout-fibre quotient argument.
(blueprint: def-sc-zariski-contracted-product-presentation) -/
structure ZariskiContractedProductPresentation (X : AlgebraicGeometry.Scheme.{u})
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}} (φ : G ⟶ G')
    (T : Torsor G) (T' : Torsor G') where
  quotient (U : (Opens X)ᵒᵖ) : T.sheaf.obj.obj U → G'.obj.obj U → T'.sheaf.obj.obj U
  quotient_natural {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (t : T.sheaf.obj.obj U)
      (h : G'.obj.obj U) :
    T'.sheaf.obj.map f (quotient U t h) =
      quotient V (T.sheaf.obj.map f t) (G'.obj.map f h)
  quotient_invariant (U : (Opens X)ᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
      (h : G'.obj.obj U) :
    quotient U (T.vadd U g t) (h - φ.hom.app U g) = quotient U t h
  quotient_vadd (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U) (h k : G'.obj.obj U) :
    quotient U t (h + k) = T'.vadd U k (quotient U t h)
  universal (F : Sheaf (Opens.grothendieckTopology X) (Type (w)))
      (a : ∀ U : (Opens X)ᵒᵖ, T.sheaf.obj.obj U → G'.obj.obj U → F.obj.obj U)
      (hn : ∀ ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V) (t : T.sheaf.obj.obj U)
        (h : G'.obj.obj U), F.obj.map f (a U t h) =
          a V (T.sheaf.obj.map f t) (G'.obj.map f h))
      (hi : ∀ (U : (Opens X)ᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
        (h : G'.obj.obj U), a U (T.vadd U g t) (h - φ.hom.app U g) = a U t h) :
    ∃! l : T'.sheaf ⟶ F, ∀ (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U)
      (h : G'.obj.obj U), l.hom.app U (quotient U t h) = a U t h

end CategoryTheory.Sheaf.Torsor
