/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.CategoryTheory.Sites.ZariskiContractedProductPresentation

/-!
# The fibre of a pushed-out Zariski extension

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ, pushout and fibre construction
(blueprint: lem-sc-torsor-h1-ext-pushout).
-/

universe uE

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Torsor

/-- Pushing out an extension by the constant integer sheaf changes its fibre over `1`
by contracted product. The maps `a` and `b` identify torsors with the two fibres, and `q`
presents the sheafification of the orbit presheaf. Its formula in the pushout fixes the
canonical identification, including the residual action.
Source: Stacks Project, Lemma 02FQ, proof by pushout and local lifts.

Proof: (1) In the abelian category of Zariski abelian sheaves
(`def-sc-topological-abelian-cohomology`), the cokernel of `g ↦ (j(g), -φ(g))`
is the pushout of `j` along `φ`: maps from the two summands agree on `G` exactly when
this relation is killed. Apply `lem-weil-pbc-pushout-short-exact-sequence` to get its
projection and short exactness.
(2) Locally, every section of the new fibre is represented by `(t,h)` with `p(t)=1`,
because the quotient epimorphism is stalkwise surjective
(`lem-sc-abelian-sheaf-short-exact-stalkwise`). Two pairs represent the same section
locally exactly when they differ by `(j(g), -φ(g))`. Thus the fibre has the universal
property of the sheafification of the orbit presheaf. Translation in the second factor
is the residual `G'`-action.
(3) Both fibres are torsors (`def-sc-gm-torsor`): stalkwise surjectivity of the projections
provides local lifts of `1`, and exactness makes the difference of two lifts a unique
section of the kernel (`lem-sc-abelian-sheaf-short-exact-stalkwise`). These fibre
identifications and the pair formula give the canonical identification of torsors.
(blueprint: lem-sc-torsor-h1-ext-pushout) -/
theorem zariski_torsor_extension_pushout (X : AlgebraicGeometry.Scheme.{uE})
    {G G' E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE}}
    (φ : G ⟶ G') (j : G ⟶ E)
    (p : E ⟶ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE}).obj
      (AddCommGrpCat.of (ULift.{uE} ℤ)))
    (hjp : j ≫ p = 0) (hE : (ShortComplex.mk j p hjp).ShortExact) :
    ∃ (p' : pushout j φ ⟶
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE}).obj
          (AddCommGrpCat.of (ULift.{uE} ℤ))),
      pushout.inl j φ ≫ p' = p ∧
      ∃ (hz : pushout.inr j φ ≫ p' = 0),
        (ShortComplex.mk (pushout.inr j φ) p' hz).ShortExact ∧
        ∃ (T : Torsor G) (T' : Torsor G')
          (a : ∀ U : (Opens X)ᵒᵖ, T.sheaf.obj.obj U → E.obj.obj U)
          (b : ∀ U : (Opens X)ᵒᵖ, T'.sheaf.obj.obj U → (pushout j φ).obj.obj U)
          (q : ZariskiContractedProductPresentation X φ T T'),
          (∀ ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V) (t : T.sheaf.obj.obj U),
            E.obj.map f (a U t) = a V (T.sheaf.obj.map f t)) ∧
          (∀ U : (Opens X)ᵒᵖ, Set.BijOn (a U) Set.univ
            {e | p.hom.app U e = (toSheafify (Opens.grothendieckTopology X)
              ((Functor.const (Opens X)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{uE} ℤ)))).app U ⟨1⟩}) ∧
          (∀ (U : (Opens X)ᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U),
            a U (T.vadd U g t) = a U t + j.hom.app U g) ∧
          (∀ ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V) (t : T'.sheaf.obj.obj U),
            (pushout j φ).obj.map f (b U t) = b V (T'.sheaf.obj.map f t)) ∧
          (∀ U : (Opens X)ᵒᵖ, Set.BijOn (b U) Set.univ
            {e | p'.hom.app U e = (toSheafify (Opens.grothendieckTopology X)
              ((Functor.const (Opens X)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{uE} ℤ)))).app U ⟨1⟩}) ∧
          (∀ (U : (Opens X)ᵒᵖ) (h : G'.obj.obj U) (t : T'.sheaf.obj.obj U),
            b U (T'.vadd U h t) = b U t + (pushout.inr j φ).hom.app U h) ∧
          (∀ (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U) (h : G'.obj.obj U),
            b U (q.quotient U t h) = (pushout.inl j φ).hom.app U (a U t) +
              (pushout.inr j φ).hom.app U h) := sorry

end CategoryTheory.Sheaf.Torsor
