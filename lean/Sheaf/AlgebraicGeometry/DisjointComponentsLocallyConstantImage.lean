/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-! # Local constancy of direct image from disjoint components

Source: smooth purity blueprint, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-disjoint-components-locally-constant-image).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Assemble locally constant component direct images along a finite disjoint open cover.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-disjoint-components-locally-constant-image).

Proof: For each etale test scheme over Y, base change the disjoint open cover of X.
The sheaf axiom identifies sections over the resulting scheme with the product of
sections over these disjoint components: intersections are empty and an abelian sheaf
has a unique section on the empty scheme. These restriction identifications commute
with maps of test schemes, giving an isomorphism from the underlying direct image to
the finite product of the underlying component direct images. Choose a trivializing
etale cover for each factor. Their finite fibre-product refinement covers Y. On every
member all factors are constant; the constant-sheaf functor preserves finite products
because etale sheafification is left exact. Hence their product is constant. Restrict
the displayed isomorphism to this refinement and transport constancy. For n = 0 the
cover condition implies X is empty; every test-object pullback is empty, so direct
image is the terminal set sheaf, the constant singleton sheaf. -/
theorem isLocallyConstant_disjoint_components_directImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (W : Fin n → X.Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hcomponents : ∀ i, IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} ((W i).ι ≫ f)).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (W i).ι).obj E)))) :
    IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E)) := by sorry

end AlgebraicGeometry.Scheme
