/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison

/-! # Normalization of the source-open comparison at the whole scheme

Source: Stacks Project, Tag 0DJ9, the final application U = X.
(blueprint: lem-pc-single-complex-open-top).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The top-open comparison is the original comparison up to canonical isomorphisms.
Source: Stacks Project, Tag 0DJ9, conclusion of source-open induction.
(blueprint: lem-pc-single-complex-open-top).

Proof: The top-open immersion is an isomorphism. Its base change is an isomorphism,
and the other projection identifies the fibre product with X'. Derived pullback
along either isomorphism is an equivalence, with inverse the corresponding derived
direct image. The composition comparisons and these equivalences identify the
source and target of the top-open comparison with those of the original comparison.
The adjoint counit description of schemeDerivedBaseChangeMap, naturality of the
counits, and coherence of the composition comparisons identify the two arrows.
Conjugating an invertible morphism by isomorphisms is invertible. This works for
any commutative square and arbitrary derived objects, including the empty scheme;
it uses neither quasi-coherence nor the stalk hypothesis. -/
theorem singleComplexOpenComparison_top
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (htop : IsIso (singleComplexOpenComparison f f' g g' h K K' φ ⊤)) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' h K ≫
      (schemeDerivedDirectImage f').map φ) := by sorry

end AlgebraicGeometry
