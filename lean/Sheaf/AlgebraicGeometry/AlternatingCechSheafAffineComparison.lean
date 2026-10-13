/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Sheaf.AlgebraicGeometry.AffineAlternatingCechModel
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine direct image of the increasing-tuple sheaf complex

Source: Stacks Project, Tags 02KG and 02KH, comparison of affine Čech complexes;
Tag 01FM, signed increasing tuples.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Direct image identifies the constructed sheaf complex with the affine section model.
Source: Stacks Project, Tag 02KG (affine module comparison), Tag 02KH, separated-case
proof before taking cohomology, and Tag 01FM (signed faces).
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-comparison).

Proof: Every increasing tuple has at least one entry. Its intersection is affine,
since f is separated over an affine scheme. The over-site restriction equivalence
identifies its intersection sheaf with j_* of G restricted to that intersection W.
Pushforward composition identifies f_* j_* with pushforward along W to Spec A.
Since W is affine and G is quasi-coherent, the tilde-global-sections counit identifies
this last module sheaf with tilde of Gamma(W,G), restricting scalars to A along f.
These isomorphisms are natural in inclusions of intersections: both restriction maps
are induced by the presheaf restriction of G, and the counit is natural. Pushforward
preserves products as a right adjoint. Tilde preserves finite products because it is
additive and preserves finite coproducts, which are biproducts in module categories.
Take the finite product of the component counit isomorphisms in each degree. Their
naturality and additivity show that they intertwine every signed face differential.
Their inverses satisfy the reverse chain-map identity by cancellation. Hence they
form an isomorphism of natural-degree complexes. Extend both sides by zero, using
the canonical compatibility of additive functors with extension, to obtain the
integer-degree comparison. An empty tuple type contributes a zero object on both
sides, so degrees past the cover size and r=0 require no additional hypotheses.
No covering assumption is used in this comparison. -/
theorem alternatingCechSheafComplex_affineComparison
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {r : ℕ} (U : Fin r → X.Opens) (haffine : ∀ i, IsAffineOpen (U i))
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    Nonempty (((Scheme.Modules.pushforward f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat) ≅
          affineAlternatingCechModel f U G) := by sorry

end AlgebraicGeometry
