/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomContinuityOn
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective

/-! # Affine-open base case for continuity of perfect Hom
Source: Stacks Project, perfect.tex, Tag 09RE, affine case of lemma-descend-homomorphisms.
(blueprint: lem-pc-perfect-hom-continuity-affine).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The open-local continuity condition holds on affine opens.
Source: Stacks Project, perfect.tex, Tag 09RE, affine case.
(blueprint: lem-pc-perfect-hom-continuity-affine).

Proof: Let t : Y → X present the affine open U. The open immersion identifies Y
with U, so Y is affine. Write Y = Spec B_i. Its base changes have rings
B_j = B_i ⊗_{R_i} R_j and B = B_i ⊗_{R_i} c.pt; tensor extension preserves the
ring colimit. Perfect complexes have quasi-coherent cohomology. Apply
`perfect_iff_affine_bounded_projective` and the affine quasi-coherent derived
equivalence to represent both by bounded finite-projective B_i-complexes E and K.
Their terms are projective, hence flat, so ordinary tensor computes all derived
pullbacks. The termwise tilde comparison identifies chain maps and homotopies
with sheaf-derived maps, and its naturality identifies scalar-extension transport
with the counit-pinned composition conjugations in `perfectStageMap` and
`perfectLimitMap`. Apply `affine_perfect_hom_colimit` to this identified diagram.
The tail above any j₀ ≥ i is directed and cofinal: a common upper bound of j₀ and
any stage supplies cofinality. Thus bijectivity gives a representative above j₀.
If two images agree, injectivity and the filtered-set colimit equality criterion
give equality at a common later stage k. Composition coherence transports that
equality to every l ≥ k. This proves both clauses for every perfect pair on Y,
as required by `PerfectHomContinuityOn`. The empty affine scheme is covered as
well: its derived category is zero, so both conclusions also hold directly. -/
theorem perfect_hom_continuity_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    PerfectHomContinuityOn R c i X s U := by sorry

end AlgebraicGeometry
