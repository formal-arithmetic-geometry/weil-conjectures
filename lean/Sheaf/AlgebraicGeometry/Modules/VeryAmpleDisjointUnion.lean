/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Very ampleness on a finite disjoint union

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-ample-positive-degree.md`,
proof, part (⇐) (blueprint: lem-pc-very-ample-disjoint-union).
-/

universe w v

open CategoryTheory

namespace AlgebraicGeometry

/-- Very ampleness of the restrictions to a finite nonempty clopen decomposition implies
very ampleness on the whole proper scheme.
Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-ample-positive-degree.md`,
proof, part (⇐) (blueprint: lem-pc-very-ample-disjoint-union).

Proof: (1) By `lem-pc-complete-linear-system-closed`, read very ampleness using a finite
basis of global sections, generating the module and inducing a closed immersion. Empty pieces
can be discarded; the empty whole scheme has the empty complete linear system.
(2) By the sheaf axiom and the pullback/restriction identification of
`lem-weil-pbc-open-immersion-module-pullback-restriction`, global sections split as the
finite direct sum of the sections on the pieces. Extend each piece's basis by zero.
(3) The nonvanishing locus of an extended section stays in its own piece. Quotients of
sections from different blocks vanish, while quotients in the same block are unchanged
(`lem-weil-pbc-nonvanishing-section-trivializes`). These sections generate the module.
(4) Apply `lem-weil-pbc-sections-morphism-to-proj-polynomial-ring` to this combined basis.
(5) On each standard chart, the preimage and coordinate ratios coincide with those of
the corresponding piece's closed immersion. The preimage is affine and the coordinate
ring map is surjective, by `lem-weil-pbc-proj-polynomial-twist-chart` and
`lem-weil-pbc-closed-immersion-affine-cover-criterion`.
(6) The affine-cover criterion makes the combined map a closed immersion, and its pullback
of `O(1)` is the original module. The combined basis makes this the complete linear system. -/
theorem isVeryAmple_of_finite_disjoint_union
    {K : Type w} [Field K] {Y : Scheme.{w}}
    (f : Y ⟶ Spec (.of K)) [IsProper f]
    (I : Type v) [Finite I] [Nonempty I] (U : I → Y.Opens)
    (hclosed : ∀ j : I, IsClosed (U j : Set Y))
    (hdisjoint : Pairwise (fun j k : I => Disjoint (U j) (U k)))
    (hcover : iSup U = ⊤)
    (hproper : ∀ j : I, IsProper ((U j).ι ≫ f))
    (M : Y.Modules) (hM : M.IsInvertible)
    (hvery : ∀ j : I, IsVeryAmple ((U j).ι ≫ f)
      ((Scheme.Modules.tensorPullback (U j).ι).obj M)) :
    IsVeryAmple f M := by
  sorry

end AlgebraicGeometry
