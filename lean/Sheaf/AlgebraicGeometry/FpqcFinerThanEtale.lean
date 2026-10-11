module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Every small étale covering family is an fpqc covering

Source: Stacks Project, Topologies, Tag 022C, lines 3043--3077;
(blueprint: lem-weil-pbc-fpqc-finer-than-etale).
-/

@[expose] public section

universe v u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/--
Every covering family in the small étale site is an fpqc covering
(Stacks, Tag 022C; (blueprint: lem-weil-pbc-fpqc-finer-than-etale)).

The family `f i : Z i ⟶ U` is a covering family of the small étale site `T.smallEtaleTopology`
(the sieve it generates covers `U`); the conclusion is that the underlying morphisms of schemes
`(f i).left : (Z i).left ⟶ U.left` form an fpqc covering, i.e. the presieve they generate belongs
to Mathlib's `Scheme.fpqcPrecoverage` (flat, jointly surjective, and every affine open of the
target is covered by the images of finitely many quasi-compact opens of the sources).

Proof (Tag 022C): each `f i` is étale by the definition of the covering families of `T_Et`,
hence flat. Over an affine open `V ⊆ U` the restrictions `f i⁻¹(V) → V` are étale (open
immersions are étale; composition and cancellation) and jointly surjective; by the affine
refinement lemma for étale coverings of an affine scheme (Tag 0218) finitely many affine opens
`V_j ⊆ U_{i_j}` have images with union exactly `V`. These are the two clauses of an fpqc covering.
-/
theorem fpqcCover_of_smallEtaleCover
    (T : Scheme.{u}) {U : T.Etale} {ι : Type v} {Z : ι → T.Etale} (f : ∀ i, Z i ⟶ U)
    (hf : Sieve.ofArrows Z f ∈ T.smallEtaleTopology U) :
    Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      Scheme.fpqcPrecoverage U.left := by
  sorry

end AlgebraicGeometry.Scheme
