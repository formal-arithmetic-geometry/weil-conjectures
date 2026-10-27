module

public import Sheaf.AlgebraicTopology.FreeBisimplexProjectiveResolutions
public import Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy

/-! # The prescribed universal signed shuffle is a homotopy equivalence

Source: Stacks Project, Tags 0649 and 064A, specialized to the free bisimplex
resolutions, and the signed lattice shuffle in the six-functor stability proof,
paragraph (3) (blueprint: lem-sfb-universal-shuffle-homotopy-inverse).

The generator equation characterizes the forward map of the homotopy equivalence.
Thus the derived isomorphism is the class of that prescribed signed shuffle.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped BigOperators

noncomputable section

namespace AlgebraicTopology.FreeBisimplex

/-- The pair of counting maps attached to a shuffle partition, encoded by the existing
lattice path. Its first coordinate at `k` counts horizontal steps before `k`, and its
second counts vertical steps before `k`. Source: the displayed formula for `α_μ, α_ν`
(blueprint: lem-sfb-universal-shuffle-homotopy-inverse). -/
def shufflePathArrow {a b : ℕ} (s : SimplexLatticeShuffle.LatticePath a b) :
    (⦋a + b⦌, ⦋a + b⦌) ⟶ (⦋a⦌, ⦋b⦌) :=
  (SimplexCategory.Hom.mk
      { toFun := fun k ↦ (s.val k).1
        monotone' := fun _ _ h ↦ (s.property.1 h).1 },
    SimplexCategory.Hom.mk
      { toFun := fun k ↦ (s.val k).2
        monotone' := fun _ _ h ↦ (s.property.1 h).2 })

/-- The prescribed finite signed shuffle on a summand's basis arrow, extended by
postcomposition. The lattice-path sign counts vertical-before-horizontal inversions,
hence is the sign of the permutation listing `μ` before `ν`.
Source: the displayed signed generator sum and its postcomposition extension
(blueprint: lem-sfb-universal-shuffle-homotopy-inverse). -/
def shuffleGenerator (a b : ℕ) (j : SimplexCategory × SimplexCategory)
    (α : (⦋a⦌, ⦋b⦌) ⟶ j) : (representable.{u} (⦋a + b⦌, ⦋a + b⦌)).obj j :=
  letI : Fintype (SimplexLatticeShuffle.LatticePath a b) := Fintype.ofFinite
    {s : Fin (a + b + 1) → Fin (a + 1) × Fin (b + 1) //
      Monotone s ∧ ∀ k, (s k).1.val + (s k).2.val = k.val}
  ∑ s : SimplexLatticeShuffle.LatticePath a b,
    SimplexLatticeShuffle.pathSign s • generator (shufflePathArrow s ≫ α)

/-- The universal signed shuffle, characterized on every basis arrow, has a natural
augmentation-preserving chain homotopy inverse, and gives the indicated derived isomorphism.
The input identifications and boundary/augmentation equations specify precisely the two
complexes of `lem-sfb-free-bisimplex-projective-resolutions`, without choosing unrelated
projective resolutions. Naturality is internal to the functor category.

Source: Stacks Project, Tags 0649 and 064A, with the prescribed combinatorial shuffle
(blueprint: lem-sfb-universal-shuffle-homotopy-inverse).

Proof: (1) The free-bisimplex projective-resolution theorem supplies projectivity and
augmented exactness for these generator-normalized complexes. The generator Yoneda
bijection extends the finite shuffle sums uniquely and naturally to diagram morphisms.
(2) Evaluate at each bisimplex: its basis arrows are the weakly increasing strings, and
the displayed shuffle is exactly `lem-sfb-simplex-lattice-shuffle-boundary`. That theorem
proves the chain-map identity and the augmentation equation, also for repeated vertices
and zero factor degrees. (3) Apply `lem-sfb-abelian-projective-resolution-lift` to the
identity on the constant integer diagram to obtain the reverse augmented chain map.
(4) The two composites have the same augmentations as the identities. Apply
`new-t4-augmented-resolution-lift-homotopy` with source and target respectively `P` and
`Q` to obtain both homotopies in the diagram category. (5) Extend by zero along
`n ↦ -n`. The two homotopy identities become inverse identities after localization in
`def-weil-abstract-derived-category`, giving the derived isomorphism with exactly the
specified forward map. -/
theorem universal_shuffle_homotopy_inverse
    [HasDerivedCategory.{w} (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u})]
    (P Q : ChainComplex (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}) ℕ)
    (p : ∀ n : ℕ, P.X n ≅ representable.{u} (⦋n⦌, ⦋n⦌))
    (q : ∀ n : ℕ, Q.X n ≅ totalTerm.{u} n)
    (εP : P.X 0 ⟶ (Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (εQ : Q.X 0 ⟶ (Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hP : ∀ (n : ℕ) (j : SimplexCategory × SimplexCategory)
      (α : (⦋n + 1⦌, ⦋n + 1⦌) ⟶ j),
      (p n).hom.app j ((P.d (n + 1) n).app j
        ((p (n + 1)).inv.app j (generator α))) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
        generator ((SimplexCategory.δ k, SimplexCategory.δ k) ≫ α))
    (hQ : ∀ (a b : ℕ) (j : SimplexCategory × SimplexCategory)
      (α : (⦋a⦌, ⦋b⦌) ⟶ j),
      (q (a + b - 1)).hom.app j ((Q.d (a + b) (a + b - 1)).app j
        ((q (a + b)).inv.app j (totalGenerator a b (a + b) rfl j α))) =
      totalBoundary a b j α)
    (hε : ∀ (j : SimplexCategory × SimplexCategory) (α : (⦋0⦌, ⦋0⦌) ⟶ j),
      εP.app j ((p 0).inv.app j (generator α)) = ULift.up (1 : ℤ) ∧
      εQ.app j ((q 0).inv.app j (totalGenerator 0 0 0 rfl j α)) = ULift.up (1 : ℤ)) :
    ∃ (e : HomotopyEquiv Q P)
      (eD : DerivedCategory.Q.obj (Q.extend ComplexShape.embeddingDownNat) ≅
        DerivedCategory.Q.obj (P.extend ComplexShape.embeddingDownNat)),
      (∀ (a b : ℕ) (j : SimplexCategory × SimplexCategory) (α : (⦋a⦌, ⦋b⦌) ⟶ j),
        (p (a + b)).hom.app j ((e.hom.f (a + b)).app j
          ((q (a + b)).inv.app j (totalGenerator a b (a + b) rfl j α))) =
        shuffleGenerator a b j α) ∧
      e.hom.f 0 ≫ εP = εQ ∧ e.inv.f 0 ≫ εQ = εP ∧
      eD.hom = DerivedCategory.Q.map
        (HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat) := by
  sorry

end AlgebraicTopology.FreeBisimplex
