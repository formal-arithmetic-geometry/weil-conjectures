module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.Group.Basic
import Sheaf.RepresentationTheory.DiscreteRep

/-!
# The cyclic permutation complex after a square-order lift

Source: ILO, Expose XVI, proof of Proposition 3.4.5, pp.247--248; the finite-level
replacement by an explicit quasi-isomorphism roof in the DAG proof
(blueprint: lem-per-cyclic-square-permutation-complex-splitting).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace Rep.CyclicSquare

/-- Reduction from the square-order additive cyclic group to the prime-order group.
Source: ILO XVI 3.4.5, root tower, p.247, finite-level refinement in the DAG proof.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
def reduction (ℓ : ℕ) : ZMod (ℓ ^ 2) →+* ZMod ℓ :=
  ZMod.castHom (by simpa only [pow_two] using dvd_mul_right ℓ ℓ) (ZMod ℓ)

/-- Translation on functions on the quotient: `(c • h)(q) = h(q - π(c))`.
`Multiplicative` only changes the notation for the additive cyclic group.
Source: ILO XVI 3.4.5, pp.247--248, finite-level refinement in the DAG proof.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
def translation (ℓ : ℕ) :
    Representation (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))) (ZMod ℓ → ZMod ℓ) where
  toFun c :=
    { toFun := fun h q ↦ h (q - reduction ℓ c.toAdd)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_one' := by
    ext h q
    simp [reduction]
  map_mul' c d := by
    ext h q
    change h (q - reduction ℓ (c.toAdd + d.toAdd)) =
      h (q - reduction ℓ c.toAdd - reduction ℓ d.toAdd)
    simp only [map_add, sub_sub]

/-- The discrete continuous permutation module `Map(Q,A)` with its specified action.
Source: ILO XVI 3.4.5, pp.247--248, finite-level refinement in the DAG proof.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
def permutationModule (ℓ : ℕ) :
    DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))) :=
  ⟨Rep.of (translation ℓ), fun _ ↦ isOpen_discrete _⟩

/-- The coefficient module with trivial cyclic action.
Source: ILO XVI 3.4.5, pp.247--248, finite-level refinement in the DAG proof.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
def trivialModule (ℓ : ℕ) :
    DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))) :=
  ⟨Rep.trivial (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))) (ZMod ℓ),
    fun _ ↦ isOpen_discrete _⟩

/-- The equivariant differential `τ - 1`, with `τ` the additive element one.
Source: ILO XVI 3.4.5, pp.247--248, finite-level refinement in the DAG proof.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
def differential (ℓ : ℕ) : permutationModule ℓ ⟶ permutationModule ℓ :=
  ObjectProperty.homMk
    ((permutationModule ℓ).obj.applyAsHom (Multiplicative.ofAdd 1) - 𝟙 _)

/-- The actual two-term cochain complex, in degrees zero and one, with `d⁰ = τ - 1`.
All remaining objects and differentials are zero by `HomologicalComplex.double`.
Source: ILO XVI 3.4.5, pp.247--248, finite-level refinement in the DAG proof.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
def permutationComplex (ℓ : ℕ)
    [h : Abelian (DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))))] :
    @CochainComplex (DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))))
      _ (@Preadditive.preadditiveHasZeroMorphisms _ _ h.toPreadditive) ℤ _ _ :=
  @HomologicalComplex.double _ _
    (@Preadditive.preadditiveHasZeroMorphisms _ _ h.toPreadditive) _ _ _
    (differential ℓ) ℤ (ComplexShape.up ℤ) 0 1 rfl

/-- The permutation complex splits in the ordinary derived category after the square-order lift.
Source: ILO XVI, proof of Proposition 3.4.5, pp.247--248, with the explicit finite-level
roof in the DAG proof. Proof plan:
1. Use `lem-exc-discrete-modules-abelian-structure` to compute kernels and cokernels
   on underlying modules; all stabilizers are open because the cyclic group is discrete.
2. For `S = C,Q`, translation minus identity has constants as kernel and the zero-sum
   functions as image. Summation is onto, as witnessed by the delta function at zero.
   Partial sums give a preimage of every zero-sum function.
3. Define `p : Map(C,A) → Map(Q,A)` by summing over reduction fibres. It is equivariant,
   commutes with translation, kills constants (each fibre has ℓ elements), and preserves sums.
4. Form the roof complex `Z` in degrees -1,0,1 with terms `A`, `A ⊕ Map(C,A)`, `Map(C,A)`
   and differentials `a ↦ (0,const a)` and `(a,r) ↦ (τ-1)r`. Map it to the zero-differential
   complex `T` by projection and summation, and to `K` by `(a,r) ↦ const a + p(r)` and `p`.
5. The calculations in step 2 identify both maps on H⁰ and H¹ with the identity of A;
   all other cohomology vanishes. Thus both maps are quasi-isomorphisms.
6. Invert them under `DerivedCategory.Q`. The resulting roof gives an isomorphism
   from K to `A[0] ⊕ A[-1]`. No canonical choice or splitting of complexes is asserted.
(blueprint: lem-per-cyclic-square-permutation-complex-splitting) -/
theorem permutationComplex_splitting (ℓ : ℕ) [Fact ℓ.Prime]
    [h : Abelian (DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))))]
    [HasDerivedCategory.{w}
      (DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))))] :
    Nonempty
      (((DerivedCategory.Q (C := DiscreteContinuousRep.{0, 0, 0}
          (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2))))).obj (@permutationComplex ℓ h)) ≅
        ((DerivedCategory.singleFunctor
          (DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2)))) 0).obj
            (trivialModule ℓ) ⊞
          ((DerivedCategory.singleFunctor
            (DiscreteContinuousRep.{0, 0, 0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2)))) 0).obj
              (trivialModule ℓ))⟦(-1 : ℤ)⟧)) := by
  sorry

end Rep.CyclicSquare
