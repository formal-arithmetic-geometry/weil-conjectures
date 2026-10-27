module

public import Mathlib.Algebra.Lie.SerreConstruction
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.Algebra.Lie.Sl2
import Sheaf.Algebra.Lie.RationalSerrePresentation

/-!
# The Serre presentation with a prescribed rational pinning

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.63,
printed pp.503–504, and its characteristic-zero extension and normalized
simple-root triples on p.508.
(blueprint: lem-sfb-pinned-serre-presentation-isomorphism)

The comparison uses the actual free Lie algebra quotient `Matrix.ToLieAlgebra`.
The roots are indexed by `ι`, and the simple roots by an arbitrary finite type `I`.
Neither index type is required to be nonempty. Root spaces are ordinary simultaneous
eigenspaces, and the normalized bracket elements are supplied independently of
the intrinsic root-pairing coroots.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace LieAlgebra

open Classical in
/-- The prescribed simple-root triples identify the rational Serre quotient with the
given split semisimple Lie algebra, with the stated values on every generator.
Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, pp.503–504,
and the characteristic-zero extension and normalized triples on p.508.
(blueprint: lem-sfb-pinned-serre-presentation-isomorphism)

Proof plan, following the seven steps of the node:
1. If I is empty, its basis makes the Cartan dual zero, hence the Cartan zero.
   There are no roots, so the decomposition makes L zero. The universal property
   makes the free Lie algebra on no generators, and its quotient, zero as well.
2. Jacobi adds weights under brackets. Repeated adjoints of a root vector shift
   weights by distinct multiples of a nonzero root, so they vanish eventually
   on the finite weight decomposition. One-dimensional opposite root spaces and
   the normalized bracket elements give sl2 triples for every root.
3. Apply lem-sfb-integrable-sl2-reflection-automorphism to those triples. Their
   reflections permute the roots and are identified with the intrinsic root
   reflections by averaging a rational positive definite form over the finite
   root permutation group. Thus evaluation at hα a is the intrinsic coroot
   functional and all root pairings are integral; in particular each
   α_j(hα_i) is an integer, which is the first conjunct (the matrix a_ij exists).
4. Apply lem-sfb-serre-rational-presentation to this root system and base. It
   identifies the simple Cartan generators with the simple coroots, which form
   a basis of H, and gives dimension |I| + |ι| for the quotient.
5. Distinct simple roots have mixed-sign difference, so the mixed brackets
   vanish. The weight equations give the Cartan relations and diagonal entries
   two. Reflection of a simple root in a different simple root has one positive
   coordinate; the sign condition forces the other Cartan entry nonpositive.
   Apply lem-sfb-sl2-primitive-string-vanishing to the swapped sl2 triple and
   then the original triple to obtain the E and F Serre relations. The free
   universal map therefore kills the defining ideal and descends to the quotient
   with exactly the prescribed generator values.
6. For a positive root, the positive definite form supplies a simple coroot with
   positive pairing. Its reflection lowers integral height until a simple root
   is reached; the sign condition keeps the other steps positive. Apply this
   also to negative roots. Every root lies in a signed simple-root orbit.
7. The image contains H and the simple positive and negative root spaces. It is
   stable under the finite exponentials defining the simple reflection
   automorphisms and their inverses. Step 6 propagates containment to every root
   space, so the decomposition gives surjectivity. The equal dimensions from
   step 4 give injectivity; the linear inverse preserves brackets. -/
theorem exists_pinnedSerrePresentation_isomorphism
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [IsLieAbelian H]
    (hmax : ∀ K : LieSubalgebra ℚ L, H ≤ K → IsLieAbelian K → K = H)
    (hsplit : ∀ h : H, (⨆ a : ℚ, (ad ℚ L (h : L)).eigenspace a) = ⊤)
    (ι : Type v) [Finite ι] (P : RootPairing ι ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (α : Module.Dual ℚ H) (h : H), P.toLinearMap α h = α h)
    (hdecomp : DirectSum.IsInternal
      (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
        (fun a : ι ↦ (LieModule.weightSpace L (P.root a)).toSubmodule)))
    (hdim : ∀ a : ι, Module.finrank ℚ (LieModule.weightSpace L (P.root a)) = 1)
    (hα : ι → H)
    (hbracket : ∀ a : ι, (hα a : L) ∈ Submodule.span ℚ
      {z : L | ∃ x ∈ LieModule.weightSpace L (P.root a),
        ∃ y ∈ LieModule.weightSpace L (-P.root a), ⁅x, y⁆ = z})
    (htwo : ∀ a : ι, P.root a (hα a) = 2)
    (I : Type w) [Finite I]
    (s : I → ι) (b : Module.Basis I ℚ (Module.Dual ℚ H))
    (hb : ∀ i : I, b i = P.root (s i))
    (hsign : ∀ a : ι, (∀ i : I, ∃ n : ℤ, b.repr (P.root a) i = (n : ℚ)) ∧
      ((∀ i : I, 0 ≤ b.repr (P.root a) i) ∨ (∀ i : I, b.repr (P.root a) i ≤ 0)))
    (e f : I → L)
    (he : ∀ i : I, e i ∈ LieModule.weightSpace L (P.root (s i)) ∧ e i ≠ 0)
    (hf : ∀ i : I, f i ∈ LieModule.weightSpace L (-P.root (s i)) ∧ f i ≠ 0)
    (hef : ∀ i : I, ⁅e i, f i⁆ = (hα (s i) : L)) :
    (∃ A : Matrix I I ℤ, ∀ i j : I, (A i j : ℚ) = P.root (s j) (hα (s i))) ∧
    ∀ A : Matrix I I ℤ, (∀ i j : I, (A i j : ℚ) = P.root (s j) (hα (s i))) →
      (∀ i : I, A i i = 2) ∧ (∀ i j : I, i ≠ j → A i j ≤ 0) ∧
      ∃ φ : Matrix.ToLieAlgebra ℚ A ≃ₗ⁅ℚ⁆ L,
        (∀ i : I, φ (LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal ℚ A)
          (FreeLieAlgebra.of ℚ (CartanMatrix.Generators.H i))) = (hα (s i) : L)) ∧
        (∀ i : I, φ (LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal ℚ A)
          (FreeLieAlgebra.of ℚ (CartanMatrix.Generators.E i))) = e i) ∧
        (∀ i : I, φ (LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal ℚ A)
          (FreeLieAlgebra.of ℚ (CartanMatrix.Generators.F i))) = f i) := by
  sorry

end LieAlgebra
