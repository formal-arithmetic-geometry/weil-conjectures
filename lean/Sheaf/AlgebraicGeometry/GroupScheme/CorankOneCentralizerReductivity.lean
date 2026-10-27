module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Reductivity detected by centralizers of corank-one subtori

Source: Conrad, Reductive Group Schemes, Lemma 3.1.10, printed p.87
(blueprint: lem-sfb-corank-one-centralizer-reductivity-test).

The subtorus attached to a character is specified by its largest-subtorus universal
property inside the scheme-theoretic kernel. For the character lattice X, this is
exactly Spec k[X / (X ∩ ℚα)], including in positive characteristic. Centralizers are
specified by equality of represented subfunctors on all commutative test algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ReductiveTorusCentralizer

/-- A smooth connected affine algebraic group with a self-centralizing maximal torus
is reductive exactly when the centralizers of the corank-one subtori attached to its
nonzero adjoint character weights are reductive.

Source: Conrad, Reductive Group Schemes, Lemma 3.1.10, printed p.87
(blueprint: lem-sfb-corank-one-centralizer-reductivity-test).

The input families are representatives of the canonical subgroups, not additional
existence assumptions: `j α` is the largest subtorus of ker α, and `c α` represents
its full scheme-theoretic centralizer. The largest-subtorus property identifies its
character quotient with X / (X ∩ ℚα): any torus in ker α kills every character whose
nonzero integral multiple is an integral multiple of α. This quotient is free of
rank rank(X)-1. Thus it also handles inseparable characters such as p times a
primitive character, without replacing the kernel by its nonreduced identity component.

Proof, following the seven steps of the DAG node:
1. The group-like basis lemma identifies characters with the integral lattice.
   Saturating ℤα gives a rank-one saturated subgroup; the finite torsion-free
   quotient is free by lem-trf-fg-torsionfree-group-free. The diagonalizable
   geometric criteria identify its spectrum as the largest torus in ker α.
   If H is reductive, lem-sfb-reductive-torus-fixed-subgroup gives the forward implication.
2. For an arbitrary smooth connected normal unipotent subgroup N of H, the
   closed-subgroup and adjoint clauses of lem-sfb-affine-group-dual-number-calculus
   make Lie(N) a T-stable subspace of Lie(H). The split-torus weight decomposition
   shows its nonzero weights are in Ψ.
3. For a subtorus S of T, the intersection W = N ×_H C_H(S) represents N fixed by S.
   The torus-centralizer and torus-fixed-scheme smoothness lemmas make it smooth.
   The centralizer-Lie invariant lemma and dual-number calculus identify
   Lie(W) = Lie(N) ∩ Lie(H)^S = Lie(N)^S on all test algebras.
4. For S = T_α, the identity component W⁰ is smooth, connected, closed and unipotent.
   Conjugation by C_H(S)(k) preserves it; smooth ambient normality makes it normal.
   Reductivity of C_H(S) forces W⁰ = 1. Its open inclusion in W identifies tangent
   spaces at the identity, so Lie(N)^{T_α} = 0.
5. The α-weight space is fixed by T_α and therefore vanishes. Weight decomposition
   leaves only the zero weight: Lie(N) = Lie(N)^T. This also holds when Ψ is empty.
6. Apply step 3 with S = T. Since C_H(T) = T, the identity component of N ∩ T
   embeds in T and is unipotent. The unipotent-to-multiplicative-type triviality
   lemma makes it trivial, hence Lie(N)^T = 0 by the same open tangent comparison.
7. Rational tangent-cotangent duality identifies this zero tangent space with the
   cotangent-dual Lie space. Apply smooth-subgroup tangent generation to N, the
   empty finite family and the trivial subgroup, to obtain N = 1. This proves
   reductivity, including H = 1, T = 1, and the empty nonzero-weight set. -/
theorem corankOneCentralizer_reductive_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    (H T : Grp (Over (Spec (.of k))))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (i : T ⟶ H) (hT : IsMaximalTorus i)
    (hself : ∀ (A : Type u) [CommRing A] [Algebra k A],
      centralizerPoints i A =
        Set.range (fun t : StandardGroupSchemes.affine k A ⟶ T.X ↦ t ≫ i.hom.hom))
    (a : ModObj T.X H.X)
    (ha : a.smul = (i.hom.hom ⊗ₘ 𝟙 H.X) ≫ CategoryTheory.GrpObj.conj H.X)
    (Ψ : Set (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)))
    (hΨ : ∀ χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k),
      χ ∈ Ψ ↔ χ.hom.hom ≠ 1 ∧ @TorusCharacterTangent.weightSpace k _ T H a χ ≠ ⊥)
    (S : Ψ → Grp (Over (Spec (.of k))))
    (j : ∀ α : Ψ, S α ⟶ Grp.mk (CategoryTheory.GrpObj.ker α.val.hom.hom))
    (hS : ∀ α : Ψ, MultiplicativeType.IsLargestSubtorus (j α))
    (C : Ψ → Grp (Over (Spec (.of k)))) (c : ∀ α : Ψ, C α ⟶ H)
    (hc : ∀ α : Ψ, IsClosedSubgroupScheme (c α).hom.hom)
    (hC : ∀ (α : Ψ) (A : Type u) [CommRing A] [Algebra k A],
      centralizerPoints
        (j α ≫ Grp.ofHom (CategoryTheory.GrpObj.kerι α.val.hom.hom) ≫ i) A =
        Set.range (fun x : StandardGroupSchemes.affine k A ⟶ (C α).X ↦
          x ≫ (c α).hom.hom)) :
    IsReductive H ↔ ∀ α : Ψ, IsReductive (C α) := by
  sorry

end AlgebraicGeometry.ReductiveTorusCentralizer
