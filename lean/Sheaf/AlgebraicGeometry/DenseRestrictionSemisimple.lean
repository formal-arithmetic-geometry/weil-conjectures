module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
import Mathlib.RingTheory.SimpleModule.Basic
import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

/-! # Semisimple restriction to a dense abstract subgroup

Source: Milne, Algebraic Groups (2017), Proposition 4.3 and Corollaries 4.4--4.5,
p.85; Proposition 4.17, p.90; proof of Lemma 13.6, p.256
(blueprint: lem-sfb-dense-restriction-semisimple).

A basis identifies an arbitrary finite-dimensional space with `m → k`, including the
empty basis. Rational stability is written over every commutative k-algebra, without
using the characteristic-zero-only upstream rational semisimplicity abbreviation.
The span of the coefficientwise image of a subspace is its scalar extension inside `m → A`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup.RationalHom

/-- Restriction of a finite direct sum of simple rational representations to a dense abstract
subgroup is a finite direct sum of simple abstract representations, every invariant subspace
has an invariant complement, and every equivariant surjection out of it has an equivariant
linear section. Rational stability and simplicity are expanded in the hypothesis so that
neither characteristic zero nor connectedness is assumed.

Source: Milne, Algebraic Groups (2017), Proposition 4.3 and Corollaries 4.4--4.5, p.85;
Proposition 4.17, p.90; proof of Lemma 13.6, p.256
(blueprint: lem-sfb-dense-restriction-semisimple).

Proof:
1. For a Gamma-stable subspace, the stabilizer is closed by
   `lem-wf-stabilizer-density`. Its inverse image in G contains the dense subgroup, hence
   all rational points preserve the subspace. Inverses turn containment into equality.
2. `lem-sfb-smooth-group-rational-point-subspace-test` identifies this with stability over
   every algebra, including nonreduced algebras. Conversely rational stability implies
   Gamma-stability by evaluation at k. The two collections of subspaces therefore coincide.
3. Each given simple rational summand remains simple: any Gamma-stable subspace of it is
   rationally stable by steps 1--2, and hence zero or the whole summand. The original finite
   internal sum is unchanged. The zero space is the empty direct sum.
4. The Gamma-stable k-subspaces are exactly the k[Gamma]-submodules: use a[1] and [gamma]
   in one direction and closure under finite sums in the other. The preceding simple
   summands span the module. Apply `lem-sfb-module-socle-complements`, whose Mathlib
   declaration is `IsSemisimpleModule.of_sSup_simples_eq_top`, to obtain a stable complement.
5. For an equivariant surjection q, its kernel is stable. On its stable complement C,
   q is injective by disjointness and surjective by the sum decomposition. Its inverse,
   followed by the inclusion of C, is linear and equivariant and is a section of q.
   If the source is zero, surjectivity forces the target to be zero as well. -/
theorem dense_restriction_semisimple
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left]
    [Smooth G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {m : Type u} [Fintype m] [DecidableEq m]
    (ρ : RationalHom G m) [IsMonHom ρ]
    (Γ : Subgroup (AlgebraicGeometry.points G k))
    (hdense : DenseRange fun γ : Γ ↦ γ.val.left (IsLocalRing.closedPoint k))
    (hM : ∃ (n : ℕ) (S : Fin n → Submodule k (m → k)),
      iSupIndep S ∧ (⨆ i, S i) = ⊤ ∧ ∀ i,
        S i ≠ ⊥ ∧
        (∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : AlgebraicGeometry.points G A),
          Submodule.span A ((fun w : m → k ↦ fun j ↦ algebraMap k A (w j)) '' (S i : Set _)) ≤
            (Submodule.span A
              ((fun w : m → k ↦ fun j ↦ algebraMap k A (w j)) '' (S i : Set _))).comap
                (Matrix.toLin' (ρ.points A g))) ∧
        ∀ T : Submodule k (m → k), T ≤ S i →
          (∀ (A : Type u) [CommRing A] [Algebra k A]
            (g : AlgebraicGeometry.points G A),
            Submodule.span A ((fun w : m → k ↦ fun j ↦ algebraMap k A (w j)) '' (T : Set _)) ≤
              (Submodule.span A
                ((fun w : m → k ↦ fun j ↦ algebraMap k A (w j)) '' (T : Set _))).comap
                  (Matrix.toLin' (ρ.points A g))) → T = ⊥ ∨ T = S i) :
    (∃ (n : ℕ) (S : Fin n → Subrepresentation (ρ.representation.comp Γ.subtype)),
      (∀ i, (S i).toRepresentation.IsIrreducible) ∧
        iSupIndep (fun i ↦ (S i).toSubmodule) ∧ (⨆ i, (S i).toSubmodule) = ⊤) ∧
    (∀ N : Subrepresentation (ρ.representation.comp Γ.subtype),
      ∃ C : Subrepresentation (ρ.representation.comp Γ.subtype),
        IsCompl N.toSubmodule C.toSubmodule) ∧
    (∀ (V : Type v) [AddCommGroup V] [Module k V] (σ : Representation k Γ V)
      (q : Representation.IntertwiningMap (ρ.representation.comp Γ.subtype) σ),
      Function.Surjective q →
        ∃ s : Representation.IntertwiningMap σ (ρ.representation.comp Γ.subtype),
          q.toLinearMap.comp s.toLinearMap = LinearMap.id) := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup.RationalHom
