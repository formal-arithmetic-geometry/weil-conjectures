/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

/-! # Local weights and reality

Source: latest blueprint, sec-purity-real-sheaves/sk-d-real-weights, local polynomial
and logarithmic-weight complement (blueprint: sk-d-real-weights).

The accepted DAG statement uses a pointwise upper bound. The latest blueprint calls
this a punctual bound, distinguishing it from the finite-filtration mixed bound.
The constructible clauses use the actual scalar stalk and canonical local return of
`CondensedWeil`, rather than a lisse representation on a single global fibre.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace RealSheaves.LocalWeights

variable {K : Type u} [Field K] [Finite K] {C₀ : Scheme.{u}}
  {p : C₀ ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) {E : Type v} [Field E]
  {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (ρ : Representation E W.carrier V)

variable (ι : E →+* ℂ)

end RealSheaves.LocalWeights

namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The pointwise logarithmic upper bound on the actual constructible scalar stalks.
Source: latest blueprint, punctual-bound paragraph and local-weight complement;
accepted DAG pointwise-bound clause (blueprint: sk-d-real-weights). -/
def HasPunctualWeightsAtMost (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ)
    (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l)),
    Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
      WeilGroup.frobeniusWeight ι (Nat.card (X₀.left.residueField x.val)) α.down ≤ w

/-- The native modulus purity predicate is exactly logarithmic punctual purity.
Source: latest blueprint, purity formula and local-weight complement
(blueprint: sk-d-real-weights).
Proof: the actual local operator is a composite of isomorphisms, so each eigenvalue
is nonzero. Its image under the field embedding has positive norm. A closed point
of a finite-type scheme over the finite field has residue cardinality at least two.
Taking logarithms of the modulus equality gives 2*log(norm)/log(q_x)=w, and
exponentiation reverses the calculation. Quantify over the same closed points,
compatible residue embeddings, and eigenvalues as the native Pure predicate. -/
theorem pure_iff_logarithmic (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ)
    (w : ℝ) :
    Pure D l X₀ M ι w ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (α : ULift.{u + 1} (PadicAlgCl l)),
        Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
          WeilGroup.frobeniusWeight ι (Nat.card (X₀.left.residueField x.val)) α.down = w := by
  sorry

set_option maxHeartbeats 0 in
-- Comparing native scalar fibres and their matrix operators exceeds the default elaboration budget.
/-- The existing polynomial reality predicate is conjugation stability with multiplicity
in every finite basis of the actual scalar stalk. Constructible stalks have such bases.
Source: accepted DAG reality equivalence and constructible-stalk clause; latest
blueprint def-wf-iota-real.md (blueprint: sk-d-real-weights).
Proof: in each finite basis the canonical local return is invertible. Its characteristic
polynomial splits with nonzero roots over the algebraically closed coefficient field.
Reverse the factorization, embed in the complex numbers, and conjugate. The
coefficients have zero imaginary part exactly when conjugation fixes the polynomial.
Uniqueness of its nonzero reciprocal roots, with multiplicities, proves the forward
implication, and multiplying the conjugate-stable multiset proves the converse.
The existing Real predicate already quantifies over exactly these finite bases. -/
theorem real_iff_conjugation (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ) :
    NativeCondensedWeil.Real D l X₀ M ι ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (n : ℕ) (b : Module.Basis (Fin n) (ULift.{u + 1} (PadicAlgCl l))
          (NativeCondensedModule.fibre l D M.carrier
            (NativeCondensedModule.localClosedPoint D X₀ x i hi))),
        (((LinearMap.toMatrix b b (closedOperator D l X₀ M x i hi).hom).charpoly.roots.map
          (fun α ↦ ι α.down)).map (starRingEnd ℂ)) =
          (LinearMap.toMatrix b b (closedOperator D l X₀ M x i hi).hom).charpoly.roots.map
            (fun α ↦ ι α.down) := by
  sorry

end WeilConjectures.NativeL2
