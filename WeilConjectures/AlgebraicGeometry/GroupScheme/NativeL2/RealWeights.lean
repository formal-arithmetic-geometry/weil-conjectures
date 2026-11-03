/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeComplexUpperWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

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

/-- A constructible Weil sheaf is iota-mixed when it has a finite filtration by
constructible Weil subsheaves whose successive quotients are punctually pure, of
possibly different real weights. A zero quotient is pure of every weight.
Source: latest blueprint, sk-d-real-weights, mixedness sentence
(blueprint: sk-d-real-weights). -/
def IsMixed (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ) : Prop :=
  ∃ (n : ℕ) (G : Fin (n + 1) → WeilModule D l X₀)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (G i).carrier) ∧
    IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧ (∀ i, Mono (φ i)) ∧
      ∀ i : Fin n, ∃ v : ℝ, Pure D l X₀ (cokernel (φ i)) ι v

/-- A bounded Weil complex is pure of weight w when every nonzero cohomology sheaf,
with its induced Weil structure, is punctually pure of weight w+n in degree n.
Boundedness and constructibility are imposed by callers, as for the recorded upper
bound. Source: latest blueprint, sk-d-real-weights, purity of a complex
(blueprint: sk-d-real-weights). -/
def complexIsPure
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀)))
    (ι : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ n : ℤ, ¬ IsZero (complexWeilCohomology D l X₀ K n) →
    Pure D l X₀ (complexWeilCohomology D l X₀ K n) ι (w + (n : ℝ))

/-- Mixedness is the existence of some upper weight bound.
Source: latest blueprint, sk-d-real-weights, mixedness and weights-at-most sentences
(blueprint: sk-d-real-weights).
Proof: a filtration witnessing the bound w is a mixedness filtration. Conversely, a
mixedness filtration has finitely many quotient weights; their maximum, or zero for
the empty filtration, bounds them, so the same filtration witnesses Mixed. -/
theorem isMixed_iff_exists_mixed (M : WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ) :
    IsMixed D l X₀ M ι ↔ ∃ w : ℝ, Mixed D l X₀ M ι w := by
  sorry

/-- The punctual bound in logarithmic form is the modulus bound of the blueprint.
Source: latest blueprint, sk-d-real-weights, punctual-weights sentence
(blueprint: sk-d-real-weights).
Proof: the local operator is a composite of isomorphisms, so each eigenvalue is nonzero
and its image has positive norm. The residue cardinality is at least two, so its
logarithm is positive. Multiply the logarithmic inequality by log(q_x)/2 and
exponentiate, and reverse these steps for the converse. -/
theorem hasPunctualWeightsAtMost_iff_modulus (M : WeilModule D l X₀)
    (ι : PadicAlgCl l →+* ℂ) (w : ℝ) :
    HasPunctualWeightsAtMost D l X₀ M ι w ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (α : ULift.{u + 1} (PadicAlgCl l)),
        Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
          ‖ι α.down‖ ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2) := by
  sorry

/-- A zero Weil sheaf is punctually pure of every weight.
Source: latest blueprint, sk-d-real-weights, zero objects satisfy every bound
(blueprint: sk-d-real-weights).
Proof: every stalk of a zero sheaf is zero, so its local operator has no eigenvalue. -/
theorem pure_of_isZero (M : WeilModule D l X₀) (hM : IsZero M)
    (ι : PadicAlgCl l →+* ℂ) (w : ℝ) : Pure D l X₀ M ι w := by
  sorry

/-- A zero Weil sheaf has every punctual bound.
Source: latest blueprint, sk-d-real-weights, zero objects satisfy every bound
(blueprint: sk-d-real-weights).
Proof: every stalk of a zero sheaf is zero, so its local operator has no eigenvalue. -/
theorem hasPunctualWeightsAtMost_of_isZero (M : WeilModule D l X₀) (hM : IsZero M)
    (ι : PadicAlgCl l →+* ℂ) (w : ℝ) : HasPunctualWeightsAtMost D l X₀ M ι w := by
  sorry

/-- A zero Weil sheaf is mixed of weights at most w for every w.
Source: latest blueprint, sk-d-real-weights, zero objects satisfy every bound
(blueprint: sk-d-real-weights).
Proof: take the filtration of length zero, whose only term is the zero sheaf itself.
The zero sheaf is constructible, and there are no quotients to check. -/
theorem mixed_of_isZero (M : WeilModule D l X₀) (hM : IsZero M)
    (ι : PadicAlgCl l →+* ℂ) (w : ℝ) : Mixed D l X₀ M ι w := by
  sorry

/-- A zero Weil complex has weights at most w for every w.
Source: latest blueprint, sk-d-real-weights, zero objects satisfy every bound
(blueprint: sk-d-real-weights).
Proof: the cohomology functors are additive, so every cohomology sheaf of a zero
complex is zero, with zero Weil structure; apply the zero-sheaf case in each degree. -/
theorem complexMixedOfWeightsAtMost_of_isZero
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀)))
    (hK : IsZero K.carrier) (ι : PadicAlgCl l →+* ℂ) (w : ℝ) :
    complexMixedOfWeightsAtMost D l X₀ K ι w := by
  sorry

/-- A zero Weil complex is pure of every weight.
Source: latest blueprint, sk-d-real-weights, zero objects satisfy every bound
(blueprint: sk-d-real-weights).
Proof: every cohomology sheaf of a zero complex is zero, so no degree is constrained. -/
theorem complexIsPure_of_isZero
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀)))
    (hK : IsZero K.carrier) (ι : PadicAlgCl l →+* ℂ) (w : ℝ) :
    complexIsPure D l X₀ K ι w := by
  sorry

/-- At a point of degree d, with residue cardinality q^d, an eigenvalue has iota-weight w
exactly when its complex modulus is q^(dw/2).
Source: latest blueprint, sk-d-real-weights, first display
(blueprint: sk-d-real-weights).
Proof: the image of a nonzero eigenvalue has positive norm, and log(q^d)=d*log(q) is
positive for q>1 and d>0. The defining quotient equals w exactly when log of the norm
is d*w*log(q)/2; exponentiate, and take logarithms for the converse. -/
theorem frobeniusWeight_eq_iff_norm {E : Type v} [Field E] (ι : E →+* ℂ) (q d : ℕ)
    (hq : 1 < q) (hd : 0 < d) (α : E) (hα : α ≠ 0) (w : ℝ) :
    WeilGroup.frobeniusWeight ι (q ^ d) α = w ↔
      ‖ι α‖ = (q : ℝ) ^ ((d : ℝ) * w / 2) := by
  sorry

end WeilConjectures.NativeL2
