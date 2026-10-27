/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.AlgebraicGeometry.SubcanonicalResidualDuality
public import Sheaf.AlgebraicGeometry.MovingLinearSeriesZero
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Extremal subcanonical clusters moving on a common component

Source: Franciosi--Tenni, On Clifford's theorem for singular curves,
Lemma 3.3, printed pp.236--238, reduced nodal specialization
(blueprint: lem-sfb-extremal-cluster-moving-component).

The helpers spell out the node's Clifford index and its canonical section subspace.
The generality assertion uses opens of the affine polynomial spectrum in every basis.
The imported `restrictedLinearSeriesImage` is recorded by the definition node
`def-sfb-restricted-linear-series-image`; the moving-zero theorem is a proof prerequisite.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The node's Clifford index `2 p_a(X) - length(T) - 2 h⁰(I_T ⊗ ω)`.
Source: Franciosi--Tenni, Definition 2.10 and Lemma 3.3, pp.231, 236--238
(blueprint: lem-sfb-extremal-cluster-moving-component). -/
def subcanonicalCliffordIndex (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {T : Scheme.{u}} (j : T ⟶ X) (ω : X.Modules) : ℤ :=
  2 * (1 - eulerChar k (unit X)) -
    (Module.finrank k (scalarCohomology (j ≫ X ↘ Spec (.of k)) (unit T) 0) : ℤ) -
    2 * (Module.finrank k
      (scalarCohomology (X ↘ Spec (.of k)) (subcanonicalModule j ω) 0) : ℤ)

/-- The canonical section subspace `V_T ⊆ H⁰(X,ω)`, the span of the image of the
ideal-twist inclusion. That inclusion is k-linear, so this is its actual image.
Source: Franciosi--Tenni, Lemma 3.3, pp.236--238
(blueprint: lem-sfb-extremal-cluster-moving-component). -/
def subcanonicalCanonicalSections (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {T : Scheme.{u}} (j : T ⟶ X) (ω : X.Modules) :
    Submodule k (ProjectiveSpace.fieldSections k ω) :=
  Submodule.span k (Set.range fun s : ProjectiveSpace.fieldSections k (subcanonicalModule j ω) ↦
    (subcanonicalModuleInclusion j ω).val.app (op ⊤) s)

/-- A general residual of an extremal cluster has length two and `p_a - 1` sections
if both canonical section spaces move on one irreducible component.
Source: Franciosi--Tenni, Lemma 3.3, pp.236--238, reduced nodal specialization
(blueprint: lem-sfb-extremal-cluster-moving-component).

Proof, following the node's six steps:
1. Residual duality gives finite dimensions and h⁰(ω) = g. Residual to the empty
   cluster along a generically nonzero canonical section is a cluster D of length
   2g-2 and h⁰(F_D)=1. Its generator is generically nonzero, so no partition into
   at least two blocks is admissible and r(D)=0. If c(S)=0, maximality against D
   contradicts length(S)<2g-2. Thus c(S)<0.
2. For each partition P of the finite component set, form the sum W_P of the
   block-supported subspaces of V_S. Delete every proper W_P and every component
   restriction kernel. Subcanonicity makes the latter proper. A product of linear
   functionals and the infinite-field polynomial nonvanishing lemma
   (lem-trf-infinite-field-top-form-direction) give a nonempty open complement.
3. For a section in that complement, residual evaluation shows that it lies in
   both ideal twists, hence in the twist for U = S ∪ S*. Any admissible partition
   for U has s in W_P, forcing W_P=V_S. Directness follows from generic detection
   on the reduced curve, so r(U)≤r(S)≤R, and U is nonempty and subcanonical.
4. Apply lem-sfb-extremal-cluster-residual-nesting with c(S)<0 and the just
   verified union hypotheses. It gives S*⊆S for sections in the chosen open.
5. If a component restriction of V_S has dimension at least two, apply
   lem-sfb-moving-linear-series-zero with L=ω and Z=S, using invertibility from
   lem-sfb-nodal-line-serre-riemann-roch. Delete its additional finite set of proper
   subspaces. Polynomial nonvanishing gives a section with a zero x outside S.
6. At x, F_S=ω. Writing s=f e in a local frame, evaluation has image (f)e, so
   the residual ideal at x is (f). Vanishing puts x in S*, contradicting S*⊆S.
   Thus no component of V_S moves; the implication is true on the whole affine
   space. Both requested numerical conclusions follow from its false antecedent.
-/
theorem extremal_cluster_moving_component
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [Nonempty X] [ConnectedSpace X] [IsReduced X]
    (hTwoConnected : ∀ (A B : Scheme.{u}) (a : A ⟶ X) (b : B ⟶ X),
      IsClosedImmersion a → IsClosedImmersion b → IsReduced A → IsReduced B →
      Nonempty A → Nonempty B →
      (∃ P Q : Set (Set X), P ⊆ irreducibleComponents X ∧ Q ⊆ irreducibleComponents X ∧
        Disjoint P Q ∧ P ∪ Q = irreducibleComponents X ∧
        Set.range a = ⋃₀ P ∧ Set.range b = ⋃₀ Q) →
      2 ≤ Module.finrank k (scalarCohomology
        (CategoryTheory.Limits.pullback.fst a b ≫ a ≫ X ↘ Spec (.of k))
        (unit (CategoryTheory.Limits.pullback a b)) 0))
    (S : Scheme.{u}) (i : S ⟶ X) [IsClosedImmersion i]
    (D : SubcanonicalClusterData k X S i)
    (hSsub : IsSubcanonicalCluster i D.dualizing)
    (R : ℕ) (hIndex : subcanonicalSplittingIndex D ≤ R)
    (hClifford : subcanonicalCliffordIndex k i D.dualizing ≤ 0)
    (hExtremal : ∀ (T : Scheme.{u}) (j : T ⟶ X) [IsClosedImmersion j]
      (E : SubcanonicalClusterData k X T j), E.dualizing = D.dualizing →
      IsSubcanonicalCluster j D.dualizing → subcanonicalSplittingIndex E ≤ R →
      subcanonicalCliffordIndex k i D.dualizing ≤ subcanonicalCliffordIndex k j D.dualizing ∧
      (subcanonicalCliffordIndex k j D.dualizing = subcanonicalCliffordIndex k i D.dualizing →
        Module.finrank k (scalarCohomology (j ≫ X ↘ Spec (.of k)) (unit T) 0) ≤
          Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0)))
    (hLength : 0 < Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0))
    (hLengthUpper :
      (Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ) <
        2 * (1 - eulerChar k (unit X)) - 2) :
    ∀ (n : ℕ)
      (b : Module.Basis (Fin n) k
        (ProjectiveSpace.fieldSections k (subcanonicalModule i D.dualizing))),
      ∃ U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) k)),
        (∃ s : ProjectiveSpace.fieldSections k (subcanonicalModule i D.dualizing),
          PrimeSpectrum.comap (MvPolynomial.eval (fun a ↦ b.repr s a))
            (IsLocalRing.closedPoint k) ∈ U) ∧
        ∀ s : ProjectiveSpace.fieldSections k (subcanonicalModule i D.dualizing),
          PrimeSpectrum.comap (MvPolynomial.eval (fun a ↦ b.repr s a))
            (IsLocalRing.closedPoint k) ∈ U →
          (∀ C : irreducibleComponents X,
            TopCat.Presheaf.germ (subcanonicalModule i D.dualizing).presheaf ⊤
              (genericPoints.ofComponent C).val (Set.mem_univ _) s ≠ 0) →
          ∀ J : X.IdealSheafData, topologicalKrullDim J.subscheme ≤ 0 →
            imageSubobject (subcanonicalEvaluation (subcanonicalModule i D.dualizing)
              D.dualizing s) =
              imageSubobject (subcanonicalModuleInclusion J.subschemeι D.dualizing) →
            ∀ (C : Scheme.{u}) [C.Over (Spec (.of k))] [IsReduced C]
              (j : C ⟶ X) [IsClosedImmersion j] [j.IsOver (Spec (.of k))],
              Set.range j ∈ irreducibleComponents X →
              2 ≤ Module.finrank k (restrictedLinearSeriesImage k j D.dualizing
                (subcanonicalCanonicalSections k i D.dualizing)) →
              2 ≤ Module.finrank k (restrictedLinearSeriesImage k j D.dualizing
                (subcanonicalCanonicalSections k J.subschemeι D.dualizing)) →
              Module.finrank k (scalarCohomology (J.subschemeι ≫ X ↘ Spec (.of k))
                (unit J.subscheme) 0) = 2 ∧
              (Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
                (subcanonicalModule J.subschemeι D.dualizing) 0) : ℤ) =
                (1 - eulerChar k (unit X)) - 1 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
