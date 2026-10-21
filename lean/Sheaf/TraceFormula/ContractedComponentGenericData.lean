/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Data.Set.Finite.Basic
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.TraceFormula.MultipointedCurve
import Sheaf.TraceFormula.ContractedComponentNoExtraGeneric

/-! # Generic constancy of contracted-component numerical data

Source: Temkin, Stable modification of relative curves, Lemma 5.1(ii), printed p. 34,
weighted incidence data, with the marked/ambient-incidence refinement specified in the DAG
(blueprint: lem-trf-contracted-component-generic-data).

The finite multiset is expressed by a finite list of triples and, separately in each fibre,
a bijection from its indices to the contracted components preserving the triples. This does
not label components consistently between different fibres.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ContractedComponentData

/-- The actual vanishing ideal of a component, giving its reduced induced closed structure.
Source: Temkin Lemma 5.1(ii); Stacks 01J3--01J4
(blueprint: lem-trf-contracted-component-generic-data). -/
def ideal {Z : Scheme.{u}} (R : irreducibleComponents Z) : Z.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨R.1, isClosed_of_mem_irreducibleComponents R.1 R.2⟩

/-- The scalar structure on the reduced component is the restriction of the ambient one.
Source: Temkin Lemma 5.1(ii)
(blueprint: lem-trf-contracted-component-generic-data). -/
abbrev over (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (R : irreducibleComponents Z) :
    (ideal R).subscheme.Over (Spec (.of k)) :=
  ⟨(ideal R).subschemeι ≫ p⟩

/-- The canonical scalar action on Zariski H1 of the component's structure sheaf.
This is the existing cohomology of the underlying abelian sheaf, with scalars restricted
along the component's structure map. Source: Temkin Lemma 5.1(ii)
(blueprint: lem-trf-contracted-component-generic-data). -/
abbrev h1Module (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (R : irreducibleComponents Z) :
    Module k (Scheme.Modules.H (SheafOfModules.unit (ideal R).subscheme.ringCatSheaf) 1) :=
  @Scheme.Modules.moduleHOfField k _ (ideal R).subscheme (over k p R)
    (SheafOfModules.unit (ideal R).subscheme.ringCatSheaf) 1

/-- Arithmetic genus of the reduced component itself, not of its normalization.
Source: Temkin Lemma 5.1(ii), weighted incidence graph
(blueprint: lem-trf-contracted-component-generic-data). -/
def genus (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (R : irreducibleComponents Z) : ℕ :=
  @Scheme.arithmeticGenus k _ (ideal R).subscheme (over k p R)

/-- Ambient self-nodes belonging to a component. On a nodal curve the two branches belong
to this component exactly when it is the unique global component through the node.
Each node is one point, even when both its branches belong to the component.
Source: Temkin Lemma 5.1(ii), incidence graph with loops retained
(blueprint: lem-trf-contracted-component-generic-data). -/
def selfNodes {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (R : irreducibleComponents Z) : Set Z :=
  {z | z ∈ R.1 ∧ ¬ (p.stalkMap z).hom.FormallySmooth ∧
    ∀ R' : irreducibleComponents Z, z ∈ R'.1 → R' = R}

/-- Distinct marking or ambient nonsmooth points lying on the component.
A self-node is counted once in this union. Source: Temkin Lemma 5.1(ii), decorated incidence
refinement (blueprint: lem-trf-contracted-component-generic-data). -/
def incidences {T : Scheme.{u}} (P : MultipointedCurve T)
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ T)
    (R : irreducibleComponents (pullback (C := Scheme) P.x s)) :
    Set (pullback (C := Scheme) P.x s) :=
  R.1 ∩ (Set.range (P.markingBaseChange s) ∪
    {z | ¬ ((pullback.snd P.x s).stalkMap z).hom.FormallySmooth})

/-- The actual triple attached to one reduced geometric component.
Source: Temkin Lemma 5.1(ii), decorated weighted incidence data
(blueprint: lem-trf-contracted-component-generic-data). -/
def triple {T : Scheme.{u}} (P : MultipointedCurve T)
    (k : Type u) [Field k] (s : Spec (.of k) ⟶ T)
    (R : irreducibleComponents (pullback (C := Scheme) P.x s)) : ℕ × ℕ × ℕ :=
  (genus k (pullback.snd P.x s) R,
    (selfNodes (pullback.snd P.x s) R).ncard, (incidences P s R).ncard)

/-- The subset of components contracted by the specified geometric fibre morphism.
Components are indexed by their underlying subsets, so no component is counted twice.
Source: Temkin Lemma 5.1(ii)
(blueprint: lem-trf-contracted-component-generic-data). -/
def contracted {T S : Scheme.{u}} {P Q : MultipointedCurve T} (f : P.Hom Q)
    (s : S ⟶ T) : Set (irreducibleComponents (pullback (C := Scheme) P.x s)) :=
  {R | ((f.curveBaseChange s) '' R.1).Subsingleton}

/-- The geometric point associated with an arbitrary algebraic closure of a residue field.
The formula is the same canonical Spec map as the recorded geometric-fibre definition.
Source: Temkin Lemma 5.1(ii)
(blueprint: lem-trf-contracted-component-generic-data). -/
def closurePoint (T : Scheme.{u}) (t : T) (k : Type u) [Field k]
    [Algebra (T.residueField t) k] : Spec (.of k) ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) k)) ≫
    T.fromSpecResidueField t

/-- Properness and finiteness in every geometric fibre, and generic constancy of the finite
multiset of triples (arithmetic genus, self-nodes, distinct marking/nonsmooth incidences).
The separate finiteness assertions make `finrank` and `ncard` genuine finite invariants.
Source: Temkin Lemma 5.1(ii), printed p. 34, decorated weighted incidence refinement
(blueprint: lem-trf-contracted-component-generic-data).

Proof, following the DAG:
1. Apply lem-trf-contracted-component-no-extra-generic to the proper curve map. It gives
   properness of every contracted reduced geometric component and, on an integral finite
   etale cover of a nonempty affine base open, finitely many flat finitely presented component
   families with a fixed contracted sublist. SemistableMarkedBaseChange preserves the marking.
2. The component closures are Noetherian and qcqs by finite presentation over the Noetherian
   base. Express the fraction field as the limit of nonzero principal opens. Apply
   lem-weil-pbc-eventually-proper to each contracted closure: its generic fibre is proper,
   so it is proper after shrinking. Intersect these finitely many opens; for an empty
   contracted list no shrinking is needed. Proper base change retains properness thereafter.
3. Apply lem-trf-contracted-component-generic-spread successively to these proper component
   families in the possibly nonproper ambient marked curve. It fixes H1 dimension, self-node
   count and distinct incidence count on a nonempty open. Over Spec of an algebraically
   closed field the same result gives finiteness in any fibre, and the component enumeration
   gives finiteness of the contracted list there.
4. Descend the open V on the integral finite etale cover S of U by deleting from U the image
   of S minus V. This image is closed because finite morphisms are proper and closed.
   The generic fibre of S over U is a single finite extension field, so its point belongs
   to V. The resulting open is nonempty and its inverse image is contained in V.
5. Over any point in this open and any algebraic closure of its residue field, lift the
   geometric point to S. Fibre-product identities identify the contracted components and
   triples with the fixed finite list. This gives a fibrewise bijection, hence precisely
   equality of multisets, independent of the lift or algebraic closure. Empty lists work.
-/
theorem generic_data (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T]
    [CompactSpace T] (P Q : MultipointedCurve T) (f : P.Hom Q)
    (hproperCurve : IsProper f.curve) (hproperMarking : IsProper f.marking)
    (hnodal : ∀ (t : T) (z : pullback (C := Scheme) P.x (Orgogozo.geometricPoint T t)),
      z ∉ (pullback.snd P.x (Orgogozo.geometricPoint T t)).smoothLocus →
        Orgogozo.IsOrdinaryDoublePoint
          (pullback.snd P.x (Orgogozo.geometricPoint T t)) z)
    (hetale : ∀ t : T, Etale (P.d.fiberToSpecResidueField t))
    (hmarking : ∀ (t : T) (e : pullback (C := Scheme) P.d (T.fromSpecResidueField t)),
      P.markingBaseChange (T.fromSpecResidueField t) e ∈
        (pullback.snd P.x (T.fromSpecResidueField t)).smoothLocus) :
    (∀ (t : T) (k : Type u) [Field k] [Algebra (T.residueField t) k]
      [IsAlgClosure (T.residueField t) k],
      (contracted f (closurePoint T t k)).Finite ∧
      ∀ R ∈ contracted f (closurePoint T t k),
        IsProper ((ideal R).subschemeι ≫ pullback.snd P.x (closurePoint T t k)) ∧
        @Module.Finite k (Scheme.Modules.H (SheafOfModules.unit (ideal R).subscheme.ringCatSheaf) 1)
          _ _ (h1Module k (pullback.snd P.x (closurePoint T t k)) R) ∧
        (selfNodes (pullback.snd P.x (closurePoint T t k)) R).Finite ∧
        (incidences P (closurePoint T t k) R).Finite) ∧
    ∃ (U : T.Opens) (n : ℕ) (w : Fin n → ℕ × ℕ × ℕ),
      (U : Set T).Nonempty ∧
      ∀ (t : T), t ∈ U → ∀ (k : Type u) [Field k] [Algebra (T.residueField t) k]
        [IsAlgClosure (T.residueField t) k],
        ∃ e : Fin n ≃ contracted f (closurePoint T t k),
          ∀ i : Fin n, triple P k (closurePoint T t k) (e i).1 = w i := by
  sorry

end AlgebraicGeometry.ContractedComponentData
