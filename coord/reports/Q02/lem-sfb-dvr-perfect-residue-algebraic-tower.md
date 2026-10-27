## Worker report

The module `Sheaf.RingTheory.DvrPerfectResidueAlgebraicTower` states
`IsDiscreteValuationRing.exists_algebraic_perfect_residue_tower`, with its entire
proof postponed by `sorry`. No definitions or other theorems are introduced.
The node changes only in `lean`. There is no statement correction and no disputed
statement. The source read was `literature/stacks-project/more-algebra.tex`,
Tag 09II, `proposition-epp-essentially-finite-type`, especially lines 35980–35993.
The seven-step proof docstring follows the node, including the finite-stage
identification with integral closures and the direct ideal argument for the union.

Hypotheses and clauses, in the order of the informal statement:

- A DVR A: `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. Mathlib's class is the local principal ideal
  domain with nonzero maximal ideal, excluding fields exactly as the node does.
- Its fraction field K: `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`. The universe of K is independent of that of A.
- The residue field k is the canonical `IsLocalRing.ResidueField A`, defined
  by Mathlib as A modulo `IsLocalRing.maximalIdeal A`.
- Positive residue characteristic: `(p : ℕ) (hp : 0 < p)
  [CharP (IsLocalRing.ResidueField A) p]`. Primality is a consequence because
  this residue ring is a field; it is not an additional assumption.
- An algebraic field extension P/K: the existential `P : Type (max u v)`,
  `Field P`, `Algebra K P`, and `Algebra.IsAlgebraic K P`. This last class means
  every element satisfies a nonzero polynomial over K. `Algebra A P` and
  `IsScalarTower A K P` express the composite A → K → P, not independent maps.
- The ring A' is exactly `integralClosure A P`, not an arbitrary DVR in P.
  The existential `hC : IsDiscreteValuationRing (integralClosure A P)` states
  it is a DVR. Its domain instance comes from being a subring of the field P.
- The index-one equality is
  `(IsLocalRing.maximalIdeal A).map (algebraMap A (integralClosure A P)) =
  @IsLocalRing.maximalIdeal (integralClosure A P) _ hC.toIsLocalRing`.
  This is equality of extended ideals, not just equality of contractions.
- The existential `IsLocalHom (algebraMap A (integralClosure A P))` is the
  locality consequence of that ideal equality, used as instance data to type
  Mathlib's canonical residue-field map. Indeed a nonunit of A lies in its
  maximal ideal, so its image lies in the maximal ideal of A'. It adds no
  mathematical restriction and is an output, not an input assumption.
- The perfect residue field is
  `PerfectField (IsLocalRing.ResidueField (integralClosure A P))`.
  In characteristic p this is equivalent to surjectivity of x ↦ x^p:
  `PerfectField.toPerfectRing`, `PerfectRing.surjective_frobenius`, and
  `PerfectRing.toPerfectField` in `Mathlib.FieldTheory.Perfect` give both
  directions. The canonical field map transports the base characteristic.
- The residue extension is algebraic and purely inseparable by
  `Algebra.IsAlgebraic` and `IsPurelyInseparable`, each explicitly supplied with
  the algebra structure
  `(IsLocalRing.ResidueField.map (algebraMap A (integralClosure A P))).toAlgebra`.
  Thus these clauses concern the induced residue-field map. They cannot refer
  to an unrelated algebra structure. `isPurelyInseparable_iff_pow_mem` in
  `Mathlib.FieldTheory.PurelyInseparable.Basic` identifies the latter class
  with every element having some p-power in the base field, as specified.
- A directed family of subextensions is the existential nonempty index type I
  and `F : I → IntermediateField K P` with `Directed (· ≤ ·) F`.
  Directedness is inclusion of the actual subfields of P; no additional
  preorder on indices is needed. I lives in the same universe as P.
- Finiteness of each P_j/K is `∀ j : I, Module.Finite K (F j)`, and
  `∀ x : P, ∃ j : I, x ∈ F j` says their set-theoretic union is all of P.
- Each A_j is exactly `integralClosure A (F j)`. The existential DVR witness hj
  and the displayed ideal-map equality for this ring state both finite-stage
  assertions, again using equality of extended maximal ideals. The A-algebra
  structure on each F j is the one inherited from the scalar tower.
- The final formula, for every x in P,
  `x ∈ integralClosure A P ↔ ∃ (j : I) (y : integralClosure A (F j)),
  algebraMap (F j) P (y : F j) = x`, is precisely A' = union A_j inside P.
  The maps are the inclusions of those actual subfields. This records both
  containment directions and does not substitute a union of arbitrary rings.
- No completeness, finite p-basis, characteristic of K, separability of P/K,
  or finiteness of P/K is assumed.

Recorded statement dependencies read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and
  `IsLocalRing.maximalIdeal`, `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
  Its full class signature and docstring were read.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, with
  fields on source and target. Its full signature and docstring were read.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. Its carrier is exactly
  `{x | IsIntegral A x}`; its definition, signature, and docstring were read.

Other statement API: `IntermediateField` from
`Mathlib.FieldTheory.IntermediateField.Basic`; `IsFractionRing` from
`Mathlib.RingTheory.Localization.FractionRing`; the canonical residue-field
construction/map from `Mathlib.RingTheory.LocalRing.ResidueField.Basic`;
`PerfectField` and `IsPurelyInseparable` from the public imports above. These
existing Mathlib notions require no replacement definitions.

Proof-dependency imports are present for the recorded declarations:
`WeilConjectures.FieldTheory.ExistsPBasis` (`Field.exists_p_basis`),
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (`AlgebraicClosure` and the
algebraic closure existence/uniqueness API), `Mathlib.RingTheory.AdjoinRoot`
(`AdjoinRoot.powerBasis'`), `Mathlib.RingTheory.PrincipalIdealDomain` and
`Mathlib.RingTheory.Polynomial.RationalRoot` (PID implies Noetherian,
unique factorization, and integrally closed). The already-public DVR and
integral-closure imports supply
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` and
`Algebra.IsIntegral.of_finite`. The two newly split finite-stage proof inputs
`lem-sfb-p-independent-root-quotient-field` and
`lem-sfb-finite-free-field-fibre-dvr` have no Lean attachment on the read base;
there is no recorded module for them to import. They are named in the proof
plan and remain genuine proof dependencies of the unchanged node.

Edge cases checked mathematically before writing and again against the signature:

- Perfect initial residue field: the empty p-basis permits P = K and all
  stages equal to K; the integral closure is A. No strict extension is demanded.
- Infinite p-basis: I need not be finite or countable, and only individual
  field stages are finite-dimensional. Directedness permits finite sets of
  roots and increasing root levels.
- Characteristic zero and characteristic p fraction fields: neither is
  excluded; only the residue field has its characteristic fixed.
- p = 0 is excluded exactly by hp; p = 1 and composite p have no field
  satisfying the characteristic hypothesis, so are not extra mathematical cases.
- The finite subsets used in the construction can be empty, but the family
  of stages is nonempty; even the zero field element must lie in some stage.
- A field cannot serve as the input DVR or any stage DVR because Mathlib's
  DVR class requires a nonzero maximal ideal. No such edge case was silently added.
- Universes u and v are independent; witnesses P and I may live in max u v,
  which contains A, K, the algebraic-closure construction, and its finite-root
  indexing sets. No small-universe test quantification is used.

Searches performed with the prescribed msearch.py wrapper for Q02 and this item:

1. `leanfinder`: "Every discrete valuation ring admits an algebraic fraction field
   extension with integral closure a DVR of ramification index one and perfect
   purely inseparable residue field". Eight hits: residue formal-unramifiedness,
   residue separability/algebraicity, ramification degree formulas, and DVR
   criteria; no theorem constructs this extension and its directed tower.
2. `loogle`: "IsDiscreteValuationRing, PerfectField". Zero hits.
3. `grep`, RingTheory: "perfect.*residue|residue.*perfect|perfectResidue|perfect_residue".
   Two hits, in Ideal/Quotient/HasFiniteQuotients and RamificationInertia/Ramification;
   neither is an existence/tower theorem.
4. `leansearch`: "A discrete valuation ring admits an algebraic extension with
   perfect purely inseparable residue field and unchanged uniformizer".
   Eight hits about DVR valuation rings, DVR recognition, or consequences
   for existing residue extensions; no match.
5. Direct rg of the same concept in `lean/WeilConjectures` and `lean/Sheaf`:
   existing results assume perfect residue fields or concern unrelated
   perfect complexes; the parent Epp theorem's proof cites this node, but
   no declaration states it. `grep -rn` of this exact node id in
   `lean/WeilConjectures` and rg of `dag/lean_names_upstream.json` found no match.
6. Direct rg for `exists_algebraic_perfect_residue_tower` in Mathlib,
   `lean/WeilConjectures`, and `lean/Sheaf` found no existing declaration.

Validation: the file compiled cleanly via scompile.py, both as the sandbox
module and as `Sheaf.RingTheory.DvrPerfectResidueAlgebraicTower`, within the
60-second limits. The one admitted named theorem is intentional stage-2 work.
An initial local scratch compile was run in error before the module was written;
all module compilation and delivery validation use the prescribed wrappers.

## Second reading by Q02

Reread the node and module together, including the explicit algebra arguments
on both residue-extension predicates and every finite-stage clause. The DVR
witnesses hC and hj determine the local-ring instances in the stated maximal
ideals. The residue-map algebra is the canonical one. The two union clauses
use actual inclusions into P; the finite closure rings are not unrelated
existential DVRs. Locality is output data already forced by ideal equality,
not an extra hypothesis. No clause of the informal statement is omitted,
and the signature contains no completeness or finite p-basis assumption.
The proof-plan rereading made the p-basis root formula explicit as
sum c_E*alpha_(i,1)^E, whose p-th power is sum c_E^p*b^E.
No mathematical statement change was needed. This is a same-worker rereading;
no second agent was started, in accordance with the dispatcher brief.
The maintainer's independent review remains the independent reading.
