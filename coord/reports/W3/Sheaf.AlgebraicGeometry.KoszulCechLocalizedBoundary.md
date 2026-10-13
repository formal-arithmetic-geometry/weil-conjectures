## What changed

The existing signature of AlgebraicGeometry.koszulCechLocalized_boundary is unchanged.
Its proof is reduced to the unlocalized increasing-wedge boundary calculation,
with denominator cancellation and totalization signs proved in the item's module.
A proof-only import of Sheaf.AlgebraicGeometry.KoszulCechBoundaryEvaluation supplies
that calculation; Mathlib.Data.Nat.Choose.Basic supplies triangular-number recurrence.
The original public import of KoszulCechLocalizedEvaluation remains required for
its statement and definitions. All edits are confined to the sandbox.

## Proved and sorry left

Closed hole: AlgebraicGeometry.koszulCechLocalized_boundary
(node lem-sc-koszul-cech-localized-boundary), the only original hole of the module.
One hole is split off as AlgebraicGeometry.koszulCechBoundary_evaluation
(node lem-sc-koszul-cech-boundary-evaluation), the only sorry in the delivery.
This is a decomposition, not a net hole reduction: it removes localization,
division, Hom signs and totalization signs from the remaining statement.
No other holes are added, and none remains in the item's own module.
Both delivered modules compile cleanly under lcompile.py. The dry-run axiom
probes report no forbidden axiom. The required deliver3.py --no-push check
validates the delivery; no push is performed.
The triangular-number sign identity and abstract division_factor lemma compile
in isolation. The contraction formula, ordered deletion, position cardinality
and exterior-power contraction formula also compile in scratch experiments.

## No longer needed

No imports or modules are pruned. The old direct proof dependencies
`def-sc-koszul-open-system` and `def-sc-module-total-hom-complex` are replaced
by `lem-sc-koszul-cech-boundary-evaluation` in the item's `proof_deps`.
They remain dependencies of that new node and are not globally unnecessary.
`def-sc-principal-open-alternating-total` remains a direct dependency for the
restriction and degree-transport calculation. No blueprint unit statement
or realized proof step is bypassed; sk-thm-picard-duality has no realization for
this node. No original import is removed.

## Where the brief, the DAG or earlier work was wrong

The original node's numerical sign-difference claim was incorrect:
S(p,n+1)+n-S(p-1,n) is 2*n, rather than 2*n-2*p+2. Its evenness claim remains
true, and no Lean statement changes. The revised node records the proved identity.
Although contraction_formula is private in Sheaf.Paper.KoszulDifferential,
the public proved koszul_differential includes its explicit formula clause;
it supplies a possible route for the remaining wedge calculation.
Initially the last-green-build cache lacked KoszulCechLocalizedEvaluation;
that dependency arrived after the next green build and local refresh.
LeanSearch was unavailable (Internal Server Error); the node records that
unavailability alongside the completed LeanFinder, Loogle and source searches.

## New nodes

lem-sc-koszul-cech-boundary-evaluation records only step 1 of the original plan:
negative Koszul contraction evaluated on the increasing wedge before any
localization or totalization signs. Its source is Stacks Tags 08D0 and 08D1,
its edge case card(J)=2 gives the usual two-generator Koszul boundary, and
its statement is meaningful for arbitrary coefficient complexes and in all
characteristics. No arbitrary data is chosen from an existence theorem.
No definition, existing interface or other group's module changes, so there
is no change record or forced adaptation.

## Second reading by W3

1. Interface: PASS. Compared the delivered item with the repository using diff,
   then checked the complete existing theorem signature byte for byte. It is
   identical. No existing definitions, public imports or other modules change;
   the corrected numerical assertion is only in the explanatory proof text.
2. Proof and trust: PASS as a decomposition. Both modules compile independently
   in import order with lcompile.py. The item has no sorry; the new module has
   exactly the reported named theorem with `:= by sorry`. No forbidden
   declarations, hollow definitions or arbitrary witnesses occur. A scratch
   copy probes both public theorems' axioms; each reports exactly propext,
   Classical.choice, Quot.sound and sorryAx for the remaining open proofs.
3. Split statement: PASS. Read the negative-tail definition and the contraction
   formula, and checked Stacks Tags 08D0 and 08D1 against the displayed equality.
   For two indices the boundary is minus (f(i)^(e+1)*e_j -
   f(j)^(e+1)*e_i), agreeing with the split statement. Empty covers and singleton
   subsets cannot satisfy the hypotheses; characteristic two, zero coefficients,
   the zero ring and arbitrary integer cochain degree cause no exception.
   The split removes localization, scalar inversion and both sign corrections,
   so it is strictly part of the original argument rather than a renamed item.
   Its source, complete docstring proof and node are present. Renewed LeanFinder,
   Loogle and Mathlib/source grep searches found contraction and enumeration
   ingredients, but no theorem with this transported ordered-subset statement.
   Source grep additionally found the public `ExteriorAlgebra.boundary_wedge`
   in `Sheaf.RingTheory.KoszulGeneratorChainMap`; this is a shorter raw-contraction
   ingredient than extracting the formula from koszul_differential. Its statement
   still requires reindexing the sum and transporting the extended-complex and
   coefficient degrees. A brief scratch attempt confirmed that these dependent
   degree transports do not close by the simple arithmetic rewrite attempted;
   no experimental partial proof is delivered.
4. Route and pruning: PASS after clarifying the report. Read the proof from the
   item downward. Denominator cancellation follows from linear inverse equations
   and naturality, and the parity calculation is proved using the choose recurrence.
   The two added imports are proof-only; all three public imports of the new
   module provide objects or degree equalities in its statement. The existing
   public localized-evaluation import is still needed. The unit record
   sk-thm-picard-duality has empty realized statement and step lists, so no
   realized route is bypassed. No import or module is pruned. The report now names
   both replaced original direct dependency edges and explains their indirect use.
5. DAG: PASS. Existing changes are confined to proof, proof_deps and proof_origin.
   Checked the steps against the actual sign, fraction and finite-sum argument;
   proof_deps equals the union of step uses. The new node has the required source,
   search records, creation provenance, blueprint ancestry, chapter/unit, and
   verbatim Lean statement. Its unproved argument remains a plan, not a claim
   of a completed proof.

Second reading changed the pruning/dependency accounting and documented the
additional public boundary_wedge search result. The reviewed Lean proofs and
statements needed no repair. One original hole is closed and one strictly simpler
hole is added: net zero, a decomposition rather than a sorry-free proof.
