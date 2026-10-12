## What changed

Repaired both duplicate-helper findings in the returned delivery. Removed the local
`AlgebraicGeometry.property_overPullback_comp` and
`AlgebraicGeometry.over_pullback_square` declarations. The module now uses
`import all Sheaf.AlgebraicGeometry.DescendClosedImmersion` and
`import all Sheaf.AlgebraicGeometry.DescendFiniteAffineOpen` to reuse the existing
private theorems in their original modules. These are proof-only imports; Lean's
module system exposes their private declarations within this file without making
those declarations public. Neither original module is changed or delivered.

The sole original sorry in `AlgebraicGeometry.descend_finite_locally_free` remains
replaced by the complete previously delivered proof. Its signature, universes,
public imports and docstring are unchanged. The only remaining local helper is
`over_pullback_comparison_square`, proved by pullback cancellation using the imported
`over_pullback_square` theorem.

Finite and flat descent give two stages; directedness supplies a common later stage.
The imported composite-base-change helper transports both properties there, and
local finite presentation persists by base change. For degree descent, the proof
constructs the upper-tail equivalence with `Over (op i₀)`, the base-changed limit
cone and its comparison squares. Local constancy gives a clopen, constructible
degree-d locus; fibre-degree base change puts the limit image inside it. The
constructible-limit lemma supplies a later stage with constant degree d.

All four mathematical steps of `lem-weil-pbc-descend-finite-locally-free` are kept.
The helpers implement the same categorical glue as before; no mathematical route
or proof-dependency node changes. The helper-host modules are imported for their
private categorical lemmas, not for their main descent theorems. No new nodes,
statement corrections or interface changes are introduced.

Validation: compiled the repaired module with `lcompile.py` against the existing
compiled library, without a sandbox build overlay. Both added imports passed the
import-direction checks. The required `deliver3.py --no-push` dry run is the final
verification. No delivery is pushed by this worker.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.descend_finite_locally_free`
(node `lem-weil-pbc-descend-finite-locally-free`). Both conjuncts have complete Lean
proofs. No sorry remains in the delivered module, and no holes were added or split
off. This is a proof from existing declarations, not a claim that their transitive
proofs are all finished.

The proof still depends on the existing hole
`AlgebraicGeometry.exists_flat_stage_of_limit`. The current repository proof of
`AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible` is complete;
the earlier report incorrectly described it as still holed. Transitive axioms of
the item include `sorryAx`, as expected for the open dependencies. The imported
private helpers are already proved and add no holes. The delivery adds no definitions and chooses no data from an unproved
mere-existence statement.

The original edge-case checks still apply: i₀ supplies nonemptiness of I, the
upper tail contains the common stage, degree zero uses the same clopen-locus
argument, and empty schemes require no chosen point. All helper binders match
the existing statements exactly, including arbitrary preorders and universe u.

## No longer needed

The two duplicate local helper proofs are removed and replaced by imported existing
proofs. No original import, DAG node or module of the mathematical plan is pruned.
Every proof import is used:

- `Sheaf.AlgebraicGeometry.DescendFinite`: finite descent.
- `Sheaf.AlgebraicGeometry.DescendClosedImmersion`: existing `property_overPullback_comp`.
- `Sheaf.AlgebraicGeometry.DescendFiniteAffineOpen`: existing `over_pullback_square`.
- `Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation`: flat descent.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`: the clopen degree locus.
- `Sheaf.AlgebraicGeometry.LimitContainedInConstructible`: eventual image containment.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`: base-change diagrams,
  their limit cone, and compact/quasi-separated stages.

The existing public imports support the unchanged statement and remain in place.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery recreated two private helper statements already implemented
elsewhere. The landing check correctly rejected this duplication. Both findings
are repaired by importing and using the existing declarations. The fact that they
are private does not prevent reuse: proof-only `import all` works in Lean's module
system and is understood by the project's import readers. No helper export or
adaptation of another module is needed. No mathematical statement or proof-plan
error was found.

The previous second-reading section described the unrepaired version and has been
removed so the second reader can review this repair independently.

## Second reading by F3

1. **Unchanged interface: PASS.** Read the complete delivered module and its diff
   against `lean/Sheaf/AlgebraicGeometry/DescendFiniteLocallyFree.lean`. Checked the
   existing declaration's signature byte for byte, including universe u, directed
   preorder, affine transitions, limit cone, all three qcqs hypotheses, local
   finite presentation, and both existential conclusions. The public imports,
   definitions and existing docstrings are unchanged. Only the proof, one private
   proved helper and two proof-only `import all` lines are added. No change record
   is required, and no other module is delivered.
2. **Proof and axioms: PASS with existing open dependencies.** `lcompile.py`
   compiled the delivered file without warnings in 5.1 seconds. A fresh scratch
   copy of the repaired file, not the stale first-worker copy, compiled in 5.6
   seconds with `#print axioms` for the item and all three helpers. The helpers
   use only `propext`, `Classical.choice`, `Quot.sound`; the item additionally uses
   `sorryAx` from existing dependencies. No sorry, forbidden declaration, or
   definition occurs in the delivery. The indices obtained from descent theorems
   are eliminated inside a proof of a proposition; no definition chooses data
   from a holed existence theorem. The tail functor, diagrams and cones are
   explicitly constructed from the original diagram and pullbacks.
3. **Split-off statements: PASS (none).** No new hole, public statement or node is
   introduced. The remaining private comparison-square helper is a two-line
   pullback-cancellation argument, not a replacement descent theorem. Searched
   `lean/Sheaf`, the upstream source and Mathlib with pullback/comparison and
   descent/locally-free terms; the two reused private helpers have the exact
   required statements and were read in their original modules. A fresh recorded
   Mathlib grep for finite local freeness in AffineTransitionLimit returned no
   match. Degree zero, empty schemes, a singleton index set and a preorder with
   equivalent indices cause no additional assumptions: i₀ supplies nonemptiness,
   ji lies in the directed upper tail, and degree claims quantify over existing
   points without choosing one.
4. **Route and pruning: PASS.** Read Stacks Tag 06AC directly at
   https://stacks.math.columbia.edu/tag/06AC (the local TeX is absent here), the
   finite/flat descent statements, the degree-local-constancy theorem, the
   constructible-limit theorem and `dag/units/sk-thm-p1.json`. Step 1 uses finite
   and flat descent with exactly the available qcqs and lfp hypotheses, then
   base-change stability at a common upper bound. Steps 2–3 construct the tail
   equivalence, transport the base-changed limit, and use its qcqs affine stages.
   The degree-d locus is clopen, compact, and therefore constructible; the fibre
   degree formula places the limit image inside it. Step 4 applies eventual
   containment at j itself and the correctly oriented fibre-degree equality.
   All original proof-dependency imports remain used; the helper-host imports
   are proof-only and used solely for their proved categorical helpers. No shorter
   ready-made descent theorem was found. No unit realization or route is bypassed,
   and `## No longer needed` correctly reports no pruned original node or module.
5. **DAG agreement: PASS.** Read all four proof steps, the complete `proof_deps`
   list and each dependency's Lean/Mathlib record. The proof still implements the
   stated finite/flat descent, clopen degree locus, scheme-over-limit and
   constructible-image argument from Tag 06AC. The definitions and permanence
   nodes are used through constructors and inferred Mathlib instances. Fibre
   degree base change is the upstream implementation of the rank comparison used
   by the plan. The private helper imports add categorical glue, not dependencies
   on the host modules' descent conclusions. `proof`, `proof_deps` and
   `proof_origin` remain accurate; no new node fields are needed.

Changes by this second reader: corrected the stale claim that the constructible
image theorem is still holed, regenerated an axiom scratch copy from the repaired
module, and added this independent review. The delivered Lean proof needed no
further repair. Closed `AlgebraicGeometry.descend_finite_locally_free` (one original
hole); added zero holes and split off zero statements. The first dry run failed
only because this second-reading section was not yet present; it is rerun below.
