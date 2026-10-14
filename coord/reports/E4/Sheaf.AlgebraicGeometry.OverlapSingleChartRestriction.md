## What changed

Proved `AlgebraicGeometry.overlap_single_chart_restriction` in
`lean/Sheaf/AlgebraicGeometry/OverlapSingleChartRestriction.lean` using private,
fully proved associativity, naturality, cancellation and six-factor helpers.
All existing signatures, definitions, docstrings and imports are unchanged.
Updated the node's proof to record the completed concrete specialization.

The associativity/naturality helper proofs use the existing calculation in
`EtaleGeneratorsPullbackTargetComparison.lean`, specialized directly to Mathlib's
`Scheme.Modules.pseudofunctor_associativity` and `pullbackComp.hom.naturality`.
No import of that unrelated generator construction is needed.

The concrete theorem applies the abstract six-factor helper without simplifying
concrete chart morphisms. This compiles cleanly in 2.5 s with no new attributes;
expanding and reassociating the concrete comparison directly was too slow.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.overlap_single_chart_restriction`
(node `lem-pc-overlap-single-chart-restriction`).
One hole closed, zero holes added, zero remaining sorries in the module.
Every new private helper is proved. No new public statements or definitions.

## No longer needed

None. The only existing import, `Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons`,
is needed by the statements and the proof. Both planned proof dependencies remain
used: the canonical comparisons and inverse-image associativity (through its
Mathlib specialization). No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The node's old proof described concrete specialization as unfinished. That
specialization is now complete. No mathematical statement or unit route changed.

## Second reading by E4

1. PASS: compared the delivered Lean module and node with the repository using
   diff. All three existing declaration signatures, both definition bodies,
   docstrings, visibility and the sole import are byte-for-byte unchanged.
   Only proved private helpers and the original theorem proof were added;
   the node changes only its proof text. No change record is needed.
2. PASS: compiled the module through lcompile.py, without errors or warnings.
   A scratch copy with #print axioms for all seven private helpers and all three
   public declarations compiled and reported only propext, Classical.choice
   and Quot.sound, with no sorryAx. There are no sorries, axioms, unsafe,
   opaque, implemented_by or extern declarations and no hollow definitions.
3. PASS: zero split-off statements and zero new holes or nodes. Read every
   private helper: these are proved factorization, naturality, associativity
   and cancellation identities, not assumed replacements for the target.
   Their proofs require no nonempty chart, nonzero module or distinct-map
   assumption, and apply unchanged to empty charts, zero modules and identity
   maps. No arbitrary existence witness is selected.
4. PASS: traced the argument downward from the concrete theorem through the
   six-factor decomposition, cancellation, naturality and associativity.
   Searched lean/Sheaf and lean/WeilConjectures for alternative restriction
   comparisons and composition lemmas; msearch grep confirmed Mathlib's
   pseudofunctor_associativity. Similar helpers elsewhere are private or concern
   different comparisons; no shorter public theorem was found. The existing
   public import is needed by the signatures and definitions. Both old proof
   dependencies remain used: canonical comparisons directly, left-adjoint
   associativity through Mathlib's proved pullback specialization (whose source
   uses leftAdjointCompIso_assoc). No node or module becomes unnecessary.
   Read dag/units/sk-thm-picard-semicon.json: its route and realized fields
   are unchanged; this is a below-unit single-chart calculation.
5. PASS: the node's proof describes the actual helper calculation and concrete
   specialization; proof_deps and proof_origin agree with that route. Its
   statement and Lean record remain unchanged. No new node fields are needed.

Second reading changed only this report, adding the independent review and
compilation/axiom evidence. No Lean or DAG repair was necessary. The delivery
closes AlgebraicGeometry.overlap_single_chart_restriction: one of one original
holes, zero holes added, zero split off, and no pruning.
