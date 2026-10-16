## What changed

The assigned module arrived with zero local holes: A3's proof landed at 05:48:32 UTC,
just before this worker was dispatched at 05:48:54 UTC. This delivery repairs its
remaining redundant interface assumption instead of claiming that existing proof.

`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_comparison` now proves
its original exchange-arrow conclusion without the additional `hEncoding` hypothesis.
Its proof constructs that witness with the already-proved
`CategoryTheory.constantInternalModuleSheaf_equivalence`, using monoidality of abelian
sheafification on each scheme. Bounded devissage and the three exchange-step argument
are retained. The new import is proof-only.

Adapted `Sheaf.Paper.IntegralFiniteExchangeComparison` by removing the supplied encoding
argument and its now-unused proof-only import. Its theorem statement is unchanged.
The node records the stronger statement, actual dependency and every citer.
Change record: `coord/changes/e4-finite-discrete-encoding-hypothesis.md`.

## Proved and sorry left

Actual local hole count on receipt: 0. Holes closed: none. Holes added: none.
All delivered modules have zero local `sorry`. No split-off theorem is added.
The strengthened `finiteDiscreteExchange_comparison` is completely proved from the
library's existing declarations. This is an interface repair, not a claimed net
reduction of the sorry ledger.

The existing downstream obligation
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_coefficientRealization`
(node `lem-weil-pbc-finite-discrete-coefficient-realization`) remains unchanged in
`Sheaf.Paper.FiniteDiscreteCoefficientExchange`. It is not copied or moved into this
delivery. In particular this delivery does not claim the full target's axiom closure
is already free of `sorryAx`.

## No longer needed

Removed the proof-only import `Sheaf.Paper.ConstantInternalModuleSheafEquivalence`
from `Sheaf.Paper.IntegralFiniteExchangeComparison`; the assigned comparison now supplies
its own encoding witness. The module remains needed by the assigned comparison and
is not globally pruned. No DAG node or library module becomes unnecessary.
No new origin, coefficient-equivalence, or comparison-square statement is introduced.

## Second reading by E4

1. Compared both delivered Lean modules with the shared repository. The existing
   declaration signatures are unchanged except for the explicitly recorded removal
   of `hEncoding` from `finiteDiscreteExchange_comparison`; the adapted integral
   consumer only drops its now-invalid extra argument. The change record lists the
   sole downstream caller and its effect. Verdict: signatures and interface change
   are accounted for.

2. Compiled both modules with `lcompile.py --all`; they compile without errors and
   contain no local `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The axiom print for the two public theorems contains only the
   permitted foundational axioms plus `sorryAx` inherited from still-open imported
   declarations. Verdict: the delivered proofs are kernel-accepted and introduce no
   new holes.

3. Searched the library and ran the required `msearch.py` duplicate search for the
   encoding equivalence and comparison names. No split-off theorem or duplicate
   statement was added; the proof uses the existing
   `constantInternalModuleSheaf_equivalence`. Verdict: no new-node or duplication
   defect.

4. Read the proof from the target downward. It follows the existing exchange-step
   realization and bounded devissage, constructing the encoding witness by the
   shortest available library theorem. The new equivalence import is proof-only;
   the adapted module removes its unused proof-only import. No old proof dependency
   is unused, and no module or unit route is pruned. Verdict: route and imports are
   minimal for the changed proof.

5. Checked the changed DAG node against the Lean proof: its first proof step records
   the constructed encoding witness, `proof_deps` includes the equivalence and the
   two existing exchange lemmas, and `proof_origin` records the interface repair.
   The unit's realized route and all existing downstream references remain intact.
   Verdict: DAG and Lean agree.

Changed only the finite-discrete comparison theorem and its forced integral consumer
adaptation, plus the corresponding node/change record and this review report.

## Where the brief, the DAG or earlier work was wrong

The dispatch described an open hole in the assigned module, but the live shared branch
already contained its proof. The node's additional encoding hypothesis was stronger
than the assumptions needed for its source: the library already proves precisely
that encoding without extra assumptions. We remove that hypothesis; no target
statement, universe, definition, or unit route changes. Empty schemes and the zero
ring are covered by the existing constant-module equivalence.

The changed node's sole citer remains valid: it receives the same conclusion with
fewer assumptions. The complete transitive consumer review and old/new signatures
are in the change record. Exploratory concrete encodings and origin adapters were
not needed and remain outside the delivered Lean tree.
