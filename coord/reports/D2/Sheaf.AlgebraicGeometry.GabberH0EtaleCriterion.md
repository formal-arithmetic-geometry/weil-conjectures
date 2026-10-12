## What changed

Reduced `AlgebraicGeometry.gabber_h0_etale_criterion` along two parts of Stacks Tag 09ZF:
injectivity from the Zariski hypothesis, which is now proved from the existing comparison
lemma, and a finite lift with its projection equalizer equation and closed restriction
compatibility, which remains a named intermediate theorem. The main module
contains the complete finite-descent and cancellation argument, rather than an application
of a renamed criterion. Its original signature and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.GabberH0EtaleInjective` and
`Sheaf.AlgebraicGeometry.GabberH0FiniteLift`, each with one public named theorem, source,
full proof in words, and a matching node. Updated the criterion node's proof and
proof dependencies to the actual reduction. No definition or existing statement changes.

Four private, proved helpers establish the composition-unit formula, finite-surjective
unit injectivity on any terminal étale object, injectivity after the composition
comparison, and transport of a unit along equality of morphisms. The final proof uses
finite descent to construct a section on X, applies injectivity on the closed base change,
and checks the two composite pullbacks explicitly. Broad rewrites initially produced a
kernel timeout; narrowly typed congruence and transitivity proofs compile in seconds.

The original source text was read at the locally available copy of
`etale-cohomology.tex`, lines 14974–15080, and the current online Tags 09ZF and 09Z3
were checked. The unit `sk-thm-iff` realizes its own statement and step in
`lemma-weil-pbc-property-iff-acyclicity`; this delivery preserves the invoked 09ZF route.

## Proved and sorry left

Proved from named intermediate statements: `AlgebraicGeometry.gabber_h0_etale_criterion`
(node `lem-weil-pbc-gabber-h0-etale-criterion`). Its only original sorry is removed.
All four private helpers in the criterion module are proved; none has a sorry.
Also proved: `AlgebraicGeometry.gabber_h0_etale_injective`, node
`lem-weil-pbc-gabber-h0-etale-injective`, in `GabberH0EtaleInjective.lean`. It constructs
canonical Zariski restriction sheaves, the open base-change isomorphisms, and the
terminal isomorphism, and uses the existing comparison's unit equation and injectivity.
Its continuity helper is also proved.

All three delivery modules compile cleanly in dependency order, in 3.1, 2.6, and
4.6 seconds respectively before the final import cleanup; the dry run is the final check.

One sorry added, the whole proof of its public theorem:

- `AlgebraicGeometry.gabber_h0_finite_lift`, node
  `lem-weil-pbc-gabber-h0-finite-lift`, in `GabberH0FiniteLift.lean`.

The first assumes only universal Zariski bijectivity and asserts injectivity, with no
qcqs or finite-base-change hypothesis. The second constructs a section on a finite
surjective cover and proves its two compatibility equations; it asserts no section on X.
Finite descent and the final equality on Z are proved in the criterion module.
The result still depends transitively on the existing Zariski inclusion, comparison,
composition and finite-descent statements with sorry. This is a reduction, not a claim of axiom-free target completion.

Edge cases checked mathematically: identity closed immersion, empty X and Z, and empty
Z with nonempty X (excluded by the Zariski hypothesis). In the identity case the finite
lift can use the identity cover. On the empty scheme, the empty covering forces the
section sets to be singletons. No nonemptiness of the scheme or coefficient set was added.

## No longer needed

Removed direct proof imports from the criterion module:
`Sheaf.Paper.GabberZariskiEtaleRestrictionInjective`,
`Sheaf.Paper.SiteSheafificationSectionsLocal`,
`Sheaf.Topology.ClosedPushforwardConstantStalks`, and
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement`.
Their nodes remain needed by the new intermediate modules, so none is globally pruned.
The original local-representation, shrinking, finite-refinement, and Zariski-gluing
nodes remain in the finite-lift node's proof dependencies. No unit statement or step,
and no mathematical input of the source argument, is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement discrepancy found. The comparison theorem requires explicit Zariski restriction sheaves and canonical
base-change identifications; it is not directly a global-section injectivity theorem.
The new injectivity module constructs those objects and proves the consequence. The local-representation and gluing declarations likewise do not
directly provide a finite lifted section with the two needed equations; the finite-lift
node states precisely that remaining portion of the plan.

The repository's `literature/stacks-project/etale-cohomology.tex` is absent on this machine;
a local source copy and the current Stacks pages were available. LeanSearch returned
HTTP 500 for both new-node searches and is recorded as unavailable, not as a negative
search result. LeanFinder and Mathlib grep found no matching theorem. Blueprint searches
for Gabber and finite surjective facts found no existing node stating either new part.

## New nodes

`lem-weil-pbc-gabber-h0-etale-injective`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-h0-etale-injective.json` and
`lean/Sheaf/AlgebraicGeometry/GabberH0EtaleInjective.lean`. The first two proof paragraphs
of 09ZF, including the canonical Zariski restriction objects and terminal-object
transport, are now proved from the existing comparison theorem. This node has no new
sorry and does not introduce further work.

`lem-weil-pbc-gabber-h0-finite-lift`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-h0-finite-lift.json` and
`lean/Sheaf/AlgebraicGeometry/GabberH0FiniteLift.lean`. Original plan steps 0–9 are kept
as the remaining local construction, ending before finite descent; its statement gives
the exact equalizer and composition-transport equations consumed by the main proof.

No change record is needed: all existing public statements, definitions, and public
imports are unchanged; new imports of the criterion are private proof imports.

## Second reading by D2

1. **Statements and signatures.** Compared the delivered criterion module with the repository
version byte for byte at every existing declaration. The target statement and all existing
definitions are unchanged; the two added public theorem signatures match their DAG
`lean.statement` fields exactly. Verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`. The criterion
and injectivity theorem contain no `sorry`; the only remaining `sorry` is the named
`gabber_h0_finite_lift`, with its source, proof sketch, and node recorded above. No
forbidden declarations occur. Completed declarations use only permitted logical axioms;
the split theorem necessarily reports `sorryAx`. Verdict: pass.

3. **Split statements and search.** Checked both split statements on identity and empty
scheme edge cases and searched the library and available Mathlib declarations by name and
concept. The injectivity statement is the needed first consequence, and the finite-lift
statement stops before descent and asserts exactly the two equations consumed by the
criterion. Neither duplicates an existing declaration. Verdict: pass.

4. **Pruning and route.** The criterion proof follows the finite-lift, finite-descent,
comparison-injectivity route and keeps the `sk-thm-iff` unit realization. Four proof-only
imports no longer needed by the criterion were removed and are listed above; dependencies
still needed by the split finite-lift proof remain in that module. Verdict: pass.

5. **DAG agreement.** Compared each node's statement, proof steps, `proof_deps`,
`proof_origin`, Lean declaration, and module path with the delivered code. The criterion
node records the actual reduction; both new nodes have complete metadata and matching
docstrings. Verdict: pass.

Changed during second reading: added this review record only; no Lean statements or proofs
were altered.
