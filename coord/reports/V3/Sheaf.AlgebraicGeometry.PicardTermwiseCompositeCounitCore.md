## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.picard_termwise_counit_composition`
with the actual evaluation of the pinned left-derived-lift equation. The proof
identifies the quotient counits and the tensor comparison, then cancels only the
derived and underived comparison isomorphisms. The original public import,
signature and docstrings are unchanged. Private proved helpers control
normalization; there are no new definitions.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.picard_termwise_counit_composition`
(node `lem-sc-picard-termwise-composite-counit-core`).

Holes added: none. No local sorry remains. Imported statements may still be open;
this delivery does not claim to close their proofs.

The first draft's `AlgebraicGeometry.Scheme.picard_termwise_counit_factorization`
was removed, together with its new module and proposed node. Its equation was
equivalent to the item by cancellation, so moving the hole there was not progress.

## No longer needed

No original import or old proof dependency is removed. The only original import,
`Sheaf.AlgebraicGeometry.PicardTermwiseModels`, supplies the public statement and
the proof's definitions and pinned composition equation. No existing module is
pruned from the targets' closure.

The rejected draft's new factorization module and node are absent from delivery.
The generic inverse-factorization helper has been replaced by a proved helper
that uses functor maps directly, avoiding construction of a concrete mapped iso.

## Where the brief, the DAG or earlier work was wrong

The first draft incorrectly called the equivalent factorization a strictly simpler
statement and reported vague pruning of helpers that were never original imports
or proof dependencies. The second reader rejects that decomposition. The actual
proof must evaluate the existing left-derived-lift equation, and does so here.

Earlier complete proof attempts exceeded the file limit: the local chosen-data
expressions and concrete comparison normalization were expensive to check.
Explicitly typed local choices, the existing left-derived-factorization lemma
and an abstract categorical cancellation helper control those expansions without
changing any exported definition or the limit.

The proof-dependency list now explicitly includes the definition of the tensor
composition comparison used to identify the underived comparison.

## Second reading by V3

1. Compared the delivered module with the repository version. The existing public
   theorem signature is byte for byte identical, as are its docstrings and public
   import. There is no target, statement or exported definition change. Local proof
   environment changes are recorded in
   `coord/changes/picard-termwise-counit-core-proof-environment.md`.
2. The complete module compiled in 55.1 seconds, with zero local holes and no
   forbidden declarations. Style warnings were then repaired. The final compiler
   and axiom checks are recorded below.
3. Rejected and removed the only split-off statement: its converse is the original
   theorem by cancellation, so it was a restatement. No new unproved statement or
   node remains. Searched Mathlib with Loogle for `leftDerived_fac_app`, Lean Finder
   for counits after the homotopy quotient, and the library for the pinned counit
   equation and conjugate-isomorphism projection lemmas. The proof uses the existing
   left-derived factorization lemma and conjugate-isomorphism lemmas. It cancels no
   counit and imposes no nonzero, K-flatness or invertibility assumption on K; thus
   zero complexes, identity morphisms and empty schemes require no extra case.
4. Read the unit `sk-prop-av-cube` and its `realized` record. This calculation is
   below the unit level; no unit route or realization is changed. The original
   statement import is retained and no proof-only public import is added. The
   pruning report now names the exact absence of original pruning.
5. Read the existing node and compared its proof route with the Lean calculation.
   Updated only `proof`, `proof_deps` and `proof_origin`: evaluate the pinned lift,
   transport through the quotient, identify the tensor comparison, and cancel the
   comparison isomorphisms. The new dependency is the existing tensor composition
   definition node. No proposed factorization node is delivered.

Second-reading changes: removed the equivalent sorry-backed factorization and its
module/node; restored the real reduction from the pinned comparison equation;
repaired normalization and cancellation; corrected the report, proof-environment
record and node proof metadata.

Final validation: `deliver3.py V3 Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore
--no-push` printed OK: the complete module and all-constant axiom probe compiled
and the stage-3 preflight passed. No local sorry or forbidden axiom was found.
The review class is CODEX because node metadata and local command changes are
recorded. Delivery contains one Lean module, one existing-node metadata update,
one proof-environment change record and this report.

An independent scratch copy with `#print axioms` compiled in 57.8 seconds and
reported exactly `[propext, Classical.choice, Quot.sound]` for
`AlgebraicGeometry.Scheme.picard_termwise_counit_composition`; no sorryAx is reachable.
