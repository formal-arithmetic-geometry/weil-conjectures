## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleGeneratorsPullbackTarget_naturality`
in `Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackTargetComparison`.
Four proved private helpers implement comparison associativity, comparison
naturality, the commuting-square identity, and its compatibility with an
arbitrary morphism from the abstract pullback. The public theorem specializes
the last helper to the inverse tensor/abstract pullback comparison.
All existing signatures, definitions, visibility and docstrings are
unchanged. Removed the unused proof-only import
`Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections`. The node proof now records this argument and drops the unused
generator-section proof dependency. No interface change or new module.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Modules.etaleGeneratorsPullbackTarget_naturality`
(node `lem-sc-etale-generators-pullback-target-comparison`).
No sorry remains in the assigned module; no hole was added.
The helpers `compOfEq_assoc`, `compOfEq_naturality`, `square_comp`, and
`square_comp_map` are private and fully proved. This is a proof, not a
decomposition. Single-file lcompile.py passed without errors or warnings.
The author's first dry run passed compilation and preflight, but axiom probes
then timed out under contention; nothing was pushed. The second reader has now
checked the theorem with explicit `#print axioms`: only `propext`,
`Classical.choice`, and `Quot.sound`. The second reading below records the
final proof adjustments and delivery checks.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections`; both existing public
imports are needed by the signatures and definitions. The proof does not use
`lem-sc-etale-generators-pullback-section` or its module
`Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections`; removed that node
from proof_deps. This does not assert that other targets cease to reach it.
Neither `etaleGeneratorsPullbackSource_naturality` nor an invertibility
hypothesis is needed; the imported source-comparison module remains necessary
for the actual square-isomorphism definition.

## Where the brief, the DAG or earlier work was wrong

The original planned generator-section dependency is unnecessary for this
coherence identity. The original mathematical argument is valid and preserved.
The compiled source-comparison module was initially unavailable; it arrived
during the session, so that temporary tooling blocker is resolved.
Unfolding `Iso.app` in the final identification made elaboration exceed the
single-file limit. Using its projection lemmas `Iso.app_hom` and `Iso.app_inv`
instead compiles within the limit, without changing any definition or raising
heartbeats. Searches with msearch.py (Loogle, LeanFinder and grep), plus local
rg, identified Mathlib `pseudofunctor_associativity` and
`SheafOfModules.pullback_assoc`; the former supplies the threefold coherence.

## Second reading by U1

1. Compared every delivered Lean module (one) against the repository with
   `diff -u`. The public definition's body, signatures, visibility and docstrings
   are unchanged. Restored the exact original whitespace before the theorem's
   `:=`. Only proved private helpers, the theorem proof and an unused plain
   import changed. No target or interface change; no change record is needed.
2. Read all four helper proofs and the final specialization. They use equality
   induction, Mathlib pullback associativity, naturality and cancellation of
   isomorphisms. No sorry or forbidden declaration occurs in the delivery;
   neither definition nor data construction changed. Explicit `#print axioms`
   on both public declarations returned only the three standard axioms. The
   final source with those probes compiled without warnings in 52.8 seconds.
   The delivery checks are recorded below.
3. No statements were split off and no holes or nodes were added. The proved
   private helpers express strict intermediate coherence identities, not a
   renamed target. Checked identity arrows, zero modules and empty schemes:
   the functorial identities remain valid without extra hypotheses. Independent
   Loogle, LeanFinder and grep searches through msearch.py, plus rg in the
   library, found the Mathlib coherence primitive already used, but no public
   statement of this complete square identity.
4. The proof takes the direct Mathlib coherence route. Both public imports
   supply declarations used in the unchanged signatures/definition; the unused
   plain sections import is removed. The report lists the sole removed original
   proof dependency. Read `dag/units/sk-prop-ext-invariance.json`: no realized
   statement or step is bypassed; only this subordinate comparison argument is
   simplified. No unit or chapter route changed.
5. Compared the node JSON: only proof, proof_deps and proof_origin changed.
   The remaining dependencies supply module pullback and the square comparison
   definition; the proof does not invoke the source-naturality hole or the
   generator-section hole. The recorded steps match the three associativity
   specializations, cancellation, naturality and tensor-comparison substitution.
   The recorded Lean statement remains verbatim; no new-node checks apply.

Changes by the second reader: corrected the report's false claim that no import
was removed, restored signature whitespace, specified the helper's destination
module explicitly, and normalized the goal and helper equality separately before
`exact h` to avoid expensive premature definitional comparison. The mathematical
argument and public API are unchanged.

Final validation: deliver3.py --no-push printed OK (commit 9c7f87fd0c),
with a clean single-file compile and passing preflight. Review class is CODEX
because the node file changes. Its all-declaration probe timed out at 60 seconds;
this is not recorded as a successful probe. The separate explicit axiom checks
on both public declarations succeeded as recorded above, covering the theorem's
private proof dependencies transitively. No hole was added: 1 closed, 0 added.
The removed sections import/dependency is not a claim of whole-closure pruning:
the source-comparison module still imports the sections module.
