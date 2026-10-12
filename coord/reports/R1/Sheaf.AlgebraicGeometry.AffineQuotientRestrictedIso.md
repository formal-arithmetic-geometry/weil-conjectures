## What changed

Filled `AlgebraicGeometry.affine_quotient_restricted_iso`. The proof imports
`WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` for the affine spectrum
pushforward/tilde comparison, and defines the needed restriction/pushforward
comparison helpers. The open-restriction comparison is written inline at its sole
use, so the module does not redeclare the statement already present in
`Sheaf.AlgebraicGeometry.PushforwardRankOnOpen` (the reason for this repair). It
transports the spectrum comparison along `hU.isoSpec` and `e`, then uses `he` to
identify the resulting morphism with `i ∣_ U`.

## Proved and sorry left

The theorem `affine_quotient_restricted_iso` is proved. No `sorry` remains in the
item's module, and no new theorem with `sorry` was added.
Holes closed: `AlgebraicGeometry.affine_quotient_restricted_iso` (1 of 1).
Holes added: none (0 split off). This is a proof, not a decomposition.
Single-file compilation is clean. `#print axioms` for the theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed `def-pc-module-pullback` from the node's proof dependencies: its module
`Sheaf.AlgebraicGeometry.TensorPullback` and explicit tensor pullback construction
are not needed. The actual proof uses only Mathlib restriction/pushforward functors
and their composition and unit isomorphisms. The dependency remains a statement
dependency naming the notion. No original Lean import was removed; both public
Mathlib imports are needed by the unchanged statement. No unit realization was
bypassed. Whether TensorPullback leaves the target closure also depends on its
other users.

## Where the brief, the DAG or earlier work was wrong

The original plan described a basis gluing proof. The existing affine tilde
adjunction and canonical restriction/pushforward isomorphisms make that gluing
unnecessary; the proof is a categorical transport of the same basic-open comparison.
The earlier delivery introduced a private theorem whose statement duplicated
`AlgebraicGeometry.Scheme.Modules.pushforward_restrict_iso`; the comparison is now
constructed inline, leaving the public interface unchanged.


## Earlier second reading (a previous round; superseded)

1. Interface — PASS. Diffed the sole delivered module against the repository.
   The existing theorem signature and docstring are byte for byte unchanged;
   no definitions, public imports, visibility or existing attributes changed.
   The sole added import is proof-only. No change record is required.
2. Proof — PASS. Independently compiled the module using lcompile.py without
   errors or warnings. A scratch copy with #print axioms checks the target and
   all three private helpers: only propext, Classical.choice and Quot.sound.
   No sorry, axiom, unsafe, opaque, implemented_by, extern or hollow definition
   occurs. Isomorphisms are constructed from proved categorical comparisons;
   there is no data selected from an unproved existence statement.
3. Split statements — PASS (none). No new public statement or remaining hole.
   Read each helper: open restriction compares the same inverse-image opens
   and checks scalar compatibility via morphismRestrict_app; the isomorphism
   helper uses the invertible restriction counit; the spectrum helper uses the
   invertible tilde counit and the proved global-sections comparison. These
   constructions require no nonzero ring or nonempty open assumption, so they
   cover I = top, I = bottom, and empty U.
4. Route and pruning — PASS. Independently searched Loogle for
   "restrictFunctor", "pushforward" (no hits), and searched Mathlib's Modules
   Sheaf/Tilde files and the library for restriction/pushforward isomorphisms.
   The reusable public tools used here are the existing Mathlib comparisons
   and the upstream global-sections isomorphism. The matching open restriction
   helper in PushforwardRankOnOpen is private, so reproducing its proved local
   construction avoids importing that module. All imports are needed. The only
   old proof dependency pruned is def-pc-module-pullback, fully reported above.
   Read dag/units/sk-thm-picard-duality.json: its realized statement and step
   lists are empty; this change bypasses no unit realization or unit-level step.
5. DAG — PASS after repair. The proof steps describe the Lean transport, and
   proof_origin remains the same affine comparison source. Added the existing
   lem-weil-pbc-pushforward-spec-global-sections node to the first step's uses
   and to proof_deps, since pushforwardSpecMapCompΓIso is explicitly used.
   No new nodes or statement changes.

Second reading changed only the missing DAG dependency and this report; the
Lean proof was retained unchanged.

## Second reading by R1

1. Interface — PASS. Compared the delivered module with the repository version. The existing theorem signature and docstring are unchanged; only the proof-only import and proof body differ. No public declarations or definitions were changed.
2. Proof — PASS. Compiled the module with lcompile.py. The proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; its categorical constructions use proved isomorphisms and no arbitrary data. The scratch axiom check reports only propext, Classical.choice, and Quot.sound for the target and private helpers.
3. Split statements — PASS. No statements were split off and no new holes were added. The private helpers are local constructions, and the quotient, unit, and empty-open edge cases are covered by the categorical isomorphisms.
4. Route and pruning — PASS. The proof uses the affine tilde/pushforward comparison, restriction along isomorphisms, and the sectionwise restriction comparison. The old tensor-pullback dependency is not used; the open-restriction comparison is constructed inline, avoiding a duplicate public theorem. The unit route remains via the affine pushforward comparison.
5. DAG — PASS. The node proof and proof dependencies match the Lean proof, including the global-sections comparison dependency; no statement text changed. No new nodes were added.

Changed only the report and retained the verified Lean proof and DAG repair.
