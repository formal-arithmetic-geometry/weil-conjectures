## What changed

Repaired the returned delivery by removing the duplicate private theorem declaration
`AlgebraicGeometry.isFiniteType_over`. Its finite-type restriction construction is now a
local helper inside `coherent_algebra_affine_finite_proper`, while the public theorem and
all signatures remain unchanged. This avoids redeclaring the word-for-word theorem
identified by `import_prune_check.py`.

## Proved and sorry left

Closed `AlgebraicGeometry.coherent_algebra_affine_finite_proper`; no sorry remains in this
module and no new holes were added (one hole closed, zero added).
This theorem still depends on existing open imported statements, including
`AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine` and
`AlgebraicGeometry.Scheme.Modules.module_support_proper_over_base`;
its axiom probe therefore includes `sorryAx`. This is a local hole closure, not a claim
that the theorem's entire dependency closure is proved.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`.
Removed old proof dependencies `lem-weil-pbc-affine-morphism-relative-spec` and
`def-pc-fibre-product`: sectionwise finiteness uses the assumed affineness directly,
and properness uses the closed-immersion lift instead of a fibre product.
No other old proof dependency is removed. These are dependencies pruned from this item;
no claim is made that their modules are now outside the whole target import closure.
The duplicate private theorem declaration is removed; its construction remains locally
necessary for the finite morphism argument.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private declaration whose statement duplicated an
existing library statement and was rejected by the import-pruning checker. The repair keeps
the proof construction local and compiles successfully.

## Forced adaptations

None.


## Second reading by C2

1. Compared the delivered Lean file with the repository file by `diff` and compared
   the complete existing theorem signature byte for byte: unchanged. The only public
   declaration is `AlgebraicGeometry.coherent_algebra_affine_finite_proper`; no definition
   is added or changed. All seven public imports are unchanged. The removed import is
   proof-only. No interface change or forced adaptation requires a change record.
   Read Stacks [09ZT](https://stacks.math.columbia.edu/tag/09ZT), final proof sentence,
   and [0CYS](https://stacks.math.columbia.edu/tag/0CYS), its proper-support characterization:
   the proof establishes the same finite and proper conclusions without changing any
   of the Lean hypotheses. Verdict: pass.

2. Read the entire proof and compiled a scratch copy with `#print axioms` appended.
   It compiled without errors or warnings in 36.7 seconds after the repair below.
   The probe reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
   from existing open imports. The delivered file contains no `sorry`, new axiom,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. The algebra-isomorphism component
   is linear by its Under equation, and its inverse proves surjectivity. Annihilation
   applied to the algebra unit gives kernel inclusion; the closed-immersion lift then
   cancels finiteness and composes proper morphisms. The existence witness for Z is
   eliminated inside this proposition proof, not used to define arbitrary public data.
   Verdict: pass, conditional only on the existing open dependencies.

3. No statements are split off and no nodes are added. The local finite-type restriction
   argument pulls back a covering family and maps each finite generating family with
   a left-adjoint module functor. The zero algebra and empty realization need no
   nonzero-ring or nonempty-scheme assumptions: the unit-annihilation computation and
   finite-module transport still apply. Searched `lean/` with restriction and finite-type
   terminology, and searched Mathlib via `msearch.py` grep and LeanFinder. Results give
   the local-generators primitives used here, not a public restriction theorem. The
   identical existing helper in `FinitePushforwardCoherent` is private and inaccessible;
   the delivered argument remains local and adds no duplicate declaration. Verdict: pass.

4. Read from the top down: coherence gives quasi-coherence and finite type; the affine
   section criterion and Mathlib `isFinite_iff` prove finiteness; proper support and
   Mathlib `IsClosedImmersion.lift`, `IsFinite.of_comp`, and proper-composition instances
   prove properness. This avoids the old relative-spectrum and fibre-product route.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node is not one of its `realized`
   statement/step nodes; the changed route is below unit level. The sandbox DAG already
   describes this route correctly. Corrected `No longer needed` to list both deleted
   old DAG dependencies and the removed import; the preceding report omitted them.
   Verdict: pass.

5. Compared the node JSON with the repository: only `proof`, `proof_deps`, and
   `proof_origin` differ. The two steps describe the actual sectionwise finite-module
   transport and kernel-factorization proof, and their `uses` union equals `proof_deps`.
   The six remaining dependencies agree with the existing definitions, imported
   coherent/affine/support statements, and Mathlib finite/proper facts. No new node
   field checks are needed. Corrected `proof_origin` from "Private" to "Local" helper
   to match the returned-delivery repair. Verdict: pass.

Changes from this second reading: the first compile timed out at 60 seconds because
its local restriction helper specialized `F` to `B.toModule` and introduced reducible
aliases `let F := B.toModule` and `let X := X`. Made that local helper quantify over
`X`, `F`, and `[F.IsFiniteType]` explicitly, and passed `X B.toModule` at its use.
This changes only the proof, removes those expensive reducible aliases, and compiled
in 42.3 seconds. Added the required explanatory comment for the heartbeat setting;
the subsequent axiom-probe compile is clean. Corrected the pruning report and the
helper description in `proof_origin`; no mathematically correct argument was replaced.
