## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_pushforward_free_evaluation` in
`Sheaf.AlgebraicGeometry.AffinePushforwardFreeEvaluation`, with its signature and existing
public imports unchanged. Added private, fully proved scalar-restriction and over-site
transport helpers. The proof transports the evaluation to O_V-modules, proves source and
target quasi-coherent, and applies the existing affine image formula and affine-cover
surjectivity criterion. The finite free source is handled by preservation of finite
coproducts by an additive functor. No finite-type assumption is used.

Added proof-only imports of
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`.
Updated the existing node's proof, proof dependencies and proof origin to this route.
The affine pushforward theorem is a proved tool from another unit; it does not change
any step of the assigned unit, and this node is not one of that unit's realized steps.
The original declaration docstring is preserved; its inverse-image plan is replaced
by the scalar-restriction route recorded in the DAG and implemented in the proof.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.affine_pushforward_free_evaluation`
(node `lem-weil-pbc-affine-pushforward-free-evaluation`).
No holes remain in the delivered module; no holes or nodes are added.
The two private helpers are fully proved. The proof handles arbitrary finite I,
including the empty index type, arbitrary quasi-coherent F, and the empty affine open.

## No longer needed

No original imports were removed: all three public Mathlib imports support the unchanged
statement. The broad `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage` and explicit
module-sheafification proof imports used during development were removed in favor of
the specific affine-morphism module and its existing imports.

The revised proof does not use these old direct proof dependencies:

- `def-pc-module-pullback` / `Sheaf.AlgebraicGeometry.TensorPullback`.
- `lem-weil-pbc-spec-tilde-free-module` / the `tildeFinsupp` comparison in
  `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `lem-weil-pbc-affine-tilde-gamma-adjunction` / the tilde-Gamma adjunction in
  `Mathlib.AlgebraicGeometry.Modules.Tilde`.

These node edges are removed. No claim is made that the shared Mathlib Tilde module
leaves the transitive import closure: existing quasi-coherence results still use it.
There is no inverse-image free evaluation comparison or pushforward epi comparison
left to formalize. The image formula, affine restriction and generating-evaluation
interfaces remain used. The new direct dependencies are the existing nodes for
affine pushforward quasi-coherence, coproduct closure and affine-cover epimorphy.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's inverse-image free-module comparison is
unnecessary below the unit level: restricting scalars preserves the underlying
abelian sheaf, so epimorphy can be tested on ordinary quasi-coherent O_V-modules.
The finite free source remains quasi-coherent because the transport is additive and
I is finite. The existing source lemmas provide the complete argument.

The declaration needs a local heartbeat increase because transport through the
scalar-restriction and over-site functors unfolds several module ring actions;
its single-file compile remains within the required 60-second limit.

## Second reading by J1

1. **Unchanged interfaces — PASS.** Compared the sole delivered module with the
   repository by `diff` and checked the existing theorem signature byte for byte.
   The theorem, variables, notation, docstring and public imports are unchanged.
   Only two proof imports, private helpers and the proof are added. No target,
   existing definition, statement or visibility changes; no change record is needed.
2. **Proof and axioms — PASS.** Independently compiled the module cleanly in 29.2 s.
   A scratch copy with `#print axioms` for the theorem and both private helpers
   compiled in 32.6 s: each uses only `propext`, `Classical.choice`, `Quot.sound`,
   with no `sorryAx`. The delivered file has no `sorry` or forbidden declarations.
   `scalarOver` is the explicit composite of existing functors; it chooses no
   arbitrary object from an unproved existence statement.
3. **Split statements and small cases — PASS.** There are no split-off statements
   or new public declarations. Checked the scalar-restriction epi comparison via
   the identical underlying abelian-sheaf maps, and the over-site terminal-object
   equality. The finite-coproduct argument includes empty I, and the top-open
   affine-cover argument includes the empty affine scheme. No finite-type or
   nonemptiness hypothesis is introduced.
4. **Route, search and pruning — PASS.** Read the affine-pushforward,
   quasi-coherent image, coproduct and affine-cover declarations used by the proof.
   Repeated Loogle search for scalar restriction and a grep search for affine
   surjectivity/quasi-coherence; inspected the upstream module sources. The useful
   affine-surjectivity helper is private in the image module, so the existing public
   image formula supplies the short available route. Both new imports are proof-only
   and used. All three discarded old direct dependency edges are listed in
   `No longer needed`; no unsupported transitive-module pruning is claimed.
   Checked `dag/units/sk-thm-p1.json`: this node is not a realized unit statement
   or step, and its realized route is unchanged. The proved affine-pushforward
   result is used as a generic tool, as permitted by SETUP.
5. **DAG agreement — PASS.** Compared the node JSON with the repository: only
   `proof`, `proof_deps`, `proof_origin` change. The dependency set is exactly the
   union of the steps' `uses`, and the named declarations match the Lean proof.
   No new nodes, signatures or change records are added.

Second reading changed only this report by recording the independent checks;
no repair to the Lean proof or DAG was needed. One original hole is closed and
zero holes are added, rather than a decomposition.
