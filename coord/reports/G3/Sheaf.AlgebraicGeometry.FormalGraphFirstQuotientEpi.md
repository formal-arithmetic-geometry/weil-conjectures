## What changed

Closed `AlgebraicGeometry.formalGraph_first_quotient_epi` in
`Sheaf.AlgebraicGeometry.FormalGraphFirstQuotientEpi`, with its existing statement and
visibility unchanged. No definitions or other modules changed.

The proof uses the existing theorem `formalCompletion_exact` to preserve coherent
pullbacks and kernels. Five proved private helpers extract finite-limit preservation,
prove coherence of the ordinary pullback, lift through the completed pullback and kernel,
and detect a zero formal morphism from one level when its target has a uniform
annihilation bound. The completed pullback lift of
`(id, theta)` kills the discrepancy at level n. Quotient annihilation, stabilization,
and epimorphic source transitions make it zero at every level. The resulting lift into
the completed kernel is a section of the completed first projection. At index zero it
gives an epi on first quotients, and precomposition with the kernel quotient projection
proves the required epi.

Added proof-only imports of `FormalCompletionExact`, `CoherentKernelCokernelSum`,
`CoherentFormalModuleKernelFactorization`, Mathlib's `ShortComplex.ExactFunctor` and
`Limits.Preserves.Shapes.Pullbacks`. A proof-only `import all CoherentFormalModule`
uses already proved ideal-product helpers, without making their declarations public.
The kernel-factorization module is used only for its proved `formalTransition_epi`.
Updated the item's node proof, dependencies and origin to the actual categorical route.
No unit statement or realized unit step is bypassed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.formalGraph_first_quotient_epi`
(node `lem-weil-pbc-formal-graph-first-quotient-epi`).
Added zero holes. No `sorry` remains in the delivered module, including its five
private helpers. This is a proof from existing declarations, not a decomposition.
The imported declarations retain their own existing dependency closure.

## No longer needed

Removed imports `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` and
`Mathlib.RingTheory.AdicCompletion.Exactness` from this module.
The item's direct proof no longer needs
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-coherent-formal-modules-affine`, or
`lem-weil-pbc-completion-exact-finite-modules`: their work is already encapsulated
by `lem-weil-pbc-formal-completion-exact`. The corresponding modules
`Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`, and
`Mathlib.RingTheory.AdicCompletion.Exactness` are unnecessary as direct dependencies.
This does not assert they leave the targets' transitive closure: exact completion
itself still uses the affine theory and finite-module completion facts.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The plan required more affine dictionary
work than the proof needs now that `formalCompletion_exact` is available.
The proof preserves categorical formal kernels, never assumes evaluation preserves
kernels, and uses evaluation only on an explicit retraction equation.

Small cases remain covered by the unchanged hypotheses: J=0 gives ordinary graph
reduction; J=1 gives a zero target quotient. Zero modules, n=0, and the empty scheme
require no special hypotheses or case exclusions.

The cited local Stacks source files are absent on this machine. Read the authoritative
online [Tag 0881](https://stacks.math.columbia.edu/tag/0881) for exact coherent completion
and [Tag 0889](https://stacks.math.columbia.edu/tag/0889) for the comparison context.
The graph lemma is an auxiliary consequence implemented through the exactness route.
LeanFinder, Loogle, and grep searches ran through `msearch.py`; they found generic
completion or exact-functor tools, no existing graph theorem. Single-file compilation
passes without errors or warnings (about seven seconds); delivery dry run is the final
mechanical check.

## Second reading by G3

1. **Visible declarations.** Compared the delivered module with the repository version. The
public theorem signature, statement, namespace, and visibility are byte-for-byte unchanged;
only imports and proof text changed. The DAG node records the same statement and the actual
proof route.

2. **Proof and trust.** Compiled the module with `lcompile.py` successfully. The module has
no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the five private
helpers are ordinary proved theorems. A scratch-copy `#print axioms` check reports exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the existing dependency
closure. The categorical argument uses exactness, pullback and
kernel universal properties, and the level-zero retraction, so no hollow definition or
arbitrary witness is introduced.

3. **Statements and searches.** The target statement is unchanged and its edge cases (zero
ideal, unit ideal, zero modules, and index zero) introduce no extra hypotheses. The added
DAG proof dependencies are existing declarations, and the recorded searches found no
Mathlib, upstream, or Sheaf theorem duplicating this graph conclusion. No new split-off
statement was added.

4. **Route and pruning.** The proof keeps the `sk-thm-p1` unit route through coherent
completion exactness and coherent kernels. It removes only affine and adic-exactness imports
that the exact-completion theorem now subsumes; the removed nodes are listed above under
“No longer needed”.

5. **DAG agreement.** Updated `proof`, `proof_deps`, and `proof_origin` to match the Lean
proof. The unit's `realized` record is untouched. No definition or target statement changed.

Changed after this reading: added this review record only; no Lean proof repair was needed.
