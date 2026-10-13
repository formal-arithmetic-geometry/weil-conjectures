## What changed

The unchanged theorem `HomologicalComplex₂.verticalCutoff_comparison_kernel_twoTerm`
now has a complete Lean proof. It proves support away from the two endpoints
using evaluation of kernels/cokernels and the actual truncation coordinates.
A proved private categorical lemma identifies the endpoint kernel differential
with the abelian coimage-to-image comparison. A new proof-only import supplies
the remaining boundary kernel/cokernel universal properties, in the new module
`Sheaf.Algebra.Homology.VerticalCutoffEndpointForks`.

The reduction does not assume either conclusion about `kernel q`. The new theorem
has no `q` argument and states universal properties of the original cutoff inclusion
and canonical truncation projection. The support assertion, transport to coimage
and image, chain-map compatibility, and isomorphism cancellation are proved here.
The original public import and every existing signature and visibility are unchanged.

Repair of the returned delivery: removed the duplicate private declarations
`HomologicalComplex₂.inclusion_f_isIso`, `HomologicalComplex₂.pi_f_above`,
and `HomologicalComplex₂.truncLEXIsoCycles_comp_iCycles`. Also removed the
duplicate `HomologicalComplex₂.truncLEXIsoCycles_naturality`. Added proof-only
`import all` of `VerticalCutoffComparisonEpi`, `LowerTruncationTransitionKernel`,
and `UpperTruncationStepSES` to reuse their existing private lemmas. Calls to
the lower projection and cycles naturality lemmas now use the `CochainComplex`
namespace. No other module is adapted. The previous second reading preceded
this repair and has been removed for the new independent reader.

## Proved and sorry left

Closed hole: `HomologicalComplex₂.verticalCutoff_comparison_kernel_twoTerm`
(node `lem-sp-vertical-cutoff-comparison-kernel-two-term`).

Added hole: `HomologicalComplex₂.verticalCutoff_endpoint_forks`
(node `lem-sp-vertical-cutoff-endpoint-forks`). This is the only remaining `sorry`
in the delivery, as the complete proof of a named public theorem in its own module.
The delivery is a decomposition: one upper hole closed and one strictly smaller
boundary-fork hole added, with net zero holes. In particular it does not claim
that the target is proved without `sorry` in its dependency closure.

Both files compile together with no warnings using `lcompile.py --all`.
The endpoint theorem was checked mathematically for a=1, b=a+1, zero differential,
and the zero complex: its kernel is cycles and its cokernel is opcycles when
b>a+1, or cycles modulo boundaries when b=a+1. Both endpoints survive restriction
because a>0. The abstract endpoint proof includes the zero-image case.

## No longer needed

No original imports, modules, or DAG nodes are pruned. The existing definitions
of the vertical cutoff and window remain necessary.

The four duplicate private helpers listed above are removed from this module.
Their existing library declarations are reused; the three source modules are
now necessary proof imports, and none is claimed pruned. No new separate nodes
for zero support, endpoint kernel coordinates, or invertibility of the
coimage-to-image map are needed: those parts have been proved in Lean.

## Where the brief, the DAG or earlier work was wrong

The assigned plan's two dependencies define the window and tower maps; they do not
state the boundary kernel/cokernel identifications needed to finish this argument.
That is the exact gap isolated by the new theorem. The returned delivery was
wrong to reproduce existing private truncation-coordinate lemmas. Lean module
`import all` permits their reuse without changing their visibility or signatures;
the repair removes all four copies and updates the proof dependencies. No false statement or changed
interface was found. The unit's `realized` lists are empty for this item, and this
reduction keeps the original smart-truncation comparison route.

LeanSearch returned an internal server error and is recorded as unavailable.
Loogle, LeanFinder, and grep found useful canonical truncation and universal-property
APIs, but no exact cutoff-boundary theorem. The ancestor script could not follow
`created.item` because it is a module name; the new node inherits the explicit
blueprint ancestor and chain already recorded on the assigned node.

## New nodes

`lem-sp-vertical-cutoff-endpoint-forks`, in
`dag/nodes/sec-abelian-varieties/lem-sp-vertical-cutoff-endpoint-forks.json`, states
that the boundary component of the smaller cutoff inclusion is a kernel of the
upper-cutoff differential and the canonical comparison component is its cokernel.
Its docstring and DAG proof describe both the opcycles case and the adjacent-boundary
homology case. Source read: Stacks Tag 0118, `homology-section-truncations`, cochain
canonical truncations (3) and (4). No change records or forced adaptations are needed.

## Second reading by U3

1. Compared both delivered modules with the repository versions. The existing target
   declaration and all existing declarations retain byte-for-byte identical signatures;
   the only additions are proof bodies and the separately documented endpoint theorem.
   Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds with no warnings.
   The only remaining `sorry` is the named `verticalCutoff_endpoint_forks` theorem,
   and no definition contains `sorry`, `axiom`, `unsafe`, `opaque`, or related escape hatches.
   Verdict: pass, with the documented split hole.
3. Checked the endpoint theorem statement against the cutoff coordinates and the cases
   a=1, b=a+1, zero differential, and zero complex. It states exactly the two universal
   properties needed by the target and makes no assertion about `kernel q`; no duplicate
   library declaration was found. Verdict: pass.
4. Reviewed the proof route and imports. The target proof uses the endpoint theorem and
   the existing truncation-coordinate lemmas through proof-only `import all`; the unit
   route and all required proof dependencies are retained. No import or DAG node can be
   pruned from this delivery. Verdict: pass.
5. Compared the target and endpoint DAG records with the Lean declarations, including
   proof steps, dependencies, origins, and the split status. They agree; the endpoint
   node is a strict lower-level decomposition with its required source and proof text.
   Verdict: pass.

Changed after this reading: no Lean proof or statement changes; added this independent
review record only.

Final checks: scratch-copy `#print axioms` for both public theorems reports exactly
`propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. Independent
Loogle search for `"truncLEMap", "IsColimit"` returned no matches; grep of the
coimage/image and cycles/opcycles universal-property APIs confirms the existing
building blocks without supplying the missing endpoint transport. Repository grep
confirmed all three reused private coordinate lemmas in their reported modules.
Read the cochain formulas (3) and (4) of [Stacks Tag 0118](https://stacks.math.columbia.edu/tag/0118)
and checked the adjacent-boundary case as the kernel-of-induced-quotient calculation.
No short complete replacement for the split theorem was found.
