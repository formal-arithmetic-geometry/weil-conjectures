## What changed

Replaced the sorry in AlgebraicGeometry.affine_open_localized_tensor_exact by a complete
Lean reduction. The geometric transport of sheaf Tor bounds is isolated in the new
PrincipalLocalizationSheafTorBounds module. The original statement, universes, binders,
and public imports stay identical. No other existing module or interface is changed.

The main proof widens the interval to [a,max(a,b)], applies affine_torAmplitude_iff,
proves localized boundedness and flatness with Mathlib, proves categorical K-flatness
using the existing bounded-flat acyclicity theorem and braiding, and transports IsGE
through QObjTensorSingleFunctorObjIso and isGE_Q_obj_iff to ordinary tensor exactness.
The compactness assumption is recorded but not needed for this reduction.

## Proved and sorry left

Closed: AlgebraicGeometry.affine_open_localized_tensor_exact
(node lem-sc-affine-open-localized-tensor-exact), one original hole.

Added: AlgebraicGeometry.principal_localization_sheaf_tor_bounds
(node lem-sc-principal-localization-sheaf-tor-bounds), one public theorem with exactly
`:= by sorry`. No sorry remains in the original module; no definitions are added.
This is a decomposition, not a net hole reduction: one hole closed, one added.
The remaining statement concerns only the geometric transport of sheaf bounds,
with no boundedness/free hypotheses and no ordinary tensor exactness conclusion.
All affine-criterion, localized-flatness, K-flatness, and derived-to-ordinary steps
are actually combined in Lean in the original module.

Both modules compile locally without warnings. deliver3.py --no-push printed OK:
the delivery passes compilation and preflight except for the second reading, which
the second reader writes. Nothing was pushed. The axiom probes passed.

## No longer needed

Removed the direct proof import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
from the original module. The new geometric lemma still imports it and its node uses
lem-pc-affine-derived-pullback-tensor-tilde, so this does not prune that module from the
closure. No existing node or module is claimed globally unnecessary. No pruning.
The free terms need not be finite, and U need not be compact, for this proof, but
both assumptions of the existing theorem have been preserved.

## Where the brief, the DAG or earlier work was wrong

The planned affine comparison theorem provides the general pullback and tensor
isomorphisms, not a public packaged theorem transporting sheaf Tor bounds to the
concrete localizedModuleFunctor complex on Spec(A_f). This geometric glue remains
in the new node. The proved TorAmplitudeOpenLocal module has related private helpers,
but its public theorem goes in the converse direction (local bounds imply global
bounds), and AffineLocalSheafificationTorAmplitude only supplies an existential
interval in another restriction encoding, so neither gives the required fixed bounds.

The bounded-flat node supplies one-sided acyclicity, not categorical kFlat directly.
The delivered Lean proof handles the homotopy quotient and both sides using braiding.
The original node's unit has empty realized statement/step lists; no unit route is
bypassed. Sources read: Stacks Tags 09U8, 08DW(2), and 08EG, together with the node's
original argument. No mathematical statement dispute or forced adaptation.

## New nodes

lem-sc-principal-localization-sheaf-tor-bounds states only restriction/localization
transport of sheaf Tor bounds. Its source and complete proof are in its docstring
and its node. Small cases checked: f=0, a unit f, empty U, zero ring, and a>b;
localization to the zero ring gives only zero modules, and exact restriction retains
the entire interval, including an empty one. No boundedness or quasi-compactness
hypothesis is used. The direct image is only used as an input to the given bound;
its exactness is not assumed. Searches were run with leanfinder, grep, and leansearch
(the last service returned Internal Server Error); the whole blueprint search for
"localization tor amplitude" returned no matches. No change record is needed.

## Second reading by A3

1. **Interface and accidental changes.** Compared `AffineOpenLocalizedTensorExact.lean` with the repository copy. The theorem signature is byte-for-byte unchanged; the only interface change is the intended proof-only import replacement plus the new split theorem module. The new node records match the declarations and no definitions were changed. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled both delivered modules with `lcompile.py --all` and the target module independently; both complete without errors or warnings. The original target has no `sorry`; the sole remaining `sorry` is the explicitly named public theorem `principal_localization_sheaf_tor_bounds`. No forbidden declarations or hollow definitions were introduced. Verdict: pass.

3. **Split statement review.** The split theorem isolates a strictly smaller, lower-level component of the argument: it transports the stated sheaf vanishing interval to a principal localization and has no boundedness, freeness, compactness, or tensor-exactness conclusion. Its hypotheses and conclusion match the node and its docstring gives the direct-image, restriction, and affine-localization argument, including edge cases. Searches recorded in the node found no existing declaration with this statement. Verdict: pass, decomposition accepted.

4. **Pruning and route.** The proof uses the affine Tor-amplitude criterion, bounded-flat K-flat result, source tensor-model isomorphism, and the new geometric transport theorem. The former direct proof import was removed and is retained only by the new theorem. No old proof dependency is unused beyond that documented import adjustment; no unit route is bypassed. Verdict: pass.

5. **DAG and delivery checks.** The target and split node `proof`, `proof_deps`, `proof_origin`, Lean records, and report agree with the code. The unit record is unchanged. The delivery dry-run printed OK (commit eb9216e39e), including compilation, the axiom probes, and preflight; no statement or definition change record is needed. Verdict: pass.

Changed in this second reading: appended this review and clarified dependency pruning below; no Lean proof or statement required repair. Independent searches with `msearch.py` used “Pullback along an open immersion preserves the vanishing interval of derived tensor with all module sheaves” (leanfinder) and `restrictFunctor.*[Tt]ensor|localiz.*[Tt]or|[Tt]or.*localiz` (grep). They returned ordinary restriction/pullback comparisons and exact module localization, not the split statement. Read the public affine comparison declarations, the existential finite-Tor-amplitude theorem, and the private open-local model helpers; none closes the concrete fixed-interval localization comparison in a few minutes.

The old direct proof dependency `lem-pc-affine-derived-pullback-tensor-tilde` is replaced in the target node by `lem-sc-principal-localization-sheaf-tor-bounds`; it remains a transitive proof dependency through that new node and hence no module is globally pruned. All other old proof dependencies remain used. The unit’s `realized.statement` and its sole `realized.steps` list are empty.
