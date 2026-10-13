## What changed

Proved `AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_coordinate_squares`
from the existing affine chart transition construction and coherence theorem. Added the
proof-only import `Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartCoherence`.
The public statement, its universes, and both public imports are unchanged.

The private proved helper `chart_scalar` recovers structural A-linearity of the additive
chart coordinates using the diagonal localization square and its scalar formula. The prime
coordinate is A-linear by C-linearity and `ΓSpecIso_inv_naturality_assoc`. The proof builds
the formal gluing data with the existing coherence equations and supplies all four numerator
equations from the same transition object. Updated the node's proof, proof dependencies,
and proof origin to record this route.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_coordinate_squares`
(node `lem-sbc-punctured-completion-affine-coordinate-squares`), the only original hole.
No holes remain in the item's module. No holes were added and none were split off.
The existing imported `exists_affine_chart_transitions` and
`affine_chart_transition_generator_coherence` still contain their pre-existing holes;
this delivery uses their statements as intended by stage 3. The theorem is proved relative
to those existing dependencies, not claimed to be free of all transitive sorry axioms.

## No longer needed

No imports removed and no module is claimed globally pruned. The node no longer uses
`lem-weil-pbc-fibre-product-affine-spectra` directly: the affine coordinate construction is
supplied by `lem-sbc-punctured-completion-affine-chart-transitions`. Tensor/localization
construction remains work below that existing node. `PuncturedCompletionAffineChartRealization`
is not imported; using its transitions and coherence separately retains the extra scalar
formulas needed for A-linearity. All other original direct dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The earlier node's search correctly observed that the additive-coordinate realization
statement alone does not supply A-linearity. The newer `AffineChartTransitions` interface
also records `b_scalar`, which, together with `b_right` on the diagonal, suffices to prove
A-linearity without a new geometric lemma. No statement or definition needed correction.
The unit `sk-prop-input-spreading` has empty realized-node lists, and this reuse stays
within its completion-gluing argument.

The newly landed transitions/coherence modules initially had not reached the green-build
snapshot. Independent scalar and affineness calculations compiled through `lcompile.py`
while waiting. After publication, the complete item compiled cleanly in 5.1 seconds with
the unchanged statement and no remaining holes. The only full-file repair was to use
`change` instead of `dsimp [V]` before the composite-preimage rewrite, avoiding premature
unfolding of that preimage.

Tool observation: a read-only `tools/batch_land.py status` invocation was refused by the
lead-only shell guard imported from `merge_delivery.py`. This was a status query while
waiting for publication. Subsequent checks use `tools/build.py status` and the local
compiled-file availability only.

## Second reading by C1

1. **Statements unchanged.** Compared the delivered theorem against the repository version; its
signature, binders, lets, hypotheses, conclusion, and visibility are byte-for-byte unchanged.
The only declaration change is the proof body, plus the proof-only coherence import.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it succeeds with no
errors and no `sorry` in the item. The proof uses the existing transition and coherence theorem
statements and introduces no axioms, unsafe declarations, hollow definitions, or arbitrary data
choices.

3. **Split statements and node agreement.** No statements were split off and no new Lean modules
were added. The updated node records the exact theorem statement, the transition/coherence route,
its proof dependencies, and the proof origin. The theorem is a direct construction from those
existing declarations, not a restatement under another name.

4. **Pruning and imports.** The added coherence module is used by the proof as a proof-only import;
the two public imports remain necessary for the theorem's interface. The proof follows the unit's
completion-gluing route and does not bypass a unit step. The report's no-longer-needed analysis and
the node's dependencies agree with the actual proof.

5. **Truth and edge cases.** The scalar upgrade follows from diagonal restriction injectivity,
`b_scalar`, and functoriality; the completed coordinate is upgraded by `GammaSpecIso` naturality.
The four numerator identities are inherited directly from the transition object. The construction
also handles empty and zero-generator families, including `t = 0`, as stated.

Changed in this second reading: added this review section only; no Lean declarations or node
statements were altered.
