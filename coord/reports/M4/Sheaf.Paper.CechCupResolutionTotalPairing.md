## What changed

Restored `Sheaf.Paper.CechCupResolutionTotalPairing` and its beta-axis helper from
repair note `ebf9d37306c806a6`, preserving both recorded signatures and visibility.
The total pairing is the characterized sheaf cup product transported through the
three comparison isomorphisms. Its alpha square follows from `alpha_class` and
the resolution characterization; its beta square follows from the separate
beta-axis theorem and cancellation of the target isomorphism.

The two modules compile together against the current published build, without
warnings. No dependency modules or instances were changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing`
(node `lem-sc-cech-cup-resolution-total-pairing`), reduced to the beta-axis
obligation by an actual bilinear-map construction and a complete alpha proof.

Left/split off: `AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing`
(node `lem-sc-cech-cup-resolution-beta-class-pairing`) is the sole delivered sorry.
It asserts only compatibility on augmentation classes, with a fixed characterized
cup; it does not assert existence of a total pairing or its alpha formula.
This is a decomposition, not a proof without sorry dependencies. The assigned
module and both nodes were absent from the checkout after the returned landing,
so the counts refer to the recovered obligation, rather than claiming a new
baseline hole was closed.

## No longer needed

None. The comparison-data and Cech-product public imports supply the signatures.
The beta-class pairing proof import supplies the remaining axis formula.
No unit statement or step is bypassed, and no imported dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned file and its node were absent from the checkout. The repair note
contains the returned delivery, which was used as the exact signature reference.
Both recorded failures were import/probe failures caused by the same duplicate
symmetric-category instance in `ModuleCupKInjectiveTarget` and
`GlobalTensorPullbackMonoidalNormalization`. Neither failure reproduces when
compiling the restored modules against the current published build. The dry-run
probe is checked separately before reporting READY. No arbitrary witness is
selected for a definition: the pairing is constructed in an existence proof,
and the characterized cup is unique. Empty index families, zero inputs and
degree zero require no extra hypotheses; the beta obligation uses only the
comparison data, and the alpha proof is uniform in both natural degrees.

## New nodes

`lem-sc-cech-cup-resolution-total-pairing` restores the returned node with its
actual transport proof and dependencies. It introduces no new sorry.

`lem-sc-cech-cup-resolution-beta-class-pairing` restores the strictly smaller
augmentation-axis obligation, including the signed Alexander--Whitney argument
in its docstring and node. Searches found no existing exact Mathlib result.

Change record: `coord/changes/CechCupResolutionTotalPairing-new-module.md`.

## Second reading by M4

1. **Interfaces — pass.** Both Lean files are absent from the repository baseline,
   so an ordinary baseline diff is an addition. Extracted the two complete files
   from `coord/repair-notes/Sheaf.Paper.CechCupResolutionTotalPairing.json`
   (repair `ebf9d37306c806a6`) and ran `diff -u`: both sandbox files are byte for
   byte identical to the recovered delivery, including signatures, visibility,
   definitions, imports and docstrings. No target or dependency definition changes.
2. **Proof and axioms — pass as a decomposition.** Compiled both modules in import
   order with lcompile.py (3.7 s and 9.9 s, no warnings). A scratch module imports
   both and runs `#print axioms` on both declarations: exactly `propext`,
   `Classical.choice`, `Quot.sound`, `sorryAx`. The total theorem contains a real
   bilinear-map construction, an alpha proof using hcup and alpha_class, and a
   beta proof by the stated remaining theorem and inverse cancellation. The only
   delivered sorry is the whole proof of the public named beta theorem. There
   are no delivered definitions or prohibited declarations. Choice of cup occurs
   inside an existence proof and its characterization is unique.
3. **Split obligation — pass.** The beta theorem fixes a characterized cup and
   asserts only its augmentation formula. The existence construction and alpha
   formula have already been discharged in the total theorem; this is strictly
   a remaining part, not an application of a renamed total theorem. Read the
   signed Alexander--Whitney argument and checked it against Stacks Tags
   [07MB](https://stacks.math.columbia.edu/tag/07MB) and
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV).
   The source's covering assumption is replaced here by explicitly supplied
   alpha quasi-isomorphisms; the sectionwise pairing needs no cover assumption.
   In bidegrees (r,i),(s,j), the sign is (-1)^(i*s); it is one on both axes.
   Empty index sets give zero Cech terms (tuples have positive length), and
   supplied comparisons then force the relevant resolution homology to vanish.
   Zero inputs give zero by bilinearity; p=q=0 uses augmentation_pair, with no
   boundary sign. The kernel cycle c is uniquely determined by hc.
   Independent leanfinder, loogle and grep searches with different terms found
   no exact Mathlib statement. Read the local CupCechTotalCochainPairing and
   CupCechTotalCochainAxes results: they give a cochain pairing and its axes,
   not the asserted equality for the characterized cup. Its cochain-map
   existence dependency is itself still sorry. Formal quotient descent and
   identification via the alpha quasi-isomorphisms remain necessary; this is
   not a hole closable by a short application. CechCupPullbackCompat and
   cechCup_resolution_representatives require cover and quasicoherence
   assumptions absent here, and do not replace this obligation.
4. **Route and pruning — pass.** The total theorem takes the direct characterized
   cup transport route and uses each import. ComparisonData and CechCupProduct
   occur in the signature; BetaClassPairing is correctly a plain proof import.
   Relative to the recovered proof_deps no node or import was removed, so
   `No longer needed: None` is complete. The unit sk-prop-av-cube is unchanged;
   its realized statement and step lists are empty in the baseline, and this
   delivery introduces no bypass of any recorded unit step.
5. **DAG — pass.** Both node Lean signatures match the declarations (whitespace
   normalized); total proof_deps are exactly the union of its three steps'
   uses. The beta node records the signed cochain calculation, alpha comparison
   and augmentation calculation, with their dependency union, source, searches,
   creation metadata, blueprint provenance, chapter, unit and complete Lean
   record. The total proof_origin describes the transport actually written.

Changed only review documentation: corrected the repair identifier above and
replaced the change record's hypothetical downstream-user row by the actual
baseline importer search and the delivered beta-to-total dependency. No Lean
proof, signature, definition or node was changed. One recovered upper obligation
is reduced to one lower obligation: one hole closed, one split off, no net
sorry reduction claimed and no module pruned. The second-reader dry run passed local compilation, per-declaration axiom
probes and stage-3 preflight: `OK (dry run)`, commit `0bf2c5b55e`.
The tool classifies the restoration CODEX because it adds modules/nodes,
leaves the one beta sorry and repairs a returned delivery.
