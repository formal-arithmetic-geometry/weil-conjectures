## What changed

Implemented the finite-residue projection argument without changing its statement. The proof chooses one flat-term K-flat representative, applies a strict Koszul augmentation, inverts its pro-zero cone under total right derived inverse limit, and constructs a normalized Roos cone. It checks the ordinary-limit comparison against each projection and transports the resulting cone to the supplied cone. Finite scalar restriction targets are complete by nilpotence. The Koszul reflector mapping bijection and the scalar adjunction then make the reduced reflector unit invertible by coyoneda. Transposing the normalized zeroth projection and cancelling this unit proves the assigned isomorphism.

The strict complex-level augmentation and its quotient-tower normalization are isolated in one new theorem. Unlike the assigned statement, this theorem mentions neither a total derived inverse limit nor the invertibility of a residue projection. The substantial derived-limit, reflection, and adjunction assembly is proved in the assigned module. The existing parent module's private finite-restriction completeness argument is reproduced here because importing that parent would create a cycle. The comparison isomorphism is an explicit composition with a proved projection formula over an abstract ringed site. The nilpotence proof takes its slice derived-category structure directly from the supplied hypothesis. The complex unit is composed as a natural transformation, and its Hom-unit evaluation isomorphism has a component API; this avoids repeatedly checking expanded naturality records.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.adicResidue_quotient_residue_projection_isIso` (one original hole). Added one hole, `AlgebraicGeometry.Scheme.adicResidue_strict_koszul_augmentation`, in `Sheaf.Paper.AdicResidueStrictKoszulAugmentation`, node `lem-sfb-adic-residue-strict-koszul-augmentation`. This is a decomposition, not a net hole reduction: one hole closed, one added. No `sorry` occurs in a definition or private helper.

Validation: both modules compile on the project server within the normal per-file limit. The packet uses the default heartbeat budget and has no profiling options. The delivery tool performs final compilation, signature, and axiom checks.

## No longer needed

No original public import is removed and no module is withdrawn. Removed the unnecessary new-module import `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`; the public derived-category interface already supplies its mapping-cone notation. The assigned theorem no longer directly needs the algebraic Noetherian Koszul augmentation node: its use belongs below the new strict augmentation node. It remains a required dependency of that node and is not globally pruned. The original constant-completion equivalence, K-flat resolution, strict-limit, Koszul reflector, complete-elements ideal, restriction-section completeness, and adjoint-tower dependencies are retained through the implemented proof and new augmentation calculation. No node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original first proof step combines the exterior-algebra Koszul augmentation, its realization as the dual ringed Koszul tower, the actual quotient tensor tower, and the normalized scalar-adjunction identification. The algebraic augmentation theorem does not itself state this ringed strict-tower comparison. The new theorem isolates precisely that missing calculation, before taking a derived limit. The remaining original steps are implemented rather than split off again.

The older `koszulQuotientTensorAugmentation` and `koszulQuotientLimit` use `CompleteCoefficientDatum` and a different constant coefficient model; `completedKoszulQuotientComparison` uses `completedCechTopology` and its completed coefficient presentation. Neither states the strict augmentation for this coefficient-sized slice. The principal strict-resolution bridge assumes monic multiplication and does not apply to a general Noetherian ideal. Transporting those models would require additional comparisons rather than directly close this step.

The proof uses the retained general ringed-site `ringedKoszulCompletionReflector`, as instructed by the node, rather than the narrower attached completed-tensor statement. The unit on an arbitrary representative is justified by descending its actual natural transformation through localization; it is not assumed equal by unfolding an arbitrary representative choice.

## New nodes

`lem-sfb-adic-residue-strict-koszul-augmentation` (`dag/nodes/sec-six-functors-basics/lem-sfb-adic-residue-strict-koszul-augmentation.json`) states the strict augmentation of the negative Koszul tensor tower on a completed coefficient slice. It supplies a pro-zero cone and the normalized isomorphism of its quotient tensor target with the counit-transpose tower. Its source is the strict Koszul/quotient comparison in Stacks Tag 099M and the algebraic pro-isomorphism in `lemma-sequence-Koszul-complexes`. The empty list, unit ideal, zero ring, and unbounded representative are addressed in its proof text. The assigned node's proof and proof dependencies now follow the Lean assembly. No existing statement or definition was changed, so no change record is needed.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
