## What changed

Reduced AlgebraicGeometry.exists_kInjective_scheme_evaluation_models without changing
its signature. The proof constructs the ordinary-to-derived Hom maps using the fixed
K-injective augmentation and localization factorization. Hom-exactness makes these
maps isomorphisms. The ordinary dual's K-flatness proves invertibility of the actual
localization tensor map using the upstream right-factor K-flat counit. These supply
the two required isomorphisms. Canonical tensor-Hom naturality, associator naturality,
injectivity of the bijection, and cancellation combine them into the required square.

Added Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization, which contains
one explicitly constructed comparison morphism and one remaining component calculation.
The latter asserts a morphism equation before any ordinary comparisons are inverted.
It assumes neither Hom-exactness, K-flatness of the ordinary dual, nor K-injectivity
of the coefficient. It is strictly the evaluation-calculation part of the argument,
not another existence statement for the requested isomorphisms.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.exists_kInjective_scheme_evaluation_models
(lem-pc-kinjective-scheme-evaluation-models) by decomposition. Its proof is complete
from the named component-calculation theorem. The assigned module compiled in 34.8 seconds against the published library plus the
new sandbox module. The required delivery dry run checks the complete set and axiom probes.
The private comparison invertibility
lemmas ordinaryHomComparison_isIso and tensorModel_isIso_right are proved.

Added one hole: AlgebraicGeometry.schemeOrdinaryEvaluation_localization
(lem-pc-scheme-ordinary-evaluation-localization), in its own new module.
The construction AlgebraicGeometry.schemeOrdinaryHomComparison has no hole and
chooses no witness from a mere existence statement. Net holes closed minus added: zero.
This is a decomposition, not a claim of a sorry-free evaluation theorem.

## No longer needed

Removed these proof imports from the assigned module:

- Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
- Sheaf.AlgebraicGeometry.DerivedTensorSymmetry
- Sheaf.Algebra.Homology.KFlatResolution
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

The first-factor natural comparison lemma (lem-pc-kflat-derived-tensor-comparison)
and separate derived symmetry existence lemma (lem-sc-scheme-derived-tensor-symmetry)
are not used by either delivered argument. All four removals were compiled together successfully.
The main proof uses the upstream canonical
right-factor K-flat counit instead. The functorial resolution is the fixed existing
construction, so the separate existential ringed-site resolution theorem
(prop-pur-kinjective-resolutions-exist) is not used directly. K-flat resolution theory
(lem-pc-kflat-resolution) and Hom projections (lem-sc-hom-complex-projections) remain
needed by the lower component calculation; they have not been pruned mathematically.
The old direct dependency def-pc-scheme-ordinary-evaluation-formula also moves to
the lower component-calculation node; its public import remains necessary for hf.
Thus every removed old proof_deps entry is accounted for above: three are bypassed
(the first-factor comparison, separate symmetry, and existential K-injective
resolution), and three move to the lower calculation (K-flat resolution, Hom
projections, and the ordinary evaluation formula). No claim is made that these
modules are unreachable from all other project targets.

## Where the brief, the DAG or earlier work was wrong

The missing SchemeOrdinaryEvaluationFormula.olean that blocked the retained attempt
is now available; the unchanged original module compiled at the start of this retry.
The retained scratch experiment's unit comparison had the wrong direction for the
needed map: quotientCompQhIso at the degree-zero unit has direction 1 to QO;
the evaluation comparison uses its inverse QO to 1.

The first-factor comparison and separate derived symmetry statements are unnecessary
for the tensor comparison: the upstream right-factor K-flat counit computes the actual
canonical localization tensor map directly. The unit-level Serre-duality route and all
existing statements and visibility are preserved. The new lower statement was checked
on the degree-zero case, zero complexes and the empty scheme; it requires no inverse
of the ordinary evaluation map and no boundedness or finite freeness hypothesis.

The cited Stacks source file is absent from this read-only clone; the official pages
https://stacks.math.columbia.edu/tag/08DJ, https://stacks.math.columbia.edu/tag/08DM
and https://stacks.math.columbia.edu/tag/08DQ were read directly.

LeanSearch returned Internal Server Error; no absence verdict was inferred. LeanFinder,
Loogle and local searches did not provide an existing localized ordinary evaluation
component equation.

## New nodes

lem-pc-scheme-ordinary-evaluation-localization records the remaining ordinary evaluation
component calculation, sourced from the original item's proof step 3 and Stacks Tags
08DJ, 08DM and 08DQ. Its module is
lean/Sheaf/AlgebraicGeometry/SchemeOrdinaryEvaluationLocalization.lean. The node records
both the explicit comparison construction and the theorem; only the theorem has sorry.
The assigned node's proof, proof_deps and proof_origin now follow the actual construction,
right-factor K-flat argument, and canonical naturality calculation. No existing interface
or definition changed, and no forced consumer adaptations or change records are needed.

## Second reading by U4

1. Compared the delivered module with the repository using its complete diff.
   The original public theorem signature, visibility, and docstring are byte-for-byte
   unchanged. There are no changed existing definitions, targets, or other modules.
   Verdict: pass.
2. Compiled both modules together in dependency order: 9.4 seconds for the new
   module and 35.0 seconds for the assigned module, no errors or unexpected warnings.
   The only delivered sorry is the named theorem schemeOrdinaryEvaluation_localization;
   the explicit Hom comparison has no sorry and selects no arbitrary existence witness.
   Checked for forbidden declarations and reviewed every proof step, including the
   right-factor K-flat argument, the direction QO to the unit, and both cancellations.
   Explicit #print axioms checks on a scratch copy report only propext,
   Classical.choice, Quot.sound, and sorryAx for the two theorems; the constructed
   schemeOrdinaryHomComparison uses only the three permitted axioms. The delivery
   tool also probes all delivered declarations. Verdict: pass, conditional on the named hole
   and the still-open upstream statements, rather than a sorry-free proof.
3. Read the lower theorem, its source and full docstring argument. This is the
   evaluation compatibility equation before inversion of the two comparisons; it
   neither supplies their invertibility nor repeats the original existential theorem.
   In degree-zero complexes it is the ordinary evaluation pairing, even for modules
   that are not finite or projective. Zero inputs and the empty scheme give zero
   maps. Resolving the inputs reduces the general equation to the same component
   identity and naturality; no perfection hypothesis is needed for this equation.
   Fresh LeanFinder and Loogle searches with different wording, local upstream and
   Sheaf searches, and reading the neighboring canonical evaluation precomposition
   and postcomposition lemmas found no exact replacement. Those neighbors express
   one-variable evaluation naturality, not this tensor-with-ordinary-dual equation.
   The Stacks pages 08DJ, 08DM, and 08DQ were checked; the lower component calculation
   is a derived consequence of their construction, not a quoted theorem asserting
   all complexes have invertible evaluation. Closing it would require the substantial
   component proof left in its docstring. Verdict: a valid strictly smaller split.
4. Checked all imports: the three public imports of the assigned file occur in its
   signature; the new import is proof-only. The new module's two public imports
   provide its signature and actual comparison construction. Checked the old
   proof_deps against the new ones and completed the accounting above for the
   ordinary evaluation formula. The unit sk-thm-picard-duality and its realized
   fields are unchanged; this reduction is below its Serre-duality route. Verdict: pass.
5. Compared both nodes with the Lean proof: the updated original node records
   explicit Hom comparisons, right-factor K-flat invertibility, and canonical
   naturality plus the lower equation. The new node records the sole remaining
   component calculation, its source, searches, provenance, chapter, unit and
   declaration. Corrected its lean.statement to the verbatim multiline Lean
   signature. Verdict: pass.

Second reading changed only the new node's verbatim signature record and the report's
complete pruning accounting; no Lean proof or interface needed repair. One original
hole is closed by decomposition and one strictly smaller hole is added: net zero.
