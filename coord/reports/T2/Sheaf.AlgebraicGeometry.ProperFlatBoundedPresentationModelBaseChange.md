## What changed

Repaired `proper_flat_boundedPresentation_model_baseChange` in
`Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModelBaseChange`. The former
false arbitrary-complex interface is replaced by transport from a nonnegative model
D along a supplied quasi-isomorphism C -> D. The proof derives K-flatness of both
complexes, proves preservation under ordinary pullback by transporting tensor
pullback, and transfers negative vanishing and higher-direct-image comparisons.
The existing private negative-homology diagnostic is retained unchanged.

Forced adaptation: `Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel`
keeps every existing signature and visibility. Its proof now constructs a genuine
Cech model D, obtains a bounded finitely presented replacement C with a
quasi-isomorphism to D, and applies the repaired transport theorem. Its only other
edits are the proof imports needed for those constructions. All four delivered
modules compile locally, with no warnings.

The comparison node records the interface correction. The caller node records the
new route. Change record: `coord/changes/proper-flat-bounded-model-identification.md`.
The coherence unit's finite-affine-Cech, perfect-replacement and Noetherian-
approximation route is preserved; no blueprint unit statement or step is changed.

## Proved and sorry left

Closed the sole hole of the item's module, under a necessary correction of its false
intermediate signature:
`AlgebraicGeometry.Scheme.Modules.proper_flat_boundedPresentation_model_baseChange`
(node `lem-pc-proper-flat-bounded-presentation-comparison-core`). This is a repair and
reduction, not a proof of the original false statement. Its new proof body contains
no sorry. The caller `exists_proper_flat_boundedPresentation_model` remains proved
with its original signature.

Added two holes, both whole named public theorem bodies `:= by sorry`:

- `AlgebraicGeometry.Scheme.Modules.exists_proper_flat_affine_cech_perfect_model`,
  node `lem-pc-proper-flat-affine-cech-perfect-model`, module
  `Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel`.
- `AlgebraicGeometry.Scheme.Modules.exists_affine_perfect_flat_model_replacement`,
  node `lem-pc-affine-perfect-flat-model-replacement`, module
  `Sheaf.AlgebraicGeometry.AffinePerfectFlatModelReplacement`.

The first supplies a bounded nonnegative flat model computing cohomology but makes
no termwise finite-presentation claim. The second is a general affine algebraic
replacement of a given perfect quasi-coherent complex and makes no direct-image
or base-change-cohomology claim. The proved combination uses the comparison map
between them. Neither is a renaming of the item. No definition is introduced or
changed, and no witness from an unproved existence theorem is chosen in a definition.

Count: one existing hole repaired/closed, two added; net -1 by this local count.
This is a decomposition repairing a false dependency, not claimed as net progress.
Existing imported K-flat dependencies may still depend on sorries; they are the
intended next items. Their holes are not added or changed by this delivery.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModelCore`
from the caller and removed its dependency on
`lem-pc-proper-flat-bounded-presentation-structural-core`. That structural-only
statement cannot tie C to F and is not used anywhere in the repaired argument.
No claim is made that it is globally unreachable from every other target branch.

Removed the item's direct public imports
`Mathlib.AlgebraicGeometry.Morphisms.Proper` and
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: the repaired transport
statement does not use these geometric hypotheses. The unchanged existence caller
retains these imports. Retained `Mathlib.Algebra.Homology.SingleHomology` because the
existing private diagnostic uses it. Added only the QuasiIso statement import and
the three proof imports for identity-relative flatness, bounded-above K-flatness
and tensor-pullback preservation. No other former proof node was used by the old
comparison node (its proof_deps was empty).

## Where the brief, the DAG or earlier work was wrong

The former comparison-core statement is false for arbitrary C. A2's existing
STATEMENT-DISPUTED marker and proved negative-homology obstruction were correct.
The caller's earlier reduction combined an unrelated structural witness with that
false universal bridge. Bounds, flatness and finite presentation cannot identify
a complex with Rf_*F. The replacement route supplies a genuine model and an actual
quasi-isomorphism before transporting any cohomology.

The existing `exists_proper_flat_cohomology_model_data` is local around an input
point and cannot supply a model on the specified affine open U, especially when
U is empty. It also does not record perfectness of that same model. The new fixed-
affine Cech statement supplies exactly these missing facts. The existing affine
perfect theorem supplies a derived representative on Spec A but not a chain map
to the given D on a general affine Y; the replacement statement isolates this glue.
LeanSearch returned Internal Server Error for both new-statement searches, recorded
as unavailable; real LeanFinder and Mathlib-source searches found no exact theorem.

A source-only DAG walk also encounters a pre-existing proof cycle between
`lem-pc-coherent-hi`, `lem-pc-e2-integral-ideal-proper-cohomology` and
`lem-pc-euler-additive`, downstream in the existing perfect-direct-image plan.
This delivery does not create that cycle or alter those unheld nodes. The delivered
Lean imports compile in order and introduce no import cycle. Generic affine derived
and perfect lemmas used in the new nodes' plans are tool dependencies, not a change
to the coherence unit's route.

## New nodes

`lem-pc-proper-flat-affine-cech-perfect-model` supplies the actual nonnegative flat
Cech model on the chosen affine open, the universal cohomology comparison, and
perfectness of this same derived object, without termwise finite presentation.
Its source is Stacks 01XB, 0A1D, 0B91(2), and the proof of 0A1H. Empty inverse
image uses the zero complex; arbitrary nonaffine new bases use compatible local
Cech augmentations, and arbitrary cartesian squares use their unique isomorphism.

`lem-pc-affine-perfect-flat-model-replacement` isolates a general affine perfect
replacement with a genuine chain map to the original quasi-coherent complex.
Its source is Stacks 08EB, 0656 and 0647 with the affine counit of 01IB. Empty
schemes, zero coefficients and negative lower bounds are allowed. A derived
isomorphism is represented by a chain map on the ring side using K-projectivity;
finite projective associated sheaves have all three structural properties.
The chosen derived localizations carry no extra geometric hypotheses.

Both nodes have complete source proofs in their Lean docstrings, exact Lean
signatures, recorded actual Mathlib searches and blueprint ancestry. The general
affine replacement has no higher-direct-image conclusion. Change record:
`coord/changes/proper-flat-bounded-model-identification.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel` is unclaimed in the
local claim snapshot. The original file compiled against the baseline but fails
against the repaired comparison interface at its old application (line 67):

```text
error: Application type mismatch: The argument hF has type F.IsFlatOver f
but is expected to have type T.Opens in the application
proper_flat_boundedPresentation_model_baseChange f F hF
```

The forced edits replace the structural-only proof import and the proof beginning
at line 64 with the actual model construction and replacement comparison; all
existing declaration signatures and visibility remain identical. Constructing
only C without e would leave the corrected hypothesis unprovable, so these edits
are necessary. The adapted module compiles against the changed item and its two
new helper modules. deliver3.py independently repeats both counterfactual
compiles before its dry run.

## Second reading by T2

1. **Visible changes.** I diffed the delivered modules against the repository versions.
The existing caller declaration is byte-for-byte unchanged in signature and visibility.
The comparison declaration is intentionally changed under the recorded change record;
the two helper declarations are new split-off statements. No unrelated declarations or
definitions changed.

2. **Proof checks.** I compiled all four delivered modules with `lcompile.py --all`.
The only remaining `sorry`s are the two named helper theorems listed above; there are no
axioms, unsafe declarations, opaque declarations, or sorry-valued definitions. The
comparison proof uses the existing K-flat, tensor-pullback, and homology-isomorphism
interfaces. Axiom printing includes only the permitted axioms plus `sorryAx` inherited
from the explicitly open helper dependencies.

3. **Statements.** The repaired comparison statement is true because it transports a
quasi-isomorphism from the supplied nonnegative model, so the former arbitrary-complex
counterexamples no longer apply. The two new statements are strictly lower-level: one
constructs the nonnegative Cech model and its comparison data, and one constructs an
affine perfect replacement with a chain-level quasi-isomorphism. Their edge cases
(empty scheme, zero complex, and negative lower bound) are covered in their docstrings.
Searches over Lean, LeanFinder, Loogle, and Mathlib found no existing declarations with
these statements.

4. **Pruning and route.** The repaired proof follows the unit route through the Cech
model, affine perfect replacement, and transport comparison. The old structural-core
import and its node are no longer used by the caller; direct geometric imports removed
from the comparison module are likewise unnecessary. The unit record remains unchanged.

5. **DAG agreement.** The comparison node records its new proof dependencies and proof
origin, the caller node records the three actual helper dependencies, and both new
nodes contain their exact Lean signatures, source proofs, searches, chapter, and unit.
The change record names the forced adapted caller and the unchanged public boundary.

I changed only the report by adding this second-reading record; no Lean proof or
statement required repair after compilation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel
Original against changed dependencies failed:
```
/tmp/forced-adaptation-i80r85st/lean/Sheaf/AlgebraicGeometry/ProperFlatBoundedPresentationModel.lean:67:8: error: Application type mismatch: The argument
  hF
has type
  F.IsFlatOver f
of sort `Prop` but is expected to have type
  T.Opens
of sort `Type u` in the application
  proper_flat_boundedPresentation_model_baseChange f F hF

(with the modules compiled into /tmp/forced-adaptation-i80r85st/.lbuild) [3.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
