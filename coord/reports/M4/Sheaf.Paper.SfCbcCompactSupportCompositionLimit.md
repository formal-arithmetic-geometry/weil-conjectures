## What changed

Proved the recursive word induction and normalization formulas in
`Sheaf.Paper.SfCbcCompactSupportCompositionLimit` without changing any existing signature,
definition, public import, or docstring. The proof uses completeness of each letter's
output, invertibility of its strict comparison, and the prescribed eta-then-Rlim(q)
construction. All three delivered Lean modules compile cleanly through lcompile.py.
Concatenation and both parenthesization equations are proved on actual
derived strict towers, using naturality rather than faithfulness of evaluations.

Added `Sheaf.Paper.SmallSiteReducedCompletionUnit`, proving that strict quotient reduction
inverts the specified completion unit over every Noetherian coefficient ring and ideal.
The proof generalizes the finite-restriction argument of `CompletionFiniteReduction` by
dropping the unused torsion/perfectness datum; no existing module is edited for this.

Added `Sheaf.Paper.SmallSiteDirectImageReconstruction` for the remaining small-site
one-letter projection/normalization step. This is the strictly smaller geometric step
needed to apply the already stated direct-image result to the parent's small-site,
ULift-coefficient presentation. It handles one geometric morphism, with no words,
concatenation, open extension, pullback letters, or parenthesization assertions.

## Proved and sorry left

Closed the body of `AlgebraicGeometry.Scheme.sfCbcCompactSupportCompositionLimit`
(node `lem-sf-cbc-compact-support-composition-limit`) by constructing the reduced-unit
witness and proving all word and expression assertions by induction. This is a
decomposition: one strictly smaller direct-image reconstruction step remains below
the target.

Proved `CategoryTheory.AdicSites.reductionCompletionUnit_isIso`
(node `lem-sf-cbc-small-site-reduced-unit`), plus private glue for the counit-tensor mate,
concatenation, and parenthesization. No sorry remains in the assigned module or the
reduced-unit module.

Added one hole: `CategoryTheory.AdicSites.smallSiteDirectImageReconstruction`
(node `lem-sf-cbc-small-site-direct-image-reconstruction`), whose entire proof is `by sorry`.
The docstring and node give the finite perfect projection, constant-tower normalization,
and augmentation-transport argument. There are no data holes. Original holes closed: 1; new holes: 1; net closure: 0.

## No longer needed

The generic word-coherence node `lem-sf-cbc-word-reconstruction-coherence` and its module
`Sheaf.CategoryTheory.WordReconstructionCoherence` are not needed by this proof: the
required recursive inductions are written directly for the existing word and expression
types, avoiding translation to a second path/expression representation.

The homogeneous-composition nodes
`lem-weil-pbc-proetale-derived-pullback-composition` and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` are not needed: the parent's
actual conclusion concerns words and reassociation, with no equation collapsing two
successive geometric maps into their composite. The recursive words are retained.

The direct statement of `lem-sf-cbc-completed-pullback-unit-tower` is not needed because
the new reduced-unit theorem applies directly over the lifted Noetherian ring, without
transporting an entire CompleteCoefficientDatum. The corresponding finite-reduction
argument remains in the proof dependency of the new reduced-unit node.

Removed proof imports:

- `Sheaf.Paper.CompletedPullbackAdjunction`
- `Sheaf.Paper.PbcActualStrictPullback`
- `Sheaf.Paper.CompletedPullbackReduction`
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.CompletedPullbackUnitTower`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.ConstantTowerDirectImageNormalization`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.ProEtaleConstantReductionTower`

The model-site finite-limit constructions retain an explicit proof import of
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. The public imports are unchanged.

Removed the obsolete approval entries for
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and
`lemma-weil-pbc-completed-pullback-reduction` from the parent's `tool_uses` list;
these are not needed directly by the written recursive proof.

No module is withdrawn. The direct-image reduction-unit, constant-tower normalization,
and projection/limit-comparison nodes remain dependencies of the split geometric step.
Their work is not claimed to be pruned from the library.

## Where the brief, the DAG or earlier work was wrong

The planned generator lemmas do not specialize by definitional equality to all the
parent's constructions. `completedPullbackUnitTower` requires a CompleteCoefficientDatum
in the lifted coefficient universe; the parent's datum is in the original universe.
`directImageReductionUnit` uses original-site coefficient and derived presentation data,
whereas the parent uses `AdicSites` on equivalent small sites and an adjunction-selected
module direct image. The split step records the precise geometric comparison still
needed, and the reduced-unit proof avoids unnecessary lifted perfectness data.

The current blueprint has moved this unit to `sec-six-functors-basics/sk-prop-sf-cbc`.
Its current Step 5 is a shorter compactification-independence paragraph. The detailed
strict-diagram prerequisite remains the assigned node's explicit refinement; the proof
here follows that refinement and the cited Stacks statements, with no unit-route change.

## New nodes

`lem-sf-cbc-small-site-reduced-unit`: proved Noetherian small-site reduced-unit theorem.
Its proof uses nilpotence on quotient coefficients, the normalized reflector's hom-set
bijection, finite scalar adjunction, and levelwise homology detection.

`lem-sf-cbc-small-site-direct-image-reconstruction`: the remaining one-letter geometric
projection and canonical unit-normalization statement, isolated from all word coherence.
It is strictly part of the parent's argument and is also valid at the zero/unit ideals
and on empty sites.

Change record: `coord/changes/M4-small-site-reconstruction-lemmas.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
