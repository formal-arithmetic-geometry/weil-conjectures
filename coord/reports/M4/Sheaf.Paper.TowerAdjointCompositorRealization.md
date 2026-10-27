## What changed

Implemented `AlgebraicGeometry.ProEtale.TowerAdjointCompositor.towerAdjointCompositorRealization`
with its original signature. The supplied calculus already contains the actual tower
compositor, finite coherence, and direct-image reductions. The proof restricts this
compositor to the full ctf categories, constructs the counit-normalized right comparison
with `rightAdjointUniq`, proves uniqueness by the composite Hom equivalence, and computes
its finite evaluation by successively evaluating the two adjunction transposes.

Private proved helpers package the given unit/counit evaluations, identify normalized
left evaluations, and deduce normalization preservation from the actual reductions.
The two reduction squares follow directly from naturality for actual tower morphisms.
The supplied `FiniteIdentities` hypothesis is retained in the unchanged signature.
No definition, existing statement, source-library declaration, or public import changes.

The only remaining geometric compatibility step is stated in the new module
`Sheaf.Paper.TowerCompositorFiniteEvaluation`: the given left compositor's finite
normalization. It asserts only one finite evaluation identity, with no right comparison,
existence, counit uniqueness, normalization preservation, or reduction conclusions.
Updated the parent DAG proof to the implemented argument and removed unused proof imports.

## Proved and sorry left

Closed 1 of the original 1 holes:
`AlgebraicGeometry.ProEtale.TowerAdjointCompositor.towerAdjointCompositorRealization`
(node `lem-sp-tower-adjoint-compositor-realization`). The assigned module has zero direct
holes. Its construction and every field of `Laws` have complete proofs from the split lemma
and the supplied calculus and adjunction data.

Added 1 hole:
`AlgebraicGeometry.ProEtale.towerCompositorFiniteEvaluation`
in `Sheaf.Paper.TowerCompositorFiniteEvaluation`
(node `lem-sp-tower-compositor-finite-evaluation`). This is a decomposition: 1 upper hole
closed, 1 strictly smaller finite-normalization hole added, net 0 direct holes.
The new theorem's docstring and node give its complete natural-language proof.
No additional holes or data constructions from an unproved existence theorem are introduced.

## No longer needed

Removed these private proof imports from the assigned module:

- `Sheaf.Paper.CompactSupportUniformTorBound`
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.UnboundedProperOpenInterchange`
- `Sheaf.Paper.ProperOpenCoefficientMate`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence`
- `Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`
- `Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization`
- `Sheaf.SixFunctors.OpenTensorNormalization`

The parent proof no longer directly uses these planned dependencies:

- `lem-sbc-smooth-relative-dimension-permanence`
- `det-sp-tower-bound-uniform`
- `det-sp-coefficient-towers-abelian`
- `lem-sf-semilinear-proper-open-mate-pasting`
- `lem-weil-pbc-finite-ring-constructible-derived-origin`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-sp-finite-compact-site-coherence`
- `lem-amb-unbounded-proper-open-interchange`
- `lem-sp-proper-open-coefficient-mate`
- `lem-amb-unbounded-compact-support-comparisons`
- `lem-cbc-compactifiable-compatible-tower`
- `lem-cbc-compactifiable-cofiltered`
- `lem-sf-semilinear-compositor-coherence`
- `lem-sp-compactification-refinement-coherence`
- `det-sp-tower-shriek-levels`
- `def-weil-pbc-adjunction-conjugate`
- `lem-sp-finite-adjoint-compositor-transposes`
- `lem-sp-strict-compactification-comparison-realization`
- `lem-sf-open-tensor-normalization`
- `det-sp-reduction-direct-image`
- `det-sp-reduction-exceptional`
- `det-sp-scalar-extension-functor`

The new finite-evaluation node retains the finite site-coherence and compact-support
comparison arguments needed for its own proof. Uniform preservation, actual composition,
and direct-image reduction are already supplied by the `Pair` and `cal` hypotheses.
No module is withdrawn and no source-library declaration is pruned. Global reachability
may retain modules through other users or existing public imports.

Pruned obsolete parent `tool_uses` entries except
`lem-coef-semilinear-derived-sections`; these entries correspond to the unused direct
construction, geometric-bound, proper/open-paste, and refinement steps listed above.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original proof plan reconstructs operations and bounds
that the actual Lean statement already supplies as explicit inputs. The shorter proof
uses those inputs without changing the unit route. Reduction squares for actual maps
are already naturality equations in `cal.reduction`, so the finite b/c composition
identities are unnecessary for those fields of this Lean theorem.

The finite-normalization split keeps every positive level, including n=0 for exponent 1,
empty schemes, d=e=0, arbitrary fields of characteristic p, and ramified E. It imposes no
flatness on quotient maps and does not assert faithfulness of derived tower evaluation.
Normalization preservation includes all m<=n, including equal indices, and follows by
isomorphism cancellation in the recorded scalar coordinates.

## New nodes

`lem-sp-tower-compositor-finite-evaluation` in
`dag/nodes/sec-smooth-purity/lem-sp-tower-compositor-finite-evaluation.json`, attached to
`AlgebraicGeometry.ProEtale.towerCompositorFiniteEvaluation` in the new module
`Sheaf.Paper.TowerCompositorFiniteEvaluation`. It isolates the finite-evaluation part of
parent steps 2--3 and blueprint composition-comparisons proof (3). Its argument uses
`cal.coherence.composition_finite`, uniqueness of normalized Evaluation comparisons,
finite etale-origin witnesses, and the finite compact-site normalization. The parent
combines this identity with independently proved categorical and reduction arguments.
No change record is required because existing public signatures and definitions are unchanged.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
