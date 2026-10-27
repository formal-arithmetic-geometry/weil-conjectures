## What changed

Prove `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_comp`
from the canonical restriction compositor. Derive the proper cocycle from the
ordinary coefficient square and derived horizontal composition. Derive the open
cocycle by normalizing the ordinary pullback square with the open coefficient
collapse, descending through exact localization, and conjugating along the open
and scalar adjunctions. Naturality combines these equations for `pasteScalar`.
All proof helpers are private and proved.

Name the existing scalar adjunction and its proper/open mates, and share these
presentations in the shift, compositor, identity and projection definitions.
Six compiled reflexivity checks identify these with the original constructions.
Cache existing colimit, Grothendieck, resolution and tensor-additivity properties
as proved propositions. Keep large construction data folded and give the private
restriction identity its explicit functor type. Write the original types of the
derived functors and refinement transformations explicitly, with their constructor
bodies unchanged. Cache the existing countable coproduct, integer exact-colimit
and scalar K-flat preservation properties as well. Name the existing Abelian
sheaf and module structures, and the existing module derived-category structure,
as reducible aliases of their original constructors.
Adapt the existing shift and
identity proofs, and remove unnecessary private-name macros. Update the node's
proof route and record the definition preservation checks in
`coord/changes/V9-condensed-scalar-adjunction.md`.

The main module, all three direct consumers, and six temporary preservation
examples compile within the single-file limit. Only the forced consumer repair
below is included; the temporary verification files are removed.

## Proved and sorry left

Closed one of the assigned module's four original holes:
`WeilConjectures.CompactSupportCondensedRealization.condensedProjection_comp`.
Added no holes; split off no statements.

The assigned module has three holes left, unchanged and attached to
`def-pur-condensed-compact-support-projection`:

- `WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_existsUnique`
- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`

The forced consumer retains its five original holes, unchanged:

- `WeilConjectures.CompactSupportRealizationFactorization.compactSupport_realization_factorization`
- `WeilConjectures.CompactSupportRealizationFactorization.identityProperReduction`
- `WeilConjectures.CompactSupportRealizationFactorization.identityProperRealization`
- `WeilConjectures.CompactSupportRealizationFactorization.identityProperCoefficient`
- `WeilConjectures.CompactSupportRealizationFactorization.q_naturality`

Thus the two delivered Lean files contain eight holes in total; the delivery
closes one and adds zero.

## No longer needed

None. Retain the existing imports and dependencies for the proved parts and
remaining refinement statements. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement correction is needed. The cocycle uses exactly the restriction
compositor specified in `condensedScalarComp`. The node now records the exact
square composition theorem used to descend the open equation. The three
remaining assigned holes retain their existing natural-language proof plans.

## Forced adaptations

`Sheaf.Paper.CompactSupportRealizationFactorization` is unclaimed. Its original
`coefficientFactorization` proof failed at line 267 with two unsolved goals after
simplifying `condensedProjection`: the finite and closure composites used the new
names on the left and the original archived comparisons on the right. Append
`<;> rfl` at line 272, after the existing `simp only` list, to close precisely
those two definitional equalities. The adapted module compiles; its signature,
visibility, imports, other proofs and five holes remain unchanged. The other two
direct consumers compile without adaptation.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
