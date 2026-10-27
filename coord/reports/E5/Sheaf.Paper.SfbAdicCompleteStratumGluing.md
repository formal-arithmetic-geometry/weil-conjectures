## What changed

The statement of `AlgebraicGeometry.Scheme.sfbAdicComplete_of_stratum_local_iso`
is unchanged. Its proof uses the existing `adicStratumCompletionUnit` preservation
and `adicStratumCompletionUnit_detection` theorems. It explicitly forgets the
constructibility fields of the stratification, transports covering sieves through
AsSmall, chooses finite ideal generators and algebraic inverse-image presentations,
and transports completeness through local isomorphisms.

`Sheaf.Paper.SfbCompletionNormalization` constructs the constant-ring comparison,
the natural isomorphism of finite quotient diagrams, and the completed coefficient
isomorphism. It constructs the normalized derived object by scalar restriction,
proves projection compatibility, identifies the kernel ideals sectionwise, and
proves `SfbCompletionNormalization.complete_iff` using the existing proved scalar
restriction completeness theorem. These constructions introduce no arbitrary
witnesses and no holes in definitions.

The sole remaining comparison is isolated in
`Sheaf.Paper.SfbNormalizedLocalRestrictionIso`. It transports an isomorphism
between two local restrictions to an isomorphism between the normalized
restrictions. Its statement has no completeness, covering, stratification,
perfectness or Noetherian-scheme hypothesis. The parent combines it with the
existing completeness preservation and detection theorems; it does not move its
conclusion wholesale to a renamed theorem.

All new imports in the item are private proof imports. Original public imports
and all existing declaration signatures are preserved. No source-library module
or other group's module is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.sfbAdicComplete_of_stratum_local_iso`
(node `lem-sfb-adic-complete-stratum-gluing`).

Added one hole, the entire proof of
`AlgebraicGeometry.Scheme.sfbNormalizedLocalRestriction_iso`
(node `lem-sfb-normalized-local-restriction-iso`). This is a decomposition,
not a net hole closure: one original hole closed and one strictly smaller
comparison obligation added. There are no holes in the item or the coefficient
normalization module. The coefficient normalization and its completeness
equivalence are proved.

## No longer needed

Removed the redundant direct proof imports of `Mathlib.RingTheory.Finiteness.Defs`
and `Mathlib.CategoryTheory.Sites.CoverLifting`: both are already available through
the original public import closure. The route retains the existing preservation and detection
statements. Scalar-restriction completeness is still needed by the proved
normalization helper. No original import, dependency node, module or upstream
declaration is withdrawn. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned site and coefficient comparisons were not themselves supplied by the
normalized stratum theorem. Its completed coefficient ring and actual restriction
functors differ from the original presentation used by `IsSfbAdicComplete` and
`sfbLocalRestriction`. This delivery proves the global coefficient and kernel
comparison and leaves only the local restriction isomorphism comparison. The
new obligation is exactly the comparison portion of old step 2, with no global
gluing or completeness conclusion.

Sources read: Bhatt--Scholze Lemma 6.5.8, Remark 6.5.10 and Proposition 6.6.11;
Stacks `algebraization.tex`, `lemma-restriction-derived-complete`; the current
blueprint integral-models unit and all named dependency signatures. Edge cases
checked: empty schemes and strata, empty covers, zero/unit ideals, arbitrary
unbounded comparison objects, and nonperfect residue quotients. The comparison
uses site equivalences and coefficient isomorphisms; none needs a point,
nonempty stratum, or finite Tor dimension of a residue quotient.

The blueprint ancestor tool follows `created.item`, but the current parent
records module names in that chain and reports no ancestor. The new nodes retain
the explicit established blueprint ancestor `det-lem-integral-models-stacks` from
the item's existing `blueprint.from`, with the precise comparison sentence.

## New nodes

`lem-sfb-completion-normalization`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-completion-normalization.json`, records
the proved canonical coefficient comparison and completeness equivalence in
`lean/Sheaf/Paper/SfbCompletionNormalization.lean`.

`lem-sfb-normalized-local-restriction-iso`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-normalized-local-restriction-iso.json`,
records the sole remaining local comparison in
`lean/Sheaf/Paper/SfbNormalizedLocalRestrictionIso.lean`. Its docstring and node
give the complete argument via slice-site equivalences, finite projections,
module-adjunction uniqueness, and exact termwise localization. The geometric
inverse-image and immersion limit-preservation results are used as generic tools,
not as a replacement for the integral-model unit route.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
