## What changed

Proved `exists_cyclicDerivedHomBoundary` from the raw off-diagonal boundary calculation.
The proof descends an additive map to the actual coinvariant quotient, proves its
injectivity, restricts forgetting to the actual invariant subgroup, proves exactness
and surjectivity, and derives normalized uniqueness from strict presentations.
The four original theorem signatures are unchanged.

Moved the 24 original data declarations verbatim to `CyclicDerivedHomData`, publicly
reexported by the original module. The change record records the complete old and new
interfaces and the unchanged N4 consumer. This avoids an import cycle between the
auxiliary statements and their consumer.

In `CyclicDerivedOffDiagonalPresentation`, constructed the triangular automorphism,
the equivariant inclusion and projection, and the short exact sequence whose underlying
complex sequence splits. Proved `exists_cyclicDerivedStrictExtension` and
`exists_cyclicDerivedOffDiagonalPresentation`, the latter by actual K-injective replacements
and a chain representative for the prescribed underlying morphism. Proved the
existence-and-uniqueness assembly and its unique-value API from a separate uniqueness
comparison. No arbitrary presentation witness supplies data to a definition: the
boundary chooses only its uniquely characterized native morphism.

Compiled all four sandbox modules together after removing unused imports. The unchanged consumer also compiled against this interface without warnings. New statements were
checked on zero objects and zero maps; for the identity action on abelian groups,
the unipotent extension represents the expected nonzero cyclic Ext class. In particular
no claim of faithfulness of derived forgetting is used. The triangular inverse and
all inclusion/projection identities are proved in Lean. Also proved
`cyclicDerivedOffDiagonalPresentation_forget_zero` and
`cyclicDerivedOffDiagonalBoundary_forget_zero`: the actual boundary vanishes after
forgetting, using the split underlying projection and the distinguished SES triangle.

## Proved and sorry left

Original holes: 4. Closed in the item: 1, `exists_cyclicDerivedHomBoundary`.
Added holes: 2. This is a decomposition, not a net reduction of proof obligations:
4 original holes become 3 original holes plus 2 separate raw-calculation holes.

Every remaining hole, with namespace `CategoryTheory.Endofunctor.IsoAlgebra`:

- `cyclicDerivedHom_exact_functorial` (unchanged, original node
  `lem-sf-cyclic-derived-hom-exact-sequence`).
- `cyclicDerivedHom_rightDerived_functorial` (unchanged, original node).
- `cyclicDerivedHom_finite_composite_functorial` (unchanged, original node).
- `cyclicDerivedOffDiagonalPresentation_unique` (new,
  `lem-sf-cyclic-derived-off-diagonal-presentation`): the free-resolution comparison
  showing that any two strict presentations of the same underlying derived class
  have equal native boundaries. Presentation existence itself is proved.
- `cyclicDerivedOffDiagonal_calculus` (new,
  `lem-sf-cyclic-derived-off-diagonal-calculus`): additivity, the three consecutive
  raw exact pairs, and native pre/postcomposition naturality, before passage to a
  quotient or subgroup.

The new modules have one named theorem hole apiece, each with a full proof in words.
There is no hole inside a definition or private helper. The data module has zero holes.
The main theorem is proved by real quotient and subgroup constructions and a separate
normalization argument; neither new theorem restates its existence/uniqueness claim.

## No longer needed

No module is withdrawn and no source-library declaration is removed.

The original item's proof-only imports are removed:
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`,
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
`Mathlib.Algebra.Homology.HomologySequence`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
The implemented quotient proof needs only the new raw-calculus module. The old public
imports now occur in the publicly reexported data module, preserving their visibility.

No original free-resolution, SES, K-injective or functoriality node is claimed globally
pruned: the two retained raw lemmas and three unclosed companions still need those
arguments. The explicit presentation-existence proof uses the existing Grothendieck
K-injective resolution API and the derived Hom localization bijection. Termwise
injectivity is unnecessary for this construction, so no new model-existence dependency
is introduced. The bounded-below and termwise-injective arguments remain needed in the
unclosed functoriality plans; they are not claimed globally pruned.

The parent no longer cites these nodes directly and removes their obsolete parent
`tool_uses` entries: `lem-sf-free-derived-weil-resolution`, `lem-weil-pbc-hom-out-of-triangle-exact`, `lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-kinjective-shift`.
They remain available through the auxiliary results where needed; this is not a claim
of global pruning.

## Where the brief, the DAG or earlier work was wrong

No original statement error was found. The free-resolution module's exported derived
triangle uses a common derived/Grothendieck universe, whereas the item allows independent
derived universes. The remaining raw-calculation proof must transport that calculation
through canonical localization equivalences; the new proof docstrings state this issue.
This delivery does not alter the C3-held free-resolution module.

The original main file combines definitions and the theorem using them. Separate
strict-presentation results could not import those definitions without an import cycle;
the public data-module relocation repairs that dependency layout without changing any
mathematics. The final three companion theorem holes are left unchanged, as the brief
permits for a module with several holes.

## New nodes

- `def-sf-cyclic-derived-hom-data`: attachment for the verbatim relocated data declarations;
  no new mathematical notion, no holes.
- `lem-sf-cyclic-derived-off-diagonal-presentation`: the strict-extension construction,
  proved presentation existence, and the retained uniqueness comparison.
- `lem-sf-cyclic-derived-off-diagonal-calculus`: the raw additive exact sequence and
  its native morphism naturality.

LeanSearch, LeanFinder, Loogle and Mathlib-source grep found only general SES-boundary,
Ext and group-cohomology results, not either cyclic comparison. Blueprint searches for
`off-diagonal`, `coinvariant`, and `fixed pair` found no matching imported node. The new
nodes retain the parent's chapter, unit and inherited blueprint route; the parent node
now describes the actual quotient assembly and marks the companion plans as unimplemented.

Change record: `coord/changes/cyclic-derived-hom-data-relocation.md`.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
