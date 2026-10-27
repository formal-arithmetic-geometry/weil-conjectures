## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.cartesianCompactSupportCompositor`
with a proof from the named-map equation and invertibility clause of
`FiniteSiteTower.paste`. Choose the canonical etale-origin witness, apply raw alpha's
existing naturality to its underlying isomorphism, and use the raw restriction and
canonical site square. A proved private categorical lemma,
`ProjectionTriangleAssembly.cancel_boundary_square`, pastes those equations and
cancels the three invertible input maps. It contains no sheaf-specific rewrite.

Added `CartesianTowerRestriction.lean` and `CartesianCandidateSiteSquare.lean`.
The first contains explicit source/output inclusion isomorphisms and the raw tower
restriction obligation. The second contains the canonical candidate site-square
obligation, using the shared four-factor constructor and displaying the specified
origin-witness maps. The item imports these privately. The two new inclusion
composites are concrete irreducible definitions;
the proof uses their isomorphism interfaces rather than expanding derived-functor data.
Moved the existing `candidateCompositor` declaration, with its signature, attributes,
docstring and body verbatim, to `CartesianCandidateCompositor.lean`. The item publicly
imports that module, so its existing public name remains available. The site-square
statement now refers to this exact declaration. This avoids a kernel deterministic
timeout (91 seconds) for checking equality with a duplicate of the four-factor formula.
All original public imports remain. The DAG records the shared constructor and the
two normalization subarguments.

All four delivery modules and the unchanged existing consumer compiled through
`lcompile.py` without errors or warnings. The consumer copy was removed afterward.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.cartesianCompactSupportCompositor`.
The private categorical helpers
`ProjectionTriangleAssembly.naturality`,
`ProjectionTriangleAssembly.epi_hom`,
`ProjectionTriangleAssembly.epi_map`, `ProjectionTriangleAssembly.epi_map_map`, and
`ProjectionTriangleAssembly.cancel_boundary_square` are proved.

Added two holes, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.ProEtale.cartesianTowerRestriction`
  (`lem-sf-cartesian-tower-restriction`): the raw proper/open mate restricts to the
  site-interchange tower. This statement mentions no canonical compositor or candidate
  comparisons.
- `AlgebraicGeometry.ProEtale.cartesianCandidateSiteSquare`
  (`lem-sf-cartesian-candidate-site-square`): the independently specified canonical
  compositor has the site square with the etale tower, with a specified origin witness
  retained on the source and target boundaries. This statement mentions no raw
  clopen mate or raw triangle arrow.

This is a decomposition: one original hole closed, two strictly smaller normalization
holes added, zero holes remaining in the item module, two in the delivered modules.
It does not establish an axiom-free proof of the mathematical result. The finite-site
pasting and cancellation between the two comparisons, and transport using raw alpha
naturality along the origin witness, are complete Lean proofs.

## No longer needed

No existing public imports were removed and no existing modules are withdrawn.
The assembly's only direct use among the original nine proof dependencies is
`lem-sp-finite-site-tower-paste`. The other direct edges change as follows:

- `lem-sf-open-tensor-normalization`, `lem-weil-pbc-mate-pasting`, and
  `lem-sp-proper-open-coefficient-mate` belong to the raw restriction node.
- `lem-amb-unbounded-compact-support-comparisons` and
  `lem-pur-compact-support-site-coherence` belong to the canonical site-square node.
- `lem-exc-proetale-derived-open-restriction` supplies the restriction comparison used
  by the coefficient-mate argument, rather than the final cancellation.
- The specialized statements `lem-sf-ambient-proper-open-pasting` and
  `lem-exc-etale-origin-proper-open-interchange` are not applied to the arbitrary ring A.
  The raw restriction argument uses the ordinary-calculus construction and the generic
  coefficient-mate statement instead.

These are changes of direct proof edges, not global pruning: the original public
imports are retained, and no claim is made that any existing module becomes unreachable.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing `proEtaleCompositionTowerNormalization` theorem is not a direct
specialization: it assumes a special coefficient presentation, separated structure
maps, and a selected pullback compactification, whereas this item uses every finite
commutative ring, no separatedness of structure maps, and arbitrary supplied Cartesian
towers. Those stronger hypotheses have not been added to the item or either new lemma.
The recorded plan is mathematically appropriate, but its two normalization comparisons
are not directly supplied in the exact ambient/D+ interface of the assigned statement.

The new statements were checked on identity factors, empty opens, and arbitrary finite
commutative rings: their equations retain the canonical adjunction units and inclusion
comparisons, so these cases require no exceptional treatment or invertibility of an
arbitrary adjunct. Every inclusion comparison is a concrete composite, with no choice
from an unproved existence theorem.

## New nodes

`lem-sf-cartesian-tower-restriction` records the raw-mate/D+ restriction step, including
the explicit `CartesianTower.sourceInclusion` and `CartesianTower.targetInclusion`
constructions. Its remaining proof is the Cartesian projector identity, open adjunct
normalization, and compatibility of the proper/open compositors with inclusion.

`lem-sf-cartesian-candidate-site-square` records the canonical-compositor site square.
Its remaining proof is the etale compositor normalization, cancellation of the
canonical candidate/site comparisons, and the four naturality squares for the
specified origin witness. Each new node has its full Lean statement,
source, dependency list, and natural-language proof.

`def-sf-cartesian-candidate-compositor` records the existing concrete constructor in
its shared module. It adds no theorem hole and does not change the selected maps.

Change record: `coord/changes/f5-cartesian-candidate-compositor-module.md`.
The existing downstream consumer is `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly`;
its public name and signature dependencies are preserved.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
