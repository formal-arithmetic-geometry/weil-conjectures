## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.SmoothStrictLocalBaseModel.smooth_strictLocal_base_model`
with an assembly of the existing stated dependencies and one new ordinary-stalk
comparison lemma. All existing declaration signatures, definitions, and public
imports are preserved. No existing module other than the item is changed.

The proof establishes the evaluation kernels, the specified closed pullback point,
smoothness, flatness and locality of the ordinary structural map, locality of
`strictMap`, and conditional Noetherianity. It constructs local affine ind-etale
charts of the strict structural map, base changes them, and uses strict-local
invariance and pointed uniqueness to prove that the specified `strictProjection`
is an isomorphism. It then constructs beta as theta composed with the opposite
ring equivalence of this very projection. The structural and evaluation equations
prove its factorization through `ordinaryMap` by the uniqueness theorem for
`strictHenselizationMap`; no factorization or beta-compatibility lemma is assumed.

Added `Sheaf.AlgebraicGeometry.GeometricStrictLocalStalkPresentation`, which states
only the generic passage from an affine-chart strict-henselization presentation
to a presentation over the actual ordinary scheme stalk. Updated the item's
proof steps, proof dependencies and proof origin to describe the Lean argument.
The new module and its node carry the source and complete remaining proof in words.

Validation: both modules compile through lcompile.py against the server library.
The new module took 3.7 seconds; the final item took 11.4 seconds after removing
unused imports. The existing theorem signature and auxiliary definition section
were compared with the repository and are identical.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.SmoothStrictLocalBaseModel.smooth_strictLocal_base_model`
(node `lem-trf-smooth-strict-local-base-model`). The item now has zero sorries.

Added one hole:
`AlgebraicGeometry.Scheme.geometricStrictLocal_stalk_presentation`
(node `lem-trf-geometric-strict-local-stalk-presentation`). This is the affine
comparison's transport to the actual stalk, with a specified pointed-etale
presentation and its two compatibility equations. It has no smooth morphism,
base-change model, ordinary flatness, canonical strict projection, beta, beta
factorization, or Noetherianity conclusion. The main theorem's combination of
these ingredients is proved in Lean. Thus this delivery is a decomposition
(one hole closed, one added), not a net hole reduction.

All private helper theorems are proved. No definition contains sorry, and no
arbitrary ring is defined by choosing a witness of an unproved existence theorem.
The existential presentation is used only inside theorem proofs.

## No longer needed

The item's proof no longer calls `lem-trf-strict-local-comparison-ind-etale` on
an identity morphism: `lem-weil-pbc-small-strict-henselization-ind-etale` directly
proves the required chart map is ind-etale. The former node is removed from this
item's proof dependencies. This is not a global withdrawal: other consumers,
including the invariance argument, may still require it.

The affine comparison and affine-open stalk localization are still required by
the new stalk-presentation lemma. They are not globally pruned. The affine
comparison's direct proof import in the item is removed because the main proof
uses the new lemma. The proper-morphism import is removed: only smooth base
change is used, supplied by Mathlib's smooth-morphism module. The redundant
proof imports of the flat-morphism and ind-etale universe-transport modules are
removed; their APIs are supplied by the retained imports. No module is withdrawn,
and no unit statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or weakened. The affine comparison declaration has
base `Localization.AtPrime p.asIdeal`, whereas the item requires the actual
scheme stalk with its own geometric residue embedding and a specified universal
presentation. Their transport is a genuine missing Lean interface, rather than
a definitional equality. It is the single new remaining lemma.

The canonical projection in the invariance declaration is supplied as an
isomorphism satisfying the structural and evaluation equations. The proof uses
pointed-map uniqueness to identify it with the item's named `strictProjection`;
it does not assume an arbitrary isomorphism is canonical.

Sources read: Stacks etale-cohomology.tex, lemma-describe-etale-local-ring (04HX)
and the functoriality paragraph after definition-etale-local-rings (03PS);
schemes.tex, lemma-spec-sheaves (01HV); the existing affine comparison,
strict-henselization functoriality, small-model ind-etale, ind-etale chart
base-change, invariance, evaluation properties, and Noetherianity signatures.
The current blueprint unit sk-i-curve-zero and its realized record were checked.
The new comparison was checked on affine schemes, local rings, fields, enlarged
Omega, nonclosed image points, and non-Noetherian schemes. An empty scheme has
no geometric point, so contributes no exceptional case. The residue embeddings
are prescribed throughout, including in positive characteristic.

## New nodes

`lem-trf-geometric-strict-local-stalk-presentation` records precisely the
ordinary-stalk transport in step 3 of the original item. Its source is Stacks
04HX, 01HV and 04GW. The proof first obtains a pointed-etale colimit presentation
from the existing residue-triples construction, then transports the existing
affine comparison along the affine-open stalk isomorphism and the induced
identification of the relative separable closures inside Omega. LeanFinder,
Loogle and Mathlib grep were run; none supplies this strict-henselization
presentation. Project search found the affine comparison already cited, which
has a prime-localization base and assumes a presentation. There are no change
records because no existing interface or definition changes.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
