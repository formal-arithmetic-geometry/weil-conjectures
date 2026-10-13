## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity`
with a compiling assembly of flatness and formal unramifiedness. The existing theorem's
signature and public imports are unchanged. Its two new imports are proof-only.

Added `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat`, which isolates
flatness from the formal-completion part of Stacks 0EYB, and
`Sheaf.AlgebraicGeometry.Morphisms.FlatDepthTwoFiniteFormallyUnramified`, which isolates
formal unramifiedness for an already flat finite extension from Stacks 0BJH / 0EY6(3).
The latter has no smooth-family, fibre-density or target-depth hypothesis. The final
Lean proof supplies local Noetherianity, obtains the two classes separately, and uses
Mathlib's finite-presentation instance and `Etale.of_formallyUnramified_of_flat`.

Read Stacks Tags 0EYB, 0EYA, 0EY6, 0BJH, 05D5 and 00MB online. Checked the unit record
`sk-prop-input-spreading`: its depth-two completion route is retained. The local copy
of its referenced blueprint section is absent; the unit JSON records the full route.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.Scheme.etale_of_smooth_local_depth_two_finite_extension`
(node `lem-sbc-smooth-local-depth-two-finite-purity`). No direct hole remains in the item.

Added exactly two holes, each the entire proof of a public theorem in its own new module:

- `AlgebraicGeometry.Scheme.flat_of_smooth_local_depth_two_finite_extension`
  (node `lem-sbc-smooth-local-depth-two-finite-flat`).
- `AlgebraicGeometry.Scheme.formallyUnramified_of_flat_depth_two_finite_extension`
  (node `lem-sbc-flat-depth-two-finite-formally-unramified`).

This is a decomposition, not a complete proof free of admitted dependencies:
one upper hole closed, two lower holes added, net -1. Flatness is only one requirement
for etaleness; the other lemma assumes flatness and proves the separate infinitesimal
uniqueness property. Neither has the original hypotheses and conclusion.

The full three-module sandbox compiles through lcompile.py. Edge cases checked against
the sources: empty E, U = L, disconnected smooth fibres, and no quasi-compactness of L.
The flatness proof works in affine charts. If U is empty, density forces any nonempty
closed fibre to be excluded by the hypotheses; the proof does not assume U nonempty.
In the second theorem, ramified flat finite morphisms in dimension one are excluded by
the source boundary depth condition, since depth is bounded by local dimension.

## No longer needed

No existing import was removed and no entire module is claimed pruned. The original
item's direct planned dependency `lem-weil-pbc-flat-local-depth-formula` is replaced by
the two new nodes. The flat local depth formula remains needed inside the future proof
of the formal-completion flatness lemma; it is not globally pruned. No normalization,
Galois-action, section-torsor or finite-etale existence module is imported: none supplies
the statement needed for this general supplied finite extension over a possibly
nonnormal local ring.

## Where the brief, the DAG or earlier work was wrong

The existing node's second proof step contains the whole formal-completion purity
argument but has no dependency nodes. It cannot be assembled from its sole recorded
flat-local-depth-formula declaration. This delivery exposes the missing flatness core
and the independent local ramification criterion rather than importing a circular
finite-etale existence theorem. No existing statement or definition is changed.

The target-depth calculation initially suggested for the second piece is unnecessary:
Stacks 0BJH applies directly using source depth two and flatness. Every source point
of dimension one lies over U, and a missing point is nongeneric. The resulting second
lemma is more general than the normalization-specific existing flat-to-etale theorem,
which cannot be applied here because normality and a normalization presentation are absent.

## New nodes

`lem-sbc-smooth-local-depth-two-finite-flat`: flatness of the supplied finite extension,
following the residue-field base change, etale slice, smooth section completion,
power-series extension, uniqueness and descent steps of 0EYB. Its source and complete
proof in words are in the declaration docstring and matching DAG node.

`lem-sbc-flat-depth-two-finite-formally-unramified`: formal unramifiedness of a finite
flat morphism whose nonetale boundary has source depth at least two. The proof in words
checks all four local hypotheses of 0BJH. Each node records actual LeanSearch,
LeanFinder and grep searches from searches.jsonl; LeanSearch returned Internal Server
Error and is recorded as unavailable. DAG and blueprint searches found no matching
existing node. No change record is needed, since existing signatures and visibility
are unchanged and no other module is adapted.

## Second reading by A2

1. Compared the existing module with the repository using diff. Its only existing
   declaration has a byte-for-byte identical signature, including every hypothesis,
   universe and conclusion. Existing public imports and visibility are unchanged;
   the two new imports are plain proof-only imports. No definition or target changed.
2. Compiled all three modules in import order with lcompile.py: no errors or warnings.
   Inspected all declarations: exactly the two reported public theorem holes remain,
   each with an entire `by sorry` proof; no data definition, forbidden declaration or
   arbitrary existence witness was added. A scratch copy with `#print axioms` for all
   three declarations compiled and showed only propext, Classical.choice, Quot.sound
   and sorryAx. The upper result still depends on the two admitted lower results.
3. Read the two split statements and their docstrings against Stacks
   https://stacks.math.columbia.edu/tag/0BJH,
   https://stacks.math.columbia.edu/tag/0EY6,
   https://stacks.math.columbia.edu/tag/0EYA and
   https://stacks.math.columbia.edu/tag/0EYB. Both are true and are separate parts of
   the argument. Checked empty source, full open, empty closed fibre, relative
   dimension zero, dimension-one ramification and non-quasi-compact target cases.
   Independently searched LeanFinder for finite-flat codimension-one ramification,
   Loogle for FormallyUnramified, and Mathlib grep for ramification/purity/codimension;
   no matching purity criterion was found. Searched both library roots and read the
   existing normalization flat-to-etale and depth-two extension declarations: their
   extra normalization structure or existence conclusion prevents replacing these
   lemmas. Neither split can be closed by an available short argument.
4. The Lean assembly takes the direct Mathlib flat/formally-unramified criterion.
   Both new proof imports are used; existing imports supply the unchanged interface.
   The old sole proof dependency, flat-local-depth-formula, is accounted for in
   No longer needed: replaced directly, still used mathematically in the flatness
   subproblem, not globally pruned. The unit JSON's depth-two completion step is
   retained, with no unit bypass. Its realized arrays are empty in the baseline;
   this delivery leaves that existing bookkeeping unchanged.
5. Checked all node statements against the Lean signatures, the original node's
   proof_deps against the two applied theorems, and all new-node source, creation,
   search, blueprint, chapter, unit and Lean fields. The records match the assembly
   and the two still-open source arguments. No unreported statement change exists.

Changed the flatness lemma's proof explanation to justify openness using finite
presentation and to explain precisely why relative dimension zero contradicts fibre
density. Synchronized that explanation in its node. No Lean proof or signature
needed repair. This remains one hole closed and two holes added, a decomposition
with net -1, and no module pruned.
