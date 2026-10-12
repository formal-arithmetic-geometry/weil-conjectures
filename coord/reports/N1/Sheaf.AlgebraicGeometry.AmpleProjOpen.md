## What changed

Replaced the only sorry in
`Sheaf.AlgebraicGeometry.AmpleProjOpen` by a complete proof of
`AlgebraicGeometry.exists_isOpenImmersion_proj_of_isAmple`.
The signature, visibility, definitions, and public imports are unchanged.
Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`.

The proof takes the finite affine nonvanishing cover from
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_affine_cover`.
It inserts each section into the explicit section ring with `DirectSum.of`,
proves its degree evaluation using `DirectSum.of_eq_same`, and establishes
that the chosen affine opens equal the corresponding nonvanishing loci.
It applies `AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_affine_charts`
to get one morphism and isomorphisms on its chosen target charts.
The inverse-image identity shows that these charts cover the image; Mathlib's
`IsZariskiLocalAtTarget.of_range_subset_iSup` then proves the open immersion.
The ring and grading witnesses are the explicit existing section-ring constructions.
No object is defined by choosing an arbitrary witness of an unproved existence result.

Updated `lem-sc-ample-proj-open`'s proof and proof_origin to describe the compiled argument.
Its two proof dependencies remain unchanged. The unit is `sk-thm-curveestimate`;
this auxiliary node does not replace any realized unit statement or step.

Searches: LeanFinder for the local-isomorphism criterion; Loogle for
`AlgebraicGeometry.IsOpenImmersion`; launcher grep and direct rg for
open-immersion cover criteria in Mathlib, WeilConjectures, and Sheaf.
No existing ample-to-Proj theorem was found. Mathlib's criterion supplies the
final gluing step. Checked the source proof at https://stacks.math.columbia.edu/tag/01Q1;
the local literature checkout contains citation lists but not properties.tex.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_isOpenImmersion_proj_of_isAmple`
(node `lem-sc-ample-proj-open`), one of one original holes.
Added holes: none. Remaining holes in the delivered module: none.

This is a proof from existing stated dependencies, not a new decomposition.
It continues to depend on the existing theorems
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_affine_cover`
(node `lem-sc-ample-finite-affine-cover`) and
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_affine_charts`
(node `lem-sc-ample-proj-local-chart`), whose own proofs still contain sorry.
The explicit section-ring algebraic laws also remain existing proof obligations.
Thus this delivery closes the item's direct hole, not its entire axiom closure.

The single-file compiler accepts the proof without warnings. The empty scheme
requires no nonempty finite index set: both cover obligations quantify over points,
and Mathlib's image-containment criterion accepts an empty family of target opens.
For an affine scheme with its structure sheaf and projective space with O(1),
the same degree embedding and chart argument apply; no extra hypotheses were added.

## No longer needed

None. Both original proof-dependency imports and both planned dependency nodes
are used. No modules are pruned. The public imports remain because they provide
the statement's notions and preserve the original exported interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found in this item or its two stated
proof dependencies. The final gluing step can be implemented directly using
Mathlib's existing target-local criterion, without constructing a glued
isomorphism or adding a new theorem. No forced adaptations or change records
are required.

## Second reading by N1

1. **Interface and accidental changes.** Compared the delivered module with the
   repository version. The theorem signature, visibility, definitions, and
   existing declarations are byte-for-byte unchanged. The only module change is
   the proof and one plain proof-only import. The DAG node changes only its
   recorded proof route and origin.

2. **Compilation and axioms.** Compiled the module with the launcher compiler;
   it succeeds without errors or warnings. The module contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and no definition
   contains a hole. The theorem's remaining `sorryAx` dependencies are exactly
   the two pre-existing proof-dependency theorems named above.

3. **Statement and proof validity.** Checked the existential witnesses and the
   chart-cover argument against the declarations of both dependency nodes and
   Mathlib's `IsZariskiLocalAtTarget.of_range_subset_iSup`. The proof constructs
   the section ring and homogeneous sections explicitly, so it adds no
   hypothesis and does not choose data from an undetermined existence theorem.
   No split-off statements were introduced.

4. **Pruning and route.** Both declared proof dependencies are used, and the
   unit route through the finite affine cover and local Proj charts is retained.
   The added `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion` import is used
   only by the proof; no removable imports or DAG dependencies were found.

5. **DAG agreement.** The node's proof steps, `proof_deps`, and `proof_origin`
   match the Lean proof, including the final target-local gluing criterion. The
   unit's `realized` route is untouched.

Changed: added this second-reading record only; no source or DAG repair was
needed.
