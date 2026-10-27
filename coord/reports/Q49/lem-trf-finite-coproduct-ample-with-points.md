# Worker report: lem-trf-finite-coproduct-ample-with-points

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-coproduct-ample-with-points.json`: statement, now split in six steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for each node used by each proof step (21 entries).
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. `searches.jsonl` was written by the required search command; `write_split.py` is the sandbox-only script used to write the JSON.

## Attachments

None. Searching the whole `lean/WeilConjectures/` tree for the exact node id gave no declaration. Concept searches found `Scheme.Modules.IsAmple` in `AlgebraicGeometry/Ample.lean`, the affine-pullback theorem in `AmplePullback.lean`, and the unrelated proper-over-a-field `AlgebraicGeometry.IsAmple` in `Modules/Ample.lean`. None states the whole item. In particular the affine-pullback theorem proves only the forward implication after verifying affineness of the coprojections; it cannot attach the item.

## WANTED

None. The argument uses available Stacks sources only. No SGA source is used.

## What was wrong or incomplete

The item was a statement-only supporting node created for `lem-trf-fibre-degree-ample-criterion`. Its statement is correct, including without finite-type, Noetherian, base-field or properness assumptions, and remains unchanged. The source description refers to the finite disjoint union and isolated point summands implicit in Varieties Tag 0B5Y; it did not itself supply the proof for the item's more general, arbitrary-scheme formulation. I supplied that proof directly from absolute ampleness (Properties Tag 01PS), scheme sobriety (Schemes Tag 01IS), and the field at the generic point of an integral scheme (Morphisms Tag 01RV).

No correction of the blueprint/unit route is needed. The original `blueprint.from` ancestry and all imported/created metadata are preserved. The current blueprint ancestor is the contracting local-term lemma, which is only the historical ancestry of the supporting geometry developed through stable modification; neither that lemma nor the unit proof is used as an ampleness theorem.

## Searches and reuse

The sandbox initially contained no node, report, citations or search log, so I copied the live item once. There was no released stage-1 repair record for this item. I retained its historical Mathlib searches and metadata.

DAG searches used `rg` for ampleness/disjoint unions/restriction, zero-dimensional integral schemes, the relevant Stacks tags and labels, and the titles and statements of existing nodes. `tools/blueprint_refs.py ancestor lem-trf-finite-coproduct-ample-with-points` identified `lem-trf-local-term-locality`; searches for `ample`, `finite disjoint union` and `zero-dimensional integral` found no equivalent imported blueprint node. The proper-field very-ample disjoint-union node has stronger base/properness hypotheses and the different projective notion of ampleness, so is not substituted. The existing `lem-weil-pbc-zero-dim-integral-point` requires finite type over an algebraically closed field; it cannot be applied to the arbitrary integral schemes in this item. This does not require a new generalization node: the singleton argument is two lines from dimension zero and sobriety, and the existing arbitrary-integral generic-field lemma completes it.

The required `msearch.py` commands were run for the item with LeanFinder, Loogle, grep and LeanSearch, and a second semantic phrasing was run. Their actual results are in `searches.jsonl` and copied into the item's `mathlib_searches`. The grep for `IsAmple|\bample\b|ampleness` in `AlgebraicGeometry` returned zero hits. Loogle reported the project-specific IsAmple identifier unknown, as recorded. The successful semantic services returned affine coproducts and quasi-separated localization/open-cover lemmas, not an ample-line-bundle theorem. I read the returned statement/types; finite coproduct affineness is not the item and none handles an arbitrary invertible module. No unavailable service is represented as mathematical evidence of absence.

## Not duplicates

There are no new nodes, so there are no new/existing pairs to distinguish. Existing nodes are cited rather than recreated, including the scheme coproduct, scheme sobriety, integral generic-field, affine closed-embedding, affine ample-pullback and invertible pullback/tensor statements.

## Review by Q49

I read the item against Properties `definition-ample` (Tag 01PS, properties.tex lines 4244 onward) and the proof of Varieties `lemma-ampleness-in-terms-of-degrees-components` (Tag 0B5Y, varieties.tex lines 10070 onward). That proof explicitly adds isolated residue-field points to the union of curves. It motivates the item but is not treated as a theorem about arbitrary disjoint unions. I also read Schemes `lemma-scheme-sober` (01IS, schemes.tex line 1930), Morphisms `lemma-integral-scheme-rational-functions` (01RV, morphisms.tex line 12705), and `lemma-homeomorphism-affine` (04DE, morphisms.tex line 11338). There are no new-node sources to audit.

For Step 1 I opened `def-pc-integral-scheme`, `def-kun-topological-krull-dimension` and `lem-sc-scheme-sober`. Integrality supplies nonemptiness and irreducibility. Sobriety really asserts a unique generic point for every irreducible closed subset of any scheme. If the closure of another point were proper, it and the whole space would be a length-one irreducible closed chain; dimension zero rules that out. Thus the uniqueness conclusion applies to every point. No assertion that arbitrary zero-dimensional schemes are discrete is used.

For Step 2 I opened `def-pc-scheme`, `lem-sc-integral-function-field-affine-fraction`, `def-weil-pbc-module-stalk` and `def-weil-affine-spectrum`. The cited field lemma explicitly allows ANY integral scheme with its generic point and a nonempty affine open, rather than only a curve or a finite-type scheme. All its hypotheses are present. An affine chart about the unique point is the entire scheme. The stalk definition says it is the colimit over neighbourhoods; here there is only one neighbourhood, so it equals the global ring. The affine-spectrum definition identifies the global ring with the chart ring, giving the actual isomorphism to the spectrum of a field. No field structure is inferred merely from a name or a definition of a function field restricted to curves.

For Step 3 I opened `def-sc-invertible-module`, the ampleness definition and `lem-weil-pbc-invertible-pullback-invertible`. Local freeness of rank one gives a frame on the whole one-point scheme, and the frame's value is nonzero in the field from Step 2. The sole nonvanishing locus is that affine scheme and a singleton is quasi-compact by the open-cover definition. The pullback lemma explicitly gives invertibility for the modules on the point summands, so the assertion about arbitrary invertible modules really covers each restricted module.

For Step 4 I read `lem-weil-pbc-scheme-coproduct-family`, `lem-trf-closed-embedding-affine` and `lem-weil-pbc-pullback-ample-invertible`. The coproduct node gives open immersions with pairwise disjoint images covering and explicitly concludes each image is closed as well. The closed-embedding node asks only for a homeomorphism onto a closed subset, not a surjection of structure sheaves; that is exactly what is established. The ample-pullback node asks for an affine morphism and absolute ampleness, which are now present. These two supporting statements are general tools, not claims borrowed from their proofs. They are Mathlib or closed results in the node records; any additional off-unit tool declaration required by the records is in `split_report.tool_uses`.

For Step 5 I opened the quasi-compact-scheme definition and checked that the direct open-cover argument does not invoke an unstated compactness theorem: restrict the given cover to each summand, take finitely many indices there, and take the finite union over finite I and J. Every Y_i is quasi-compact from its own ampleness, while each P_j is already a singleton. No uniform bound on the chosen subcover sizes is required.

For Step 6 I opened `def-pc-module-pullback`, `lem-weil-pbc-invertible-pullback-tensor`, `def-weil-sheaf-of-modules-category` and the two previously read coproduct/ampleness nodes. The tensor lemma's clause (2) explicitly gives pullback-tensor comparison; iteration gives the restriction of the nth tensor power. Open pullback is ordinary restriction directly from its ring-sheaf tensor formula. The two-open gluing argument is written out: use s on W and zero on its open complement; the empty overlap has one section. The global section has the original germs on W and zero germs off W, so its affine nonvanishing locus is exactly W_s, not the whole union of unrelated loci. This is the sheaf axiom and the definition of nonvanishing, not an unquoted extension-by-zero theorem. Each point may choose its own exponent; the absolute definition needs no common exponent. The step is elementary from the cited statements and definitions and is 1353 characters, below the long-step threshold.

I checked delivery-errors B--E point by point. There are no statement-only nodes carrying hidden proofs, no new definitions, no restated clause nodes, no dependence on the proof of a cited lemma, and no uncited non-elementary fact. `proof_deps` is exactly the union of `uses`. Each citation quote is a verbatim full statement of its node, including all hypotheses, and I checked that the intended clause is actually in it. Neither statement nor hypotheses have been weakened.

The small cases checked were I=J=empty (empty scheme and vacuous pointwise ampleness), I empty and J nonempty (a finite disjoint union of field spectra), J empty (the general finite-union criterion), empty Y_i, identity single-summand coproducts, arbitrary field spectra rather than only algebraically closed residue fields, non-Noetherian Y_i, and a non-quasi-compact Y_i (then neither the assumed component ampleness nor global ampleness can hold). The integral-point assumptions exclude the empty point summand and exclude nonreduced Artinian points, so neither is accidentally used as an example satisfying them. Infinitely many point summands would invalidate quasi-compactness, and finiteness is explicitly used at Step 5.

## Unfinished work

None in the mathematical split. Server dry-run and delivery results are recorded below when available.

## Validation

The required server dry run exited 0 and printed `OK (not pushed)` at commit `7895dfe75d5`; server preflight passed. No check script or Lean compiler was run locally. The delivery consists of the existing item split, with 0 new nodes and 0 new Mathlib leaves.
