# Q15 stage-1 delivery: lem-sfb-semiabelian-supplied-norm-ampleness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-supplied-norm-ampleness.json`: item, eight-step split; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-symmetric-cubical-specialization.json`: statement only, unsplit, no Mathlib match. For a supplied symmetric generically ample cubical line over a DVR, asserts ampleness on the closed fibre, without asserting relative ampleness or constructing an extension.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-fibrewise-ample-criterion.json`: statement only, unsplit, no Mathlib match. Assumes ampleness on every residue-field fibre and gives relative ampleness, without any generic positivity hypothesis.
- `citations.json`: one verbatim statement quotation for every use in every item step.

## Attachments

None. Searched `lean/WeilConjectures` for the item id, semiabelian/semiAbelian and the new ids; no declaration states the item or either supporting result. No sorry declaration is treated as a completed proof. No Lean was written and no compiler or Lake command was run.

## Sources wanted

WANTED: Michel Raynaud, *Faisceaux amples sur les schemas en groupes et les espaces homogenes*, LNM 119 (1970), XI 1.13 and 1.16 and the fibrewise positivity argument, for the item and both new nodes.

WANTED: Laurent Moret-Bailly, *Pinceaux de varietes abeliennes*, Asterisque 129 (1985), VI 3.1 and I 2.6, for the positivity comparison and the existing cubical-rigidification input.

Neither book is present in the local literature tree. I did not download either. The item is explicitly an agent proof, and both new nodes explicitly say they are agent formulations, not transcriptions of numbered source theorems. In particular, the nonproper generic-fibre case of the new trait lemma remains part of that lemma's mathematical obligation. Lan is not being cited as proving that extension of scope.

I read online Kai-Wen Lan's revised thesis, https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf, printed pp.75–76, Remark 4.2.1.3 and Lemmas 4.2.1.4–4.2.1.6. His special case has abelian generic fibre and a restrictive degeneration setting; its proof invokes Raynaud XI 1.16 and uniqueness of cubical extensions. It corroborates the positivity issue but is not a proof of the full item or either new node as stated. I also inspected his Remark 3.3.3.9: existence of some ample line cannot by itself prove positivity of the supplied norm.

The local sources actually read for the reduction are Stacks `algebra.tex`, Tag 00PH, `lemma-exists-dvr`, including its full hypotheses, and `morphisms.tex`, Tag 01VJ, `lemma-characterize-relatively-ample`. The supplied-line tensor calculus, smooth/separated/finite-presentation base change, and fpqc ampleness descent are used through the existing nodes' statements.

## Findings and repairs

There was no earlier split/report in the sandbox and no item-specific released repair note in the read tree. The imported item was statement only. I kept its statement and original searches. Its source already called it an agent-formulated inversion-norm version with original WANTED; I have not converted that qualification into a claim of a source proof.

The tempting proof through `lem-sfb-normal-cubical-generic-ampleness`, `lem-sfb-raynaud-generic-ample-power-model`, or `lem-sfb-normal-symmetric-cubical-extension` would be circular: their dependency closures return through `lem-sfb-raynaud-generic-ample-symmetrization` to this item. None is used. I separately checked the closures of the cubical-rigidification, field-descent, affine-cover and DVR tools; none reaches this item.

The ordinary proper ample-neighbourhood nodes, including `lem-trf-noetherian-fibre-ample-neighbourhood` (0D2N) and `lem-sfb-space-relative-ample-locus`, require properness. I did not use them for the nonproper semiabelian group. The second new node isolates exactly the additional group/cubical fibre criterion needed instead.

## Not duplicates

lem-sfb-trait-symmetric-cubical-specialization vs lem-sfb-normal-cubical-generic-ampleness: the former concerns only the closed fibre over a DVR and permits nonproper generic fibre; the latter concludes relative ampleness over a general base but requires proper generic fibre and depends on the item. The new lemma is a one-dimensional specialization input, not another name for the item's arbitrary-base relative conclusion.

lem-sfb-cubical-fibrewise-ample-criterion vs lem-trf-noetherian-fibre-ample-neighbourhood: the new node is a nonproper group/cubical criterion requiring every fibre ample; the existing node is an ample-neighbourhood theorem for proper morphisms, with one fibre assumed ample.

lem-sfb-cubical-fibrewise-ample-criterion vs lem-sfb-space-relative-ample-locus: the existing locus theorem also requires properness and treats arbitrary lines on spaces; the new criterion uses the group/cube hypotheses and makes no representability or universal ample-locus assertion.

lem-sfb-trait-symmetric-cubical-specialization vs lem-sfb-semiabelian-supplied-norm-ampleness: the new node assumes a rigidification, cube and generic symmetry for a supplied line over a DVR and concludes only special-fibre ampleness. The parent must construct a symmetric norm, rigidify on a cover, equip it with a cube, choose DVRs through arbitrary base points, identify both fibres, descend the specified fibre line, and apply the separate fibre criterion and affine-cover theorem. Neither new node individually yields the item's conclusion by specialization.

Whole-DAG statement searches for trait/DVR positivity, fibrewise ampleness, ample loci and cubical lines were made before creating the nodes. Whole-blueprint searches used `tools/blueprint_refs.py search` for semiabelian, cubical, specialization and ample; I also read the current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). No equivalent blueprint node was found. The inherited ancestor is null (`blueprint_refs.py ancestor` confirms this), so I retain it and extend the inherited explicit place/via chain; same_as is empty. No chapter/unit record changes are needed for this supporting node.

## Review by Q15

I reviewed the node files against delivery-errors B–E. Both new statements introduce their base, group, line, fibres and hypotheses, cite their notion nodes, have no proof or proof dependencies, and state propositions rather than proof sketches. Their source qualifications and missing originals are recorded above. I read the available Lan positivity discussion but did not mistake its generic-properness hypothesis for an assertion covering the present nonproper case. These are genuine new mathematical prerequisites, queued for their own splits.

In step 1 I checked that `lem-weil-pbc-invertible-pullback-tensor` gives invertibility, tensor/composition comparisons and permutation of factors, exactly the formulas used. The inversion pullback of an ample line is justified explicitly from the nonvanishing-affine-locus definition: inversion is its own inverse. `lem-sc-ample-tensor` has a general first clause for schemes over a field, so its use is not restricted to the proper abelian example in its last clause. This proves generic ampleness and symmetry of the actual norm.

Step 2 writes out connectedness of a torus extension from its fppf quotient; it does not infer it from an unproved generic-properness claim. I checked that local rank-one freeness and invertible pullback give a trivializing cover of e*N. Step 3 uses case (b) of the exact cubical-rigidification statement: base normality, smoothness, finite presentation, separatedness and geometrically connected semiabelian fibres all hold. The line supplied to it is N restricted to the chosen affine, with a chosen trivialization at the identity; no unrigidified line is called cubical.

In step 4 I read both the DVR node and 00PH. A non-generic point of an integral scheme corresponds on an affine chart to a nonzero prime, so its local domain is not a field. Its fraction field is the original K. The extension L/K is the identity extension, and hence finitely generated with zero generators. The dominating DVR therefore has exactly fraction field K; there is no hidden finite extension, perfection, excellence, strict henselization or completeness assumption. Its residue field may be transcendental over kappa(s), which step 7 deliberately permits.

Step 5 cites the smooth clause (2) of `lem-pc-proper-base-change`, not its unrelated properness clause; `lem-weil-pbc-separated-base-change` supplies separatedness and clause (3) of qcqs-permanence supplies finite presentation. I checked each statement. Group identities and cube identities pull back as equations of maps and sections; the tensor-composition comparisons identify the pulled-back cube. The fraction-field equality identifies the generic pair with the already ample symmetric generic pair. The geometric-fibre definition survives this base change without any constancy of toric rank.

Step 6 uses only the stated closed-fibre conclusion of the new trait node. I checked that the fibre being identified is G_s base-changed to the residue field of R, not G_eta or a fibre of some chosen compactification. Step 7 uses the exact field-extension fpqc-cover node and the fpqc ampleness-descent node for the specified line N_s; the latter expressly covers schemes, arbitrary fpqc field covers, and nonproper morphisms. This is not the weaker existence-of-some-ample-line result. The empty-open condition over a field is included. Step 8 uses the new fibrewise criterion on a cubical line for which every fibre is now ample; then 01VJ upgrades the chosen affine cover to every affine open, using quasi-compactness of the original finite-presentation morphism.

The small cases checked were a field base (no non-generic points or DVR choice), a constant abelian group over a trait, a split torus (including rank zero), a product of a torus and an abelian variety, and a one-dimensional semiabelian degeneration with toric special fibre. A trivial line on a positive-dimensional abelian generic fibre fails the ampleness hypothesis, while it is ample on a torus; the two new inputs do not conflate these cases. I checked that a transcendental residue-field extension causes no descent gap, and that neither new statement assumes proper generic fibre. All eight proof steps are below 2000 characters and none hides the trait positivity or nonproper fibre criterion: those are the two named new nodes.

Mathlib searches were executed with the prescribed msearch.py and are in searches.jsonl. For each new node I read two semantic phrasings, Loogle queries and a source grep. Returned valuative-criterion, affine-fibre and ring-Picard declarations do not state either result; I inspected the relevant source definitions. The new nodes record the actual queries and log output. There are no new Mathlib leaves and no fabricated search records.

The off-unit citations recorded in split_report.tool_uses are generic tensor, smooth/separated/finite-presentation base-change, field-cover/descent, and affine-cover tools; they do not replace a step of the unit's route. No prohibited source is used. No source or statement dispute was established, so the item statement is unchanged.

## What remains

No unfinished part of this one-level split. The two new statement-only nodes, including their explicitly identified source/agent obligations, remain to be split as future DAG items. The missing originals are requested above. Delivery is subject to the dry run and the maintainer's independent mathematical review.
