# Q150 — lem-trf-fibre-purity-from-high-dimension-image

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fibre-purity-from-high-dimension-image.json: statement, split; no exact Mathlib match. Statement and statement dependencies unchanged; two proof steps added.
- citations.json: eight entries, one for every step/node citation, copied verbatim from the current cited statements.
- searches.jsonl: actual search-command log; the item preserves its earlier searches and adds the five searches run in this attempt.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter files changed.

## Attachments

None. Searched WeilConjectures for the blueprint tag and for pure dimension, equidimensionality, fibre dimension and base-change terminology. Read AlgebraicGeometry/Dimension.lean and FiberDimension.lean: the former defines whole-fibre relative dimension and the latter bounds dimensions under morphisms; neither proves this local-dimension/image criterion with its component clause. No sorry declaration is counted as an attachment.

## WANTED

None. All mathematical source passages used are available locally.

## Findings and corrections

The imported item had no proof. I retained its full statement, including arbitrary base change, empty fibres, the equality at every point and componentwise purity. The proof follows the last two sentences of Stacks limits.tex Tag 0EY2 (lemma-descend-dimension-d) and makes the component inference explicit rather than interpreting global dimension d as pure dimension d. The existing lem-trf-field-extension-component-local-dimension gives the precise component formula, so no new lemma is necessary.

The existing component lemma's source calls its general collection Tag 0A21; the exact item used is varieties.tex Tag 0B1B, item-dimension-irreducibles-passing-through. I read that item, and cite it precisely in this item's proof source. I did not modify the other node. The local dimension here is the minimum of dimensions of open neighbourhoods, not the dimension of a local ring: at the generic point of an affine line these are respectively 1 and 0.

Read the latest blueprint's lem-trf-local-term-locality statement and proof, the chapter record and sk-i-curve-zero unit. The semistable-model ancestry is the existing subsidiary DAG chain rather than an explicit sentence of the current short blueprint proof; retained that provenance and followed the item's explicit Stacks source. No unit argument or chapter route is replaced. Whole-blueprint searches for dimension at, pure dimension, field extension dimension, high fibre and fibre purity found no equivalent blueprint statement. DAG searches located the existing base-change and component lemmas, which are reused.

## Not duplicates

No new nodes. In particular lem-trf-field-extension-component-local-dimension already states the field-extension component formula needed here; no duplicate is introduced. The item is distinct: it deduces purity from a lower bound on the image and a global upper bound, whereas that existing lemma has no such image condition.

## Unfinished work

None for this stage-1 split. Proofs of the cited nodes remain their own DAG tasks. No Lean was written or compiled.

## Review by Q150

I read limits.tex lemma-descend-dimension-d (0EY2) in full, morphisms.tex lemma-dimension-fibre-after-base-change (02FY), morphisms.tex lemma-base-change-finite-type (01T4), and varieties.tex lemma-dimension-locally-algebraic, especially its item-dimension-irreducibles-passing-through (0B1B). No new node requires an additional source review. I also read each of the six distinct cited node statements and checked the eight step/citation occurrences against those statements; citations.json records their actual text.

Step 1 uses def-weil-finite-type-morphism only for finite type implying locally finite type. The statement of lem-sc-fibre-dimension-after-base-change explicitly applies to arbitrary g and supplies the exact local topological fibre-dimension equality. The statement of def-kun-topological-dimension-at-point makes the whole original fibre an admissible neighbourhood, giving local dimension at most its global dimension, which is at most d by the hypothesis. Image containment supplies the opposite inequality. Antisymmetry is the remaining elementary inference. This step assumes neither flatness nor finite presentation, and does not infer local-ring dimension from local topological dimension.

Step 2 uses the same base-change lemma's explicit residue-field description of the fibre, rather than an unstated comparison construction. The definition def-pc-scheme-fibre identifies Y=X_t as the base change of f to Spec kappa(t); lem-weil-pbc-lft-base-change then gives precisely the locally finite type hypothesis required by lem-trf-field-extension-component-local-dimension. The latter's statement gives a generic point for each component and dim D = dim_z(Y_L). Step 1 applies to that very point of the base-changed fibre, so this equals d. Finally def-weil-pure-dimension defines purity by these component dimensions. Thus there is no missing sobriety or Noetherianity lemma hidden here: those conclusions and the generic-point formula are already in the cited component lemma's statement. The two off-unit generic tools are declared in split_report.tool_uses, with their purposes.

I checked B through E of delivery-errors.md, including the repeated sections: no new nodes or duplicated clauses, all objects introduced, no proof sketches substituted for arguments, no unsupported tag-only inference, no inline non-elementary lemma, and no extra hypothesis on g. Both steps are below 2000 characters. Tests: empty X or T' gives vacuous point/component assertions; d=0 gives dimension zero at every actual point and every component; an identity base change with a point disjoint from a line and d=1 fails the image condition on the point, as required; intersecting components of unequal dimensions still fail at the smaller component's generic point. Arbitrary transcendental or inseparable residue-field extensions are allowed by the component lemma. No statement dispute was found.

The actual Mathlib queries returned finite-type/smooth base-change permanence, generic components and global dimension monotonicity. I read their displayed types and the grep hit AlgebraicCycle/Basic.lean:65, which is documentation, not a theorem. Smooth permanence has an extra smoothness hypothesis; none of these hits states this item or specializes to it in one line. The second LeanFinder phrasing confirms that result. Every recorded new search is from the command's actual log; none of the five services was unavailable.
