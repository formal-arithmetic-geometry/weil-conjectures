## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-open-group-image-closed.json`: item split into two proof steps; no new nodes.
- `citations.json`: citation for Step 2.

## Attachments

None. No sorry-free Lean declaration in `WeilConjectures/` states this item exactly.

## WANTED

None. The Stacks Project source is present locally.

## What was checked and corrected

The imported item statement is retained verbatim. I read the source at Stacks Tag 047S (`literature/stacks-project/groupoids.tex`) and its surrounding group-scheme definition. I also read the general field-groupoid result at Tag 04Q6 in `more-groupoids.tex` and the existing DAG node `lem-sfb-field-groupoid-open-image-closed`. The item is a direct specialization: for a group scheme over `Spec k`, take the object scheme to be `Spec k`, the arrow scheme to be the group scheme, source and target both the structure map, and groupoid composition the group multiplication. The group unit and inverse supply the remaining groupoid maps, and a group-scheme homomorphism together with the identity on `Spec k` is a groupoid morphism.

I searched the whole DAG for Tag 047S and for open-image/group-scheme keywords. The existing groupoid node is the relevant general result; no duplicate node was created. I searched the latest blueprint as required. The item already has its blueprint ancestor and field-level `from.place` and `same_as` data; the split report records the exact direct-images proof sentence realized here.

Step 1 is elementary: it only unfolds the group-scheme and groupoid definitions and checks that the group diagrams are the group axioms. I checked the edge cases of the trivial group scheme (image all of `Spec k`) and a nonreduced group scheme; the construction still supplies the groupoid data and imposes no finite-type, separatedness, quasi-compactness, or perfectness condition.

Step 2 cites the existing node verbatim. Its statement says that for absolute groupoid schemes over `Spec k`, a morphism with open point image has closed point image, with no extra finiteness or perfectness assumptions. The hypotheses match after Step 1: the object schemes are the same `Spec k`, the arrow schemes are `P` and `Q`, and the map is `u`. Therefore its conclusion is exactly that `u(|P|)` is closed in `|Q|`.

The Mathlib searches for the item were run with LeanFinder, LeanSearch, Loogle, and Mathlib grep on 2026-10-24; they returned only unrelated ordinary topological-group or immersion results, so no Mathlib leaf applies. The exact queries and results are retained in the launcher search log.

## Review by Q67

I read `groupoids.tex` at Tag 047S, including its group-scheme definition and the proof, and `more-groupoids.tex` at Situation 04Q5 and Tag 04Q6. I opened the cited DAG node and verified that its statement, rather than an implementation detail of its proof, supplies the only non-elementary fact used in Step 2. The cited sentence explicitly covers an arbitrary morphism of absolute groupoid schemes over a field spectrum and concludes closedness from openness, with the same absence of finiteness/perfectness hypotheses as this item.

For Step 1 I checked each object and operation: `V = Spec k`; arrows `P` or `Q`; source and target the structure maps; unit and inverse the group unit and inverse; composition multiplication; and the identity object map for `u`. The group diagrams give the groupoid diagrams pointwise on every test scheme. For Step 2 I checked that the image set is exactly `u(|P|)`, that the openness hypothesis is unchanged, and that the general lemma's conclusion is the required closedness. The elementary step does not hide a separate lemma or introduce a stronger hypothesis. No statement correction was needed.
