# lem-pc-cartier-divisor-finite-over-field

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-cartier-divisor-finite-over-field.json`: split the item into the four steps of Tag 0AYY.
- `dag/nodes/sec-picard-framework/lem-pc-cartier-divisor-nowhere-dense.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-nowhere-dense-dim-zero.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-dim-zero-finite-over-field.json`: new statement, unsplit; no Mathlib match.

## Attachments

None. `IdealSheafData.IsInvertible.isFinite_subschemeι_comp` in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:336` assumes a smooth proper curve, whereas this item assumes only a proper scheme of dimension at most one; it does not state the item. Its docstring identifies `def-sc-effective-cartier-divisor`, not this node.

## Wanted

WANTED: `literature/stacks-project/varieties.tex`, Tags 0AYY and 06LH, for lem-pc-cartier-divisor-finite-over-field and lem-pc-dim-zero-finite-over-field.
WANTED: `literature/stacks-project/divisors.tex`, Tag 07ZU, for lem-pc-cartier-divisor-nowhere-dense.

The Stacks source tree is absent on this machine. I read the three tagged lemmas on the Stacks website. The local `source` paths identify the project documents to restore; the item's `proof_origin.by` is `agent` because those documents are not present under `literature/`.

## Corrections and limits

The imported item had no proof. The earlier sandbox draft paraphrased 07ZU as only topological nowhere density; I corrected the new node to state its scheme-theoretic density conclusion and then take the topological consequence. I made the finite-type hypothesis explicit at the dimension-drop step: proper over a field supplies it. Tag 06LH says an algebraic zero-dimensional scheme is finite and affine; the new node applies this to the proper case. The existing properness lemma is from another unit, so its use is declared in `split_report.tool_uses`. The item itself has no exact sorry-free Lean declaration. No part of the split remains unfinished at this one-level stage; the three new nodes intentionally have statements only and remain unsplit.

## Review by J1

I read the item against Stacks Tag 0AYY, “degree of an effective Cartier divisor,” specifically the first two sentences of its proof. I read Tag 07ZU, “complement of an effective Cartier divisor,” for the first new node: it works on any scheme and asserts that the complement is scheme-theoretically dense, which implies the topological density used by the item. I read Tag 06LH, “algebraic schemes of dimension zero,” for the third new node: its algebraic case asserts finite and affine over the field, with finite-dimensional coordinate ring. The second new node isolates the intermediate dimension inference explicitly written in 0AYY; it needs finite type, because its noetherian topology lets a positive-dimensional closed component contain an irreducible component of the ambient scheme in dimension at most one.

Step 1 cites only `lem-pc-cartier-divisor-nowhere-dense`. Its statement supplies scheme-theoretic density of the complement; ordinary density and the empty-interior conclusion are direct consequences. Step 2 cites `lem-pc-nowhere-dense-dim-zero`, whose statement has exactly a finite-type field scheme, a closed nowhere-dense subscheme, and the dimension-at-most-one hypothesis. Properness of X supplies finite type, and step 1 supplies nowhere density. Step 3 cites `lem-weil-pbc-closed-immersion-proper`, whose statement explicitly covers a closed subscheme of a proper scheme. The defining effective Cartier ideal supplies the closed immersion; the item supplies properness of X. Step 4 cites `lem-pc-dim-zero-finite-over-field`, whose hypotheses are step 2's dimension bound and step 3's properness. Its conclusion supplies finiteness, affineness, and the finite-dimensional global section ring.

I compared the new nodes against the whole DAG by their Stacks tags and mathematical phrases, and searched blueprint references for “nowhere dense,” “proper zero-dimensional,” “dim0 finite,” and “Cartier divisor.” The related blueprint node `lem-sc-dim0-finite` states only that a closed zero-dimensional subset has finitely many closed points, not finiteness of a scheme over a field; `lem-sc-proper-affine-finite` requires affineness in advance. Neither duplicates a new statement. I checked the recorded LeanSearch or LeanFinder/Loogle and Mathlib source searches in each new node; no exact declaration appeared. Each new node has its own objects and hypotheses, a Stacks tag with label, and an empty proof and proof-dependency list.

For small cases: if D is empty, its complement is all of X, its dimension is at most zero by the empty convention, and the empty scheme is finite over k. On X = Spec k[t], D = V(t), the complement is dense and D is one zero-dimensional point. On X = Spec k[t]/(t²), no nonunit nonzerodivisor can define an offending Cartier divisor; D = V(1) is empty. For Tag 06LH, Y = Spec(k[ε]/(ε²)) is a finite affine nonreduced zero-dimensional case; a finite disjoint union of such schemes also satisfies the conclusion. These cases guard against silently assuming reducedness, nonemptiness, or smoothness. The correction to the 07ZU statement and the explicit properness-to-finite-type inference came from this review.
