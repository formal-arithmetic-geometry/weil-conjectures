# Stage 1 report: lem-sc-picard-product-open

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-product-open.json`: item, split with two proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-h1-product-injective.json`: statement-only, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-h1-multiple-locus.json`: statement-only, no Mathlib match.
- `citations.json`: verbatim statement excerpts for both proof citations.

## Attachments

None. The source declaration `AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd` is specialized to the field case and contains `sorry`, so it is not an attachment for this general-over-base item.

## WANTED

None.

## Not duplicates

- `lem-sc-picard-h1-product-injective` vs existing DAG Kunneth/cohomology nodes: those nodes concern derived or Cech Kunneth constructions and do not state injectivity of the two projection pullbacks on H^1 of a proper scheme product.
- `lem-sc-picard-h1-multiple-locus` vs `lem-sc-picard-diagonal-locally-closed`: the existing node constructs one universal locally closed Picard locus; this node is the separate deformation-theoretic comparison asserting local equality of a locus with an intersection under H^1 injectivity.
- `lem-sc-picard-h1-multiple-locus` vs `lem-sc-picard-product-open`: the item is the two-section product triviality theorem (Tag 0BF3), while this child is the distinct general local scheme-theoretic comparison lemma used inside its proof; it does not assert triviality of a line bundle on a product.

## Review by M1

I read the item statement and the exact source proof in `/home/ubuntu/c1-stacks-review/more-morphisms.tex`, lines 9622--9660, including the preceding `lemma-H1-O-multiple-picard-flat-proper` at lines 9519--9619. The source first invokes Varieties Lemma `varieties-lemma-kunneth` in degree one on the special fibre, which is recorded as `lem-sc-picard-h1-product-injective`; this supplies precisely the injectivity needed and no stronger claim. It then applies the multiple Picard flat-proper lemma to `1 × τ` and `σ × 1`; `lem-sc-picard-h1-multiple-locus` records exactly its local scheme-theoretic equality conclusion. I checked that the item hypotheses supply flatness, properness, finite presentation, universal pushforward, sections, both slice trivializations, and the fibre trivialization used in this application. I searched the whole DAG and blueprint for the Kunneth and multiple-locus statements before creating either node; no existing node stated them. LeanFinder, Loogle, grep, and LeanSearch were run for both new nodes; LeanSearch was unavailable and recorded as such, while the other searches found no Mathlib declaration. I also searched the slopmaster2 source for the blueprint tag and declaration: only the specialized sorry-bearing theorem exists.

The small-case check is consistent: when either fibre is affine with vanishing H^1, the injectivity assertion reduces to the evident zero map, and the multiple-locus conclusion reduces to equality of the already-trivial locus near the point.

## Second reading by M1

- Item statement: checked against More on Morphisms, Lemma `pic-of-product`, Tag 0BF3; flatness, properness, finite presentation, universal pushforward, sections, slice triviality, and fibre triviality all match.
- Item step 1: checked against Varieties, Lemma `varieties-lemma-kunneth`, Tag 0BED, in degree one for structure sheaves; the cited injectivity statement is exact.
- Item step 2: checked against the proof of Tag 0BF3 and the full statement of `lem-sc-picard-h1-multiple-locus`; corrected the family assignment so the product family is the main family and the two projections are the comparison morphisms.
- New node `lem-sc-picard-h1-product-injective`: repaired the statement after review. It now assumes H^0(X,O_X)=k=H^0(Y,O_Y) and rational points x,y, and states injectivity of the slice-pullback map, exactly the map needed by the multiple-locus lemma; it is self-contained and distinct from existing Kunneth nodes.
- New node `lem-sc-picard-h1-multiple-locus`: checked against `lemma-H1-O-multiple-picard-flat-proper`; added the previously omitted morphisms `u_i : X_i → X` and explicitly stated universal structure-sheaf pushforward after every base change.
- Small cases checked: affine factors with vanishing H^1, a field base, the empty-index case, and `n=1`; no counterexample found.
- Changes: repaired the helper's missing morphisms and ambiguous universal-pushforward wording, and corrected step 2's application target; citations remain verbatim and valid.

## Second reading by M1

- Item statement: checked against More on Morphisms, Lemma `pic-of-product`, Tag 0BF3; all flat, proper, finite-presentation, universal-pushforward, section, slice-triviality, and fibre-triviality hypotheses agree.
- Step 1: checked against the statement of `lem-sc-picard-h1-product-injective` and Varieties, Lemma `varieties-lemma-kunneth`, Tag 0BED; the special-fibre sections give the required rational points and the cited map is exactly the slice-pullback map.
- Step 2: checked against the statement of `lem-sc-picard-h1-multiple-locus` and More on Morphisms, Lemma `lemma-H1-O-multiple-picard-flat-proper`, Tag 0BF2; the product family, two comparison morphisms, loci, and injectivity hypothesis match the source proof.
- New node `lem-sc-picard-h1-product-injective`: statement-only and self-contained; definitions are cited, the field and rational-point edge cases are harmless, and Mathlib searches are recorded.
- New node `lem-sc-picard-h1-multiple-locus`: statement-only and self-contained; the universal pushforward condition and comparison morphisms are explicit, and Mathlib searches are recorded.
- Changed both helper `source.place` fields to include the exact Stacks tags required by B5; no mathematical statement or proof step changed.

## Repair after maintainer return

The returned version incorrectly stated injectivity for pullbacks along the two projections, whose direction is opposite to the map used in the proof. I replaced it with the degree-one Kunneth statement for pullbacks along the slices at rational points, adding the necessary hypotheses $H^0(X,O_X)=k=H^0(Y,O_Y)$ and $x\\in X(k),y\\in Y(k)$. In item step 1 I verified these hypotheses on the special fibre from universal pushforward and the sections σ(s),τ(s), and identified the slices with the fibres of $1\\times\\tau$ and $\\sigma\\times1$. I updated `citations.json` to quote the repaired statement verbatim. Step 2 already cites the multiple-locus node with these same slice morphisms, so its C4 issue is resolved.
