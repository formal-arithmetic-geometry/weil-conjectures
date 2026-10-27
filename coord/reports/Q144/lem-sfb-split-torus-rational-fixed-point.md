# Stage-1 worker report

Group Q144; item lem-sfb-split-torus-rational-fixed-point; 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-rational-fixed-point.json: statement, now split in six steps; no Mathlib match.
- citations.json: twelve step/node entries, each quoting a verbatim part of the cited statement.
- report.md: this report. searches.jsonl is the search command's authentic log; milne.txt is a sandbox-only text extraction used to read the source.

There are zero new nodes and zero new Mathlib leaves. All substantive prerequisites already have nodes. The item statement, its four statement dependencies, source, creation record, and blueprint ancestry are retained. No unit realization changes are needed: this is a supporting created node, not the unit key statement.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by Borel fixed point, split torus, split solvable and rational fixed point found no declaration stating this item. The source theorem Scheme.exists_hom_of_valuationRing_stalk was read as an extension candidate; it concerns extension of a given generic map, not existence of a torus-fixed point. Its separate DAG node was already present. No Lean was written or compiled.

## WANTED

None. The item source and both scheme-theoretic auxiliary sources are available locally.

## Findings and changes

The statement is faithful to Milne, Algebraic Groups (2017), Theorem 16.51, printed p.343: a split solvable group acting on a complete algebraic scheme with a rational point has a rational fixed point. The multiplicative-group case and product-coordinate series suffice. No statement dispute was found. Complete is proper here, and the hypothesis X(k) nonempty is retained.

The source computes fixedness using geometric points and limits. The split makes the limit construction and its scheme-theoretic identities explicit: extend each coordinate orbit to the affine line across zero; compare two morphisms on a reduced affine source using the dense principal open; evaluate at zero. A second comparison preserves the fixedness acquired for the earlier coordinates. This avoids introducing a fixed-locus representability theorem, or assuming that rational points are dense over a finite field.

Mathlib searches ran via msearch.py, with two semantic phrasings, Loogle, LeanSearch and source grep. The returned fixedPoints, KrullTopology and Galois fixed-field declarations do not assert the algebraic-geometric existence result. The item retains its inherited searches and adds the searches actually run by Q144. All actual results were read.

The whole DAG statements were searched by concept and tag, including 0BX7 and the density/valuative keywords. blueprint_refs.py searches for fixed point, split torus, torus, rational map, proper curve and extend across found no duplicate blueprint statement. The existing rational-map-extension-valuation-point node gives exactly the required open extension, including the whole original open; the existing relative-separated-dominant-ext node gives relative separated uniqueness on a reduced source. The older Nagata and Chow density nodes were read, but no additional copy was needed. No new statement-only node is created for the elementary Laurent localization or finite-coordinate assembly.

## Not duplicates

No new nodes; no new/existing-node pairs to distinguish.

## Review by Q144

I read Milne Theorem 16.51 with its proof, printed p.343, in the local PDF text extraction, and the current latest blueprint unit and direct-images proof. This is the field fixed-point prerequisite in the existing long supporting chain; it replaces no unit-level step. The ancestry tool returns None for the inherited created chain, so its null from.node and via list are preserved, while the precise recorded from.place remains filled.

In step 1, def-sc-group-scheme supplies the associativity and unit diagrams. Pulling the given action along the chosen product isomorphism gives the commuting coordinate actions. The inductive assertion is stated as equality of orbit morphisms on H_i, which is stronger than fixing only k-points and exactly what step 5 needs.

In step 2, I read the complete statements of def-weil-affine-spectrum, lem-weil-pbc-polynomial-ring-domain and lem-weil-pbc-finite-type-over-noetherian. The first supplies the ring-map/scheme-map correspondence and the rational origin; the second applies to k[t] and later finite-variable polynomial rings over the field k; the third applies to the affine line, which has one finite algebra generator and a finite affine cover over Spec k. The base is Noetherian because the field has only two ideals. The valuation-stalk check is written out: a nonzero rational function has an integral t-order; after removing the lowest t-powers its remaining numerator and denominator have nonzero constant terms. Thus either the function or its inverse belongs to k[t]_(t). I marked this step non-elementary because it also invokes the two cited structural results.

In step 3, I read lem-sfb-rational-map-extension-valuation-point and its Stacks source morphisms.tex Tag 0BX7 (lemma-extend-across), including its hypotheses and proof. Its source can be any integral Noetherian scheme and its target any proper scheme over the base; it imposes no reducedness on the target. Here the dense open is D(t), the valuation point is (t), and all its hypotheses were checked in step 2. Its conclusion explicitly contains the entire original open and the valuation point. Since their union is the entire affine line, its extension is defined everywhere. Its value at the k-rational origin is a k-rational point.

For steps 4 and 5, I read lem-sfb-relative-separated-dominant-ext and the exact Mathlib theorem AlgebraicGeometry.ext_of_isDominant_of_isSeparated, Morphisms/Separated.lean:295-298; Stacks schemes.tex Tag 01KM and morphisms.tex Tag 01RH explain the corresponding closed-equalizer argument. I also read def-weil-proper-morphism, which explicitly includes separatedness. Each comparison is between morphisms over Spec k to the given separated target, with a reduced source. The source coordinate ring is a localization of a polynomial domain, and the principal open t != 0 contains its generic zero prime. No density assertion about k-points is used. Step 4 spells out the equivariance identity on the open and its restriction at zero. Step 5 spells out the commutation identity using the preceding inductive hypothesis on H_i. These two independently checked equalities give both the new coordinate fixedness and retention of all earlier fixedness.

Step 6 uses only the product multiplication isomorphism and the associativity identity from def-sc-group-scheme: if h and c fix z, then hc fixes z. Induction ends at H_r=T. The final equality is a morphism identity, so evaluating it on every commutative k-algebra gives every clause of the required conclusion, including nonreduced algebras.

I checked small cases: rank zero retains the original point; rank one is the direct orbit-limit proof; the diagonal action on the projective line sends a nonzero finite coordinate to its rational zero at t=0; finite k needs no additional argument since density concerns scheme points; a trivial action on a nonreduced proper scheme retains its given point. An empty scheme is excluded by X(k) nonempty. The argument never assumes X integral, reduced, geometrically irreducible, smooth, or k perfect. Properness is needed for the extension (translation on G_m itself would fail this step). All hypotheses are in force precisely where each cited theorem is applied.

I checked delivery-errors B through E against the node and these sources: all cited mathematical facts have existing statement nodes; every proof use has a verbatim citation; no proof of a cited node is used as an extra output; there are no new nodes restating a clause; no cycles can arise through the extension node, whose dependencies were inspected and do not include this item; and no prohibited source is cited. Every step is below 2000 characters (largest: 854), and none conceals a separate standard comparison. No corrections to the statement were necessary.

## Unfinished work

None in the stage-1 split. Delivery awaits the required server dry run and push; their outcome will be recorded below.

## Validation

The first dry run requested a longer quote for the finite-type-over-Noetherian citation. I replaced the short conclusion excerpt with the entire statement, so its hypotheses and conclusion are visible together. No proof change was required.
