# Stage-1 delivery: lem-trf-smooth-separable-hypersurface-slice

Group N1; direct delivery; 2026-10-18.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-separable-hypersurface-slice.json`: existing statement, now split in eight proof steps; no exact Mathlib match. Its statement, statement dependencies, chapter, unit, creation metadata and blueprint ancestry are preserved.
- `citations.json`: a verbatim statement quotation for each of the 41 step/node citations. Full statements are quoted so no formula or qualification is silently elided; the step-by-step review below identifies exactly what each citation supplies.
- `report.md`: this report. `write_split.py` and `searches.jsonl` are sandbox working/search records, not new DAG nodes.

New nodes: **0**. New Mathlib leaves: **0**. Every mathematical input is reused from the current DAG.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, its blueprint tag, hypersurface, slicing and the smooth-slice concepts found no declaration giving this statement. I read `AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap` in `WeilConjectures/AlgebraicGeometry/Morphisms/Slicing.lean:184`: it gives an affine etale scheme mapping through the point, but does not assert a Cartier closed immersion, a hypersurface, or this dimension drop. Thus it cannot attach this item. No master sorry declaration is treated as finished evidence.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Problems found and choices made

The item statement is correct and is unchanged. It is the finite-separable closed-point positive-dimensional case of the smooth slicing argument. I read More on Morphisms Tags 057F (`lemma-slice-smooth-once-separable-residue-field-extension`), 057D (`lemma-slice-smooth-once`), 057C (`lemma-slice-smooth-given-element`), and the positive-dimensional paragraph of 057G (`lemma-slice-smooth`). The finite-separable hypothesis permits the exact-sequence/vanishing proof from 057D/057G, rather than requiring the more general separating-residue cotangent injection used in 057F.

The existing `lem-trf-fibre-regular-element-flat-hypersurface` cites 056Y but its statement deliberately omits the Cartier conclusion. I did not use its proof or its source as though its statement supplied that conclusion (C3/C4). Instead I read and reused the existing generic `lem-pc-recd-fibre-cartier-local`, whose statement gives exactly the Cartier neighbourhood needed. Its source is Divisors Tag 062Y(3), `lemma-fibre-Cartier`. The nonzero-relative-differential smoothness implication is already `lem-zl-hypersurface-nonzero-relative-differential`, so no new 057C-style node or restatement of this item was created.

The inherited unit `sk-i-curve-zero` and current main-20261015 `lem-trf-local-term-locality.proof.md` now use contracting correspondences. This item is an already-recorded historical auxiliary descendant through the relative-completion and immersion-slice chain. I preserve that ancestry and describe its exact positive-dimensional 057G role in `split_report.blueprint`; this delivery changes no unit route, unit record, or current local-term argument. Off-unit statements are used as generic algebraic-geometry tools and are declared in `split_report.tool_uses`.

## Mathlib and duplicate searches

There was no earlier item copy or completed report in this sandbox. I retained and read the six Mathlib search records already in the repository item. I then ran five fresh searches with the required `msearch.py N1 lem-trf-smooth-separable-hypersurface-slice ...` command: one grep, one LeanSearch, one Loogle, and two distinct LeanFinder phrasings. They are recorded exactly in `searches.jsonl` and appended to `mathlib_searches`. Both semantic phrasings returned smooth-chart/relative-dimension APIs; Loogle and grep had no relevant hits. I read the local Mathlib smooth scheme definitions, `RingTheory/Smooth/StandardSmooth.lean`, and `RingTheory/Smooth/Quotient.lean`. Smooth charts and the square-zero-quotient theorem do not give the prescribed hypersurface. No failed service is recorded as a negative result.

I searched the full DAG for 057C/057D/057F, 056Y, relative Cartier and the differential/dimension concepts, and used `tools/blueprint_refs.py ancestor` and `search` for 057F, hypersurface slice, smooth hypersurface, Cartier divisor, and nonzero differential. There is no blueprint node with this full statement. The relevant existing inputs were read and reused instead of creating duplicates.

## Not duplicates

No new nodes. The smooth nonzero-differential implication, fibre Cartier criterion, field differential vanishing, local quotient dimension theorem, and finite-type dimension formula are all citations of existing nodes. No node is created for choosing a nonzero vector, tensor cancellation, killing a finite annihilator, or quotient/localization identifications.

## Review by N1

I reviewed the split against B--E of `coord/delivery-errors.md` with the source statements open. The sources I read for the item are listed above; the supplementary statements were checked in Algebra Tags 00RU, 00RT, 00RV, 090W, 00TT, 00NP, 00FN and 00KW; Morphisms Tags 01UT, 02G1, 01VF and 02FX; Schemes Tag 0HA1; and Divisors Tag 062Y(3). The existing hypersurface lemma's statement and its explicit standard smooth Jacobian proof were read. There are no new nodes needing a separate source, notion definition, or small-case review.

1. **Affine fibre and residue field.** The differential-rank node states precisely that affine opens W,V exist with Omega free of rank d. It does not state that these same opens are standard smooth, and I do not take that from its proof. Smoothness of W follows from open restriction; smoothness over V follows by the displayed lifting-square argument; the affine smooth-ring comparison then supplies the coordinate algebra. The affine fibre-product and open-fibre statements give the actual fibre chart, and the affine-stalk and fibre-stalk quotient statements identify R and its residue field with the stipulated kappa(x). There is no global finite-type or Noetherian hypothesis on X or S.

2. **The nonzero differential space.** I checked that the base-change differential node gives the S'-linear isomorphism, not merely an underlying module map, and that differential localization sends differentials to differentials. The stated fraction and tensor formulas yield E = Omega(R/k) tensor L = L^d. The relative-differential sheaf definition and tilde-stalk localization really identify this with the relative differential fibre at x. Thus nonzero survives all identifications; it is not an unproved comparison theorem.

3. **Choice and lifting of the equation.** The Jacobi--Zariski node states exactness, its explicit delta formula, and surjectivity of the second map. The finite-separable differential node gives Omega(L/k)=0 under the item's actual hypotheses, so delta is onto. Since d>0 I choose a nonzero vector and lift its conormal class to an element of the maximal ideal. The fibre-stalk quotient node explicitly supplies surjectivity of the stalk map. The inverse image of the fibre maximal ideal is the original maximal ideal, so the lift h lies in m_x. No separable-only vanishing claim for a transcendental extension is made.

4. **Fibre regularity and a section on X.** The smooth base-change node applies to the arbitrary ring map B to k, giving C smooth over k. The smooth-over-field local regularity node applies to this C; the regular-local-domain node gives the domain property. A nonzero differential forces hbar nonzero, hence hbar is a nonzerodivisor. The affine-stalk node writes the lifted germ b/t, and the principal-open node makes it a section on an affine U0. The zero-scheme properties node gives precisely a locally principal closed subscheme. I use its affine quotient assertion; I do not use its flat-base-change assertion for the generally nonflat fibre map.

5. **Fibre Cartier near x.** This is an elementary finite-annihilator argument, written out rather than made into a new node. Only C0, a finitely generated algebra over the field k, is made Noetherian using the finite-type-algebra node. The annihilator has finite generators, and their zero localizations at x have denominators killing them, exactly as the affine-stalk statement says. Their product kills the annihilator. The displayed argument also handles elements newly annihilated after localization, so injectivity on the localized ring is proved, not assumed. The quotient fibre formula is written by its two tensor maps; it does not rely on flat base change. The locally-one-nonzerodivisor definition now gives the fibre Cartier property.

6. **Ambient Cartier neighbourhood.** U0 is smooth over S, hence flat and locally finitely presented by the cited smooth-flat node. Z is locally principal by step 4 and fibre Cartier near x by step 5. These are exactly the hypotheses of the quoted 062Y(3) node, which gives an ambient open and a relative effective Cartier divisor there. The relative-Cartier definition includes the absolute Cartier property. There is no use of a dimension-one-only criterion or an unproved consequence of 056Y.

7. **Smoothness and affine shrinking.** The existing hypersurface lemma accepts any smooth ambient scheme and the zero scheme of a section of an invertible module. The trivial module satisfies that definition with basis 1. The nonzero differential is exactly steps 2--3. Its conclusion is smoothness on an open of Z, not necessarily an ambient open, so I explicitly use the closed-subspace topology to lift that open to U0. The principal-open basis theorem and the affine principal-open statement then produce an affine ambient U inside both required neighbourhoods. D is an open restriction of the Cartier cut and an open restriction of the smooth N, so both desired properties hold. This shrinking is not justified by the unsupported assertion that set-theoretic containment factors an arbitrary morphism through a subscheme.

8. **Dimension and the specified point.** I checked the quotient dimension node requires a Noetherian local ring and a nonzerodivisor in its maximal ideal. R is regular local, hence Noetherian, and hbar has both required properties. The local ring of the final fibre cut is identified by explicit fractions with R/(hbar). Both finite-type k-schemes to which the dimension formula is applied are affine charts C0 and C0/(a_s); no quasi-compactness hypothesis is silently applied to all of X_s. Finite algebraicity makes the residue transcendence degree zero, and the quotient has the same residue field L. The open-fibre and dimension-in-open statements identify their local dimensions with those in the original and final fibres. The closed-immersion statement gives uniqueness of the point above x. Every clause of the item is therefore derived, including its particular d-1 conclusion.

I also checked small cases. On affine d-space the cut by one coordinate gives dimension d-1. For d=1 and a nontrivial finite separable closed point of the affine line, the minimal polynomial P is an allowed equation because P' is nonzero at the point; the cut is etale and has dimension zero. In characteristic p, a purely inseparable closed point given by T^p-a has zero differential, which explains why the separability hypothesis must not be dropped. At d=0, E=0 and the choice in step 3 is impossible; the item expressly excludes that case. An empty divisor cannot be returned because the chosen equation vanishes at x. Arbitrary non-Noetherian bases are allowed throughout: Noetherianity was used only for the finite-type fibre algebra and the regular fibre local ring.

B1--B10 raise no new-node shape or Mathlib-leaf issue because none is created; statements and citations are TeX with ordinary single mathematical backslashes after JSON decoding. C1/C4 were checked step by step as above, and verbatim quotations were generated from the statements actually read. There is no induction or circular invocation of the item, no clause moved into a replacement node (D1/D2), and no source assertion used through another node's proof. E1--E6 were checked by following the actual fibre, quotient, residue and openness maps in each step. No statement dispute or source error was found. No proof step exceeds 2000 characters; the longest is the final local dimension computation, and the only inline spreading argument is the elementary finite-annihilator calculation in step 5.

## What could not be finished

Nothing remains mathematically unsplit at this item level. Its cited nodes retain their own current states. No Lean was written, compiled, or built; no live project or launcher file was changed. The server `review_split` check passed before this report was finalized. Full delivery dry-run and push are the remaining delivery operations.
