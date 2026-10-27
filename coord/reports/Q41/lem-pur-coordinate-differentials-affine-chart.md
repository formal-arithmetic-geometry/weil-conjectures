# Q41: lem-pur-coordinate-differentials-affine-chart

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-coordinate-differentials-affine-chart.json: statement; split into six steps using existing nodes. The statement and its statement dependencies are unchanged. The item is not itself a Mathlib leaf.
- citations.json: verbatim statement excerpts for every step/node citation.
- report.md: this report. searches.jsonl records five additional searches actually run for the item.

New nodes: 0. New Mathlib leaves: 0. All necessary lemmas already exist.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, coordinate/differential terminology, standard smooth charts and graph presentations. No project declaration states the entire item. DifferentialCoordinatesCotangentIndependent and the standard-smooth presentation results concern ring-theoretic ingredients, not this scheme chart, its canonical cotangent-fibre comparison and the graph algebra. The upstream differential sheaf exists but is only an ingredient, not an attachment of this item.

## WANTED

None. All sources needed here are present in literature/stacks-project/.

## Problems found and changes

The imported item had no proof. Its statement is correct; no STATEMENT-DISPUTED correction is needed. The current blueprint ancestor is literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-regular-immersion-linearization.proof.md, second paragraph: the differential coordinate map is etale. This split supplies its affine algebra preparation, retaining the route through standard smooth coordinates and the prescribed graph equations. It does not replace the coordinate map by an unrelated etale map supplied by a different chart.

Mathlib was searched with leanfinder twice, loogle, grep and leansearch, exactly as recorded in searches.jsonl. The hits give chart existence, standard smoothness criteria, or polynomial differential bases, rather than the complete item. I read Smooth.exists_isStandardSmooth in Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:99 and IsStandardSmooth.of_basis_kaehlerDifferential / iff_exists_basis_kaehlerDifferential in RingTheory/Smooth/StandardSmoothOfFree.lean:50,82. I retained the original search history in the item and appended only the searches run in this session. Some semantic hits use the newer name IsSmooth; the source here has Smooth. This name discrepancy does not establish an attachment or complete Mathlib match.

## Not duplicates

No new nodes were created. Searches of the whole DAG found lem-weil-pbc-smooth-locally-standard-smooth, lem-weil-pbc-standard-smooth-kahler-basis, lem-weil-pbc-spec-tilde-stalk-localization and lem-sfb-commutative-ring-invariant-basis-number, which are reused. Blueprint searches for standard smooth, differential, graph presentation and cotangent fibre found no equivalent blueprint statement of the whole item. I also read lem-trf-affine-chart-stalk-differentials: its existentially chosen affine chart is not asserted to be the particular standard smooth chart needed here, so it is not used to identify those charts.

## Review by Q41

I read delivery-errors.md sections B through E, the chapter and unit records, GOAL.md, the three-level restrictions in SETUP.md and the latest blueprint ancestor. I checked the item against Stacks morphisms.tex Tag 01V7 (lemma-smooth-locally-standard-smooth), algebra.tex Definition 00T6 and Lemma 00T7 (definition-standard-smooth, lemma-standard-smooth), morphisms.tex Tags 01US and 01UT (lemma-differentials-restrict-open, lemma-differentials-affine), schemes.tex Tag 01HV (lemma-spec-sheaves), and Tag 01I2 (lemma-category-affine-schemes). I read 02GU (lemma-etale-at-point), especially condition (8), to check the graph presentation's purpose. That tag is motivation for the chosen square presentation; it is not cited as a black box proving the graph calculation.

Step 1 uses the statement of lem-weil-pbc-smooth-locally-standard-smooth for a chart at the given point, and the actual presentation data in def-weil-pbc-standard-smooth-algebra. The smoothness hypothesis is exactly the item's; the target neighbourhood is the whole one-point Spec k. The generic chart theorem belongs to sk-thm-p1 and is declared as a tool use in split_report.tool_uses: it supplies local algebra geometry, without replacing the purity route. No pure relative dimension is assumed in this step.

Step 2 uses lem-weil-pbc-affine-open-stalk-localization for the ring isomorphism induced by germs, def-sc-relative-differential-sheaf for its explicitly stated affine restriction with compatible universal derivations, and lem-weil-pbc-spec-tilde-stalk-localization for the associated module's stalk and the formula omega maps to omega/1. I read all three statements. In particular the definition cited really specifies the affine restriction, rather than merely naming the differential sheaf. Taking the residue quotient of the ring isomorphism gives the required field identification, with no closed-point or rational-point assumption.

Step 3 proves the tensor comparison rather than citing an unsupported transport: the inverse sends (omega/s) tensor lambda to omega tensor (lambda/sbar). Equality of fractions, balancing and the two inverse identities are written out. Only tensor base change, as defined in def-weil-module-base-change, is additionally used; the localization description is Step 2. Every denominator outside q has nonzero image in K. This is an elementary calculation from those descriptions, not a new lemma node.

Step 4 uses precisely the free basis of the *remaining variables* supplied by lem-weil-pbc-standard-smooth-kahler-basis. Scalar extension of the basis is checked with its coordinate maps and finite-sum reconstruction. The existing invariant-basis-number node applies over the nontrivial residue field K and says that an equivalence K^(n-r) with K^d implies n-r=d. It needs neither a rational point nor perfection of k. This avoids assuming the desired dimension equality while choosing the chart.

Step 5 constructs both graph quotient maps explicitly. Surjectivity of the given polynomial quotient supplies H_j. The polynomial universal property is actually included in def-weil-pbc-mv-polynomial-ring. The reverse map is R-linear because H_j(y)=T_j in the graph quotient; its two composites fix all algebra generators. Hence neither a kernel-comparison theorem nor a hidden graph-isomorphism lemma is used. This is a direct quotient calculation, not a restatement of the desired clause as a new node.

Step 6 uses lem-weil-pbc-spec-map-global-sections for the coordinate pullbacks, the polynomial universal property for equality of ring maps, and the fully faithful affine spectrum description in def-weil-affine-spectrum for equality of scheme morphisms. I read their statements and checked that they assert these exact facts. The original prescribed functions remain the pullbacks throughout.

Every uses entry has a verbatim excerpt in citations.json, checked against the corresponding live node statement. All proof dependencies are the union of those entries; no citation points to a node created from this item or to an ancestor needing it. All steps are shorter than 2000 characters. There are no unsplit new nodes, new notions, duplicate tags, hidden source arguments or fabricated searches to audit under B/D. During source checking I corrected a draft tag for lemma-differentials-restrict-open to 01US using tags/tags.

I tested d=0 (empty prescribed family, zero cotangent fibre, n=r and R=k), r=0 (polynomial chart and its full coordinate differential basis), n=r=0 (A=k), and nonclosed points with arbitrary residue fields. The tensor inverse and graph maps still work with empty sums and empty families. A=0 cannot arise because W contains u. Over an imperfect field the argument still works because only the stated smoothness and the given residue-field basis are used. No finite coefficient, SGA trace, or purity theorem is invoked in this local algebra preparation.

## Unfinished work

None for this one-level split. Existing cited unsplit dependencies remain the responsibility of their own DAG items.
