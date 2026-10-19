1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-open-relative-normalization-gluing.json` (new statement node; no Mathlib match).
- `dag/nodes/sec-trace-formula/lem-trf-integral-surjective-open-extension.json` (repaired item; no Mathlib match).
- `citations.json` (verbatim statement excerpts for every cited node in every item step).

2. Attachments: none. Searches of the read-only slopmaster2 and master source trees by the item id, Tag 0CNX, normalization names, and open-extension vocabulary found no sorry-free project declaration stating the item or the chart-gluing statement.

3. WANTED: none. The local Stacks sources contain Tags 0CNX, 035F, 035H and 035K.

4. What was wrong and what I repaired:

The returned version made Step 1 depend on a statement-only node whose conclusion already asserted the whole arbitrary-open envelope. It also presented that conclusion as if it followed from the quasi-compact/quasi-separated relative-normalization definition. That is not a valid inference when the open immersion is arbitrary. I narrowed `lem-trf-open-relative-normalization-gluing` to the genuinely auxiliary chart assertion: on affine charts of the open, integral-closure rings are canonically identified after localization, satisfy the cocycle condition, and glue compatibly. The node cites the authoritative proof of Stacks Lemma 0CNX (more-morphisms.tex, lines 13686–13704) together with Morphisms 035F/035K.

Step 1 now writes the missing construction explicitly. It chooses affine charts of the ambient scheme and of their intersections with the open, forms the integral-closure charts, uses the cited localization statement on every overlap, checks the cocycle condition, and performs the two ordinary scheme-gluing operations. The resulting map is integral by the affine definition and its restriction is the given map. The step explicitly records that the composite V→U→S is never fed into the 035H normalization definition. Stacks Lemma 0CNX is cited as the authoritative source for this arbitrary-open gluing construction; the auxiliary node no longer restates the target extension theorem.

Steps 2–4 were reread against Tag 0CNX and their cited node statements. The reduced complement, coproduct, surjectivity, and fibre-product restriction remain as in the returned version.

5. What I could not finish: no unresolved proof or search issue remains in this repaired stage-1 split.

## Review by Q76

I reread the returned entry, `coord/returns/Q76.md`, Stacks `more-morphisms.tex` at Tag 0CNX (lemma and proof, lines 13686–13704), and `morphisms.tex` at 035F (integral-closure charts), 035H (the relative-normalization definition), and 035K (normalization localization). I also opened every node cited by all four item steps and checked the item against the chapter/unit metadata.

For Step 1, the new node now says only what the step takes from it: localization-compatible affine integral-closure charts and their cocycle/gluing compatibility. The item step separately supplies the global construction and identifies the resulting restriction with V. The localization node says verbatim that localization of an integral closure is the integral closure after localization, which is exactly the overlap calculation used. The source check was the point of the repair: 035H is used only on each legitimate affine chart; the arbitrary composite V→S is not assumed quasi-compact or quasi-separated. The published Tag 0CNX lemma is the authoritative source for the resulting arbitrary-open gluing.

For Step 2, I checked that the reduced-induced-subscheme node supplies a reduced closed subscheme supported on S\\U and that the quotient affine maps are integral by the cited definition. For Step 3, I checked the coproduct universal property and open-and-closed summands, then verified coordinatewise integrality and coverage of S using the stated definition of surjectivity. For Step 4, I checked the fibre-product universal property and the empty restriction of the complement summand; the coproduct base-change identification gives exactly V over U.

I tested empty-open, empty-base, and full-open cases. Mathlib searches for the item and the new chart node were run with LeanFinder, LeanSearch, Loogle, and grep; the normalization APIs found all require quasi-compact/quasi-separated hypotheses, so no Mathlib leaf was claimed. The return's unsupported full-gluing node was repaired by narrowing its statement and moving the actual gluing argument into Step 1 with the direct Stacks 0CNX citation.

## Not duplicates

lem-trf-open-relative-normalization-gluing vs lem-trf-integral-surjective-open-extension: the new node states only localization-compatible affine chart gluing; it does not assert surjectivity or the reduced-complement coproduct, which are conclusions of the item.
lem-trf-open-relative-normalization-gluing vs lem-weil-pbc-relative-normalization: the existing Mathlib leaf assumes a quasi-compact, quasi-separated input morphism; the new node records the chart-localization mechanism used for an arbitrary open immersion.
lem-trf-open-relative-normalization-gluing vs lem-weil-pbc-normalization-in-residue-field-extension: that node concerns normalization in a finite residue-field extension and an affine chart, whereas this node concerns overlaps of charts over an arbitrary open.
lem-trf-open-relative-normalization-gluing vs lem-weil-pbc-universally-closed-global-sections-integral: that node proves integrality of global sections under universal closedness and qcqs hypotheses; this node is the localization/cocycle chart fact and has neither hypothesis.
lem-trf-open-relative-normalization-gluing vs lem-sbc-dvr-galois-components-stalk-factor: the existing node is a localized DVR/Galois stalk statement; this node has no DVR, Galois, or stalk hypotheses.
lem-trf-open-relative-normalization-gluing vs lem-sbc-normalization-algclosed-field: the existing node factors points through a normalization over an algebraically closed field; this node concerns arbitrary-open affine chart overlaps.
lem-trf-open-relative-normalization-gluing vs lem-sbc-reduced-artinian-affine-normalization-charts: the existing node is restricted to reduced Artinian charts; this node has no Artinian or reduced assumption.
lem-trf-open-relative-normalization-gluing vs lem-sbc-reduced-artinian-tensor-normalization-charts: the existing node is a reduced Artinian tensor-product calculation; this node is the general overlap-localization calculation.
lem-trf-open-relative-normalization-gluing vs lem-weil-pbc-reduced-algebraic-normalization-field-change: the existing node assumes a reduced finite-type scheme over a field and proves finite normalization, normal locus, and separable field-change; the new node has an arbitrary base scheme and integral map over an arbitrary open and states only overlap-localization and cocycle gluing.
lem-trf-open-relative-normalization-gluing vs lem-sbc-stalk-normalization-normal-dense: the existing node assumes an integral Noetherian normal base, a smooth morphism, and a finite etale cover and concludes normality and density of a specific pulled-back normalization; the new node has no Noetherian, normal, smooth, or etale hypotheses and concerns the general affine chart gluing needed for an arbitrary-open extension.
