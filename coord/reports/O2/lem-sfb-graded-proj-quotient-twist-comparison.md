# Stage-1 delivery: lem-sfb-graded-proj-quotient-twist-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-proj-quotient-twist-comparison.json`: statement, split into eight proof steps. Statement and statement dependencies unchanged. No exact Mathlib match.
- `citations.json`: one verbatim statement excerpt for each of the 21 step/node citations.
- `report.md`: this report. `searches.jsonl` records the actual msearch calls. `write_split.py` is the sandbox preparation script.

New nodes: 0. New Mathlib leaves: 0. All proof dependencies already exist. No repository, launcher, Lean, unit, or chapter file was written; no git or compiler was invoked directly.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id and for graded quotient/Proj/twisting-sheaf notions. Read the ProjectiveSpectrum/Twist re-export and searched its component files. The existing declarations construct twists, their degree-one frames, multiplication, and sections, but do not state the whole quotient pullback comparison. No attachment is claimed.

## Literature and searches

Read the item against `literature/stacks-project/constructions.tex`, Tag 01MY (`lemma-morphism-proj`), including both characterizing properties and the local formula for the graded algebra map; Tag 01N0 (`lemma-surjective-graded-rings-map-proj`); Tag 01N1 (`lemma-surjective-graded-rings-generated-degree-1-map-proj`); and Tags 01MS/01MT (`lemma-when-invertible`, `lemma-apply-modules`). Also read `sheaves.tex`, Tag 04TN (`lemma-glue-maps`), and `schemes.tex`, Tags 01I7 and 01IA, for the affine sheaf realization of the explicit module maps. There are no new-node sources to check.

Read the chapter and unit records, the current blueprint direct-image statement, and the inherited ancestry place: this is a lower prerequisite for the standard-Proj section-finiteness reduction, not a replacement for the direct-image/alteration route. `blueprint_refs.py ancestor` reports the inherited ancestor as None; its `from` record is retained. Whole-blueprint searches for `twisting sheaf`, `graded rings`, `01N1` and the broader `twist`/`Proj` searches did not find the whole statement. DAG searches included the tags, graded quotient, twist, localizations, and module gluing. In particular the existing `lem-sfb-standard-proj-twist-tensor` is reused for the actual multiplication formula; the relative-Proj functoriality node alone was not taken to assert a twist comparison or any chart formula.

Retained the item's earlier Mathlib search records and read their recorded hits. Ran and recorded fresh leanfinder, loogle, grep and leansearch calls under this item, including a second semantic phrasing and a broader grep. Read Mathlib `AlgebraicGeometry/ProjectiveSpectrum/Functor.lean` around lines 145–215: `Proj.map_preimage_basicOpen`, `awayToSection_comp_appLE` and `awayι_comp_map` supply the underlying map/chart formulas, but no twists or their graded compatibility. `Proj.pullbackAwayιIso` identifies an intersection of opens, not the pullback of O(n). The grep of Mathlib AlgebraicGeometry for twisting sheaves/graded modules returned no hits. The full item is therefore not a Mathlib leaf. No unrun query was added to the record.

WANTED: none.

## What changed or was wrong

The original node had no proof. Its statement is correct and is preserved, including negative twists, arbitrary positive-degree charts, homogeneous-section and multiplication compatibility, zero rings and empty opens. The source's degree-one generation hypothesis is genuinely needed: 01N0 gives the weighted example A=k[x,y], deg(x)=1, deg(y)=2, B=A/(x), in which an arbitrary quotient need not identify twists. This delivery does not drop that hypothesis or restrict the conclusion to nonnegative twists. No statement dispute or departure from the unit route was found.

## Review by O2

I checked the statement clause by clause against 01MY and 01N1, and used 01MS/01MT to justify the degree-one chart argument. The induced map is built in the proof, not inferred with extra properties from an existence-only citation. For each cited node I opened its statement and checked the actual hypotheses and conclusion; the citations file quotes the text, not an imported proof.

Step 1 uses `prop-nagata-proj-standard-open` only for its ideal-generation covering criterion. The degreewise lifting is proved by homogeneous projection, and the assertion about the irrelevant ideal is proved from positive-length monomials. Thus both covers follow even with infinitely many degree-one generators and with a noninjective degree-zero map.

Step 2 uses `def-nagata-homogeneous-localization-degree-zero` for the equal-degree fraction convention. The localization equality relation, its preservation under psi, and surjectivity by homogeneous numerator lifting are written out. This is an elementary calculation, not a new localization lemma.

Step 3 uses `def-pc-proj` for its affine standard opens and localization restrictions, `def-weil-affine-spectrum` for the contravariant spectrum maps, `lem-weil-pbc-proj-basic-open-intersection` for precisely D(g^d/f^e), `lemma-nagata-proj-chart-ring-cocycle` for the transition identifications, and `lem-weil-pbc-scheme-morphism-gluing` for existence and uniqueness of the glued map. These statements do give the facts used. `prop-nagata-relative-proj-functoriality` identifies the existing graded-quotient induced morphism; its statement is not used as a citation for the fraction formula. The inverse-image equality is checked on every source chart with the principal-open formula. This handles f and g of different positive degrees without assuming either has degree one.

Step 4 uses the twisting definition for the degree-n chart module and localization restrictions, `lem-weil-pbc-proj-graded-module-sheaf-exists` clause (c) for quasi-coherence of A(n) and B(n), and `lem-weil-pbc-affine-tilde-gamma-adjunction` for the functorial equivalence with modules on each affine. Multiplication by f^n has the explicit inverse multiplication by f^(-n). Thus the proof really gives a sheaf frame, rather than claiming freeness of a sheaf from global generators alone.

Step 5 applies `lem-weil-pbc-module-pullback-affine-sections` with the affine pair U_f,V_f and the quasi-coherent input established in Step 4. Its specified pure-tensor formula is exactly what identifies the pullback of the frame. `lem-weil-pbc-module-pullback-quasi-coherent` gives the further hypothesis needed to apply the affine equivalence to the source of the comparison. The target is quasi-coherent by Step 4. The tensor map is balanced, and the inverse v -> f^n tensor (v psi(f)^(-n)) has its coefficient in degree zero. No injectivity of psi is used.

Step 6 uses the restriction maps in the twisting definition and clause (1) of `lem-weil-pbc-glue-sheaves-of-modules`, which explicitly glues compatible module morphisms and detects their equality on the cover. The integer-power transition calculation is written out: f/g is a unit on the overlap, and its image under the chart map is psi(f)/psi(g). This proves compatibility for negative n too. I glue inverses separately and use uniqueness for both composites, rather than appealing to an unquoted local-isomorphism theorem.

Step 7 uses the already existing `lem-sfb-standard-proj-twist-tensor`, whose statement supplies the exact canonical multiplication formula. Both its covering hypotheses were verified in Step 1. The tensor and pullback definitions give the displayed pure-tensor identifications. Equality on the single free tensor frame gives equality on each whole chart, and the module-morphism gluing node gives global equality. The unit is explicitly the degree-zero frame 1. No new node merely restates the multiplication clause.

Step 8 uses clause (3) of the twisting definition: the canonical section is characterized by s/1 on each chart. Its degree-zero coefficient s/f^d is sent by the already proved chart map to psi(s)/psi(f)^d; multiplying by the compared degree-d frame gives psi(s)/1. The sheaf uniqueness axiom gives the global conclusion.

I checked B1–B10: no new nodes, no copied proof sketch disguised as a statement, all notions are inherited with their definition dependencies, TeX is singly escaped in the decoded strings, sources use verified Stacks tags, existing Lean is not mistaken for an attachment, and searches are actual logged calls. I checked C1–C8: every non-elementary tool has an existing node with the right statement; generic off-unit tools are declared in `split_report.tool_uses`, and no node is cited for a stronger conclusion than its statement. D1–D5 are addressed by the written chart, inverse, overlap and compatibility calculations, with no restatement children. For E1–E7 I checked degreewise surjectivity, all ring-map directions, the two tensor coefficient rings, arbitrary integer degrees, and the compatibility calculation itself.

Small cases: n=0 is the structural unit, n=-1 uses the inverse of f, and the identity quotient gives identity frames. For A=A_0 concentrated in degree zero the Proj schemes are empty; for B=0 all source charts are empty. For A=k[x], B=A/(x) the image denominator is zero and the tensor coefficient ring is zero, so the displayed inverse maps still apply. For a nilpotent degree-one f both corresponding opens are empty. No cancellation by a nonunit or assumption 1 != 0 occurs. All eight proof steps are shorter than 2000 characters; none contains a hidden comparison lemma beyond its explicitly cited affine/gluing tools.

## Not duplicates

No new nodes were created. The existing standard-Proj multiplication node and existing affine/gluing tools are cited directly.

## Unfinished work

None within this one-level split. Existing dependency nodes retain their own states and are not edited or split here. Delivery validation follows through the prescribed server dry run.
