# Stage-1 report: lem-coef-dg-module-cone-triangulation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-module-cone-triangulation.json`: statement, now split into eight proof steps. Statement unchanged. Fresh Mathlib searches find ordinary homotopy categories, not this dg-module category.
- `dag/nodes/sec-six-functors/lem-coef-dg-abc-homotopy-category-triangulated.json`: one new statement-only node, unsplit; no exact Mathlib match. It states the abstract dg-category ABC criterion, including its admissible-sequence definition and cone-triangle characterization.
- `citations.json`: one verbatim statement quotation for every citation of every item step. The full criterion is quoted where its separate axioms or conclusion are used, and the full definition is quoted for the several different triangulated axioms used.

One new node; zero Mathlib leaves. No unit record changed: this is auxiliary infrastructure, not the unit's key statement.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, dg-module/dg-category terminology, module cones and triangulation, and inspected the homotopy-category hits. There is no project declaration stating this item or the new ABC criterion. The master source was searched as reference material only, not treated as a finished proof.

## WANTED

None. All sources used for the split and the new node are in `literature/stacks-project/dga.tex`. No SGA source is used.

## Problems found and corrected

The item itself is mathematically correct. Its statement and hypotheses are retained. It had no proof or direct Lean audit entry. Its pre-existing searches were preserved and supplemented by searches actually run for Q73 with `msearch.py`.

It is not sufficient to apply 09QY directly to the label set: the supplied isomorphisms to shifted labelled modules need not make shifts a strict action on labels. Steps 1 and 3 use formal shift labels `(s,n)` to meet axiom (B), and steps 6--7 explicitly recover the original category and its axioms. The final arrow is `-p` by 09QU; the boundary in the admissible cone sequence itself is `f[1]`. Conflating these two signs would produce the wrong triangle convention.

During self-review I corrected an initially mistyped source tag: `lemma-get-triangle` is 09P6, not 09QI (09QI is a different product lemma). I also expanded the reverse cone characterization in step 6: conjugating by the strict isomorphisms to original labels gives an actual diagonal cone isomorphism, so no unstated theorem about completing an arbitrary homotopy equivalence of endpoints is being used.

The current unit record is `sk-prop-sf-biduality-general`; the item's established ancestry goes through the generic dg-quotient infrastructure to paragraph 2 of `prop-coef-integral-exceptional-adjoint`. I read that paragraph in the current main-20261015 blueprint and retained that ancestry and unit binding. Nothing here replaces a geometric step of the unit or changes its route.

## Unfinished work

The single new ABC criterion is deliberately unsplit, with complete hypotheses and only a statement. A future worker can split the proof of Stacks 09QY (TR1--TR3, the admissible-monomorphism octahedron and its reduction) and the two directions of 09QU. This split leaves no omitted assertion in the item's module specialization. No Lean was written or compiled.

## Not duplicates

lem-coef-dg-abc-homotopy-category-triangulated vs lem-coef-dg-module-cone-triangulation: the new node is Stacks' theorem for an arbitrary dg category with strict shifts, enriched Hom shift identifications, and graded-split admissible sequences. It has no module category, no labels with closure up to strict module isomorphism, and no conclusion about independence of module representatives. The item supplies these hypotheses through the explicit full dg category on formal shift labels, constructs its cones and boundary, and transfers all four axioms and choices back. This is a generic theorem used after substantial construction and hypothesis verification, not a new lemma asserting the item's conclusion under its own hypotheses.

lem-coef-dg-abc-homotopy-category-triangulated vs lem-coef-dg-finite-twisted-extension: the latter constructs finite one-sided twisted complexes, proves invariance under quasi-equivalences and their functorial extension, and already cites this item for its triangulation. It is not an abstract ABC theorem and citing it here would be circular. Its source mentions 09QY and 09QU in proof steps, which is why the tag search finds it.

lem-coef-dg-abc-homotopy-category-triangulated vs lem-pur-homotopy-category-triangulated: the existing Mathlib leaf concerns ordinary complexes in a fixed abelian category (and their derived localization). A right module over a dg category with nonzero differential is not such an ordinary complex of modules with degree-zero differential in a fixed ordinary module category. The abstract ABC hypothesis verification is needed; this is not a one-line specialization of that leaf.

Whole-DAG searches used 09QY, 09QU, ABC, admissible short exact, dg categories, module cones and triangulated homotopy categories. Whole-blueprint searches with `tools/blueprint_refs.py search` used 09QY, dg category, differential graded, admissible short exact, and homotopy category. No blueprint node states the new criterion, so both `same_as` fields are empty. The new node uses the exact ancestor printed by `blueprint_refs.py ancestor` and prepends this item to the inherited `via` list.

## Review by Q73

I read the item against Stacks `dga.tex` section-review, including the full axioms (A)/(B), Situation 09QJ, the boundary construction in 09P6, both statements and the proof of 09QU, and Proposition 09QY with its proof and the admissible-monomorphism octahedron immediately preceding it. I verified all four tag-to-label mappings in `literature/stacks-project/tags/tags`. The new node is exactly this abstract criterion over the special base ring Z, with the notion of an admissible sequence and its boundary written out so that no tag is needed to interpret its statement.

For step 1 I opened `lem-coef-dgcat-formal-cone-enlargement` and read its actual statement: it defines right actions with the Leibniz rule, unsigned graded right-module maps and their commutator differential. Those are exactly the notions used. The step verifies the Hom differential, dg composition and the full embedding on formal shift labels explicitly. It uses no derived Yoneda statement, projective resolution, or model-category conclusion from that node. Smallness is the set S times Z, with Hom groups in the permitted enlarged universe.

For steps 2--4 I read the new criterion's entire statement alongside the source. Step 2 establishes its closed biproduct maps by conjugation through strict degree-zero isomorphisms; an H0 isomorphism would not suffice here and is not used. Step 3 verifies the right action after shifts, the homogeneous-map factor (-1)^(kr), strict addition of formal shifts, and the target-shift isomorphism of complexes. The displayed differential equality is the required compatibility. Negative shifts obey the same parity identities and give the inverse. Step 4 conjugates a closed map between shifted modules to a map between original labels before invoking the cone hypothesis, so the hypothesis is applied within its actual scope. The diagonal cone isomorphism is checked against the off-diagonal differential. The coordinate graded splitting has pi*partial(s)=f, which represents f[1] in the target shift convention, establishing exactly axiom (C).

For step 5 the criterion's conclusion supplies the triangulated category and the isomorphism-class characterization of cone triangles, including the negative projection. This is the one non-elementary generic triangulation theorem needed. The new criterion is not being justified by the proof of the item, and none of its dependencies leads back to the item. I opened `lem-coef-dgcat-model-structure` for the new statement dependency; its statement explicitly defines small cochain dg categories and H0. Its model-structure theorem is not invoked by this split.

For steps 6--7 I opened `def-weil-triangulated-category` and checked each triangle equation and TR1--TR4 against its actual text. These steps use the new criterion's triangulation and cone characterization from step 5 plus that definition, with an explicit quasi-inverse and Hom bijections. The reverse characterization is handled by the actual strict diagonal cone map after conjugation to original labels; it does not silently assume a cone is functorial on homotopy classes. Rotation uses the same natural shift comparison as the definition of image triangles. The TR3 completion and TR4 octahedron are obtained in H0 D using the criterion, and all the needed arrows, equations and remaining distinguished triangle reflect to H0 C by the stated Hom bijections and definition. I marked these combined categorical arguments non-elementary, rather than labelling the entire transport of a triangulation as a one-line observation.

For step 8 the same definition supplies what it means for the comparison to be an exact equivalence. I checked the actual comparison formulas for shifts and cones, the last-arrow square (the two minus signs cancel), and cancellation for iterates; these prove choice independence without an uncited general transport theorem.

I tested the statements and constructions on S representing only the zero module (the empty S cannot satisfy the zero hypothesis), duplicate labels for one module, the zero map (the block diagonal cone), the identity map, negative integer shifts, and a dg base with nonzero differential (the shifted Leibniz calculation retains the d(a) term). No boundedness, cofibrancy, abelian-category hypothesis or quasi-isomorphism closure has been smuggled in. Only the strict module isomorphisms assumed by the item are used. For the abstract criterion the zero category satisfies all hypotheses; a category lacking cones fails (C), rather than contradicting the conclusion. The new statement is not claiming that an arbitrary additive category of graded objects is triangulated.

Against delivery-errors B--E: the new node is statement-only and introduces all objects and notions, its source has checked Stacks tags and TeX labels, the searches are the actual logged Q73 queries with their hits, and the Mathlib candidates were read at `HomotopyCategory/Triangulated.lean:191-211` and `Pretriangulated.lean:574-586`. These are ordinary complexes, not the module-action or abstract ABC assertion. There is no duplicate, circular dependency, new node equal to a module-closure clause, or proof hidden inside the new statement. Steps carry the module and representative calculations; the only newly isolated input is the independently stated general source theorem. Every cited statement was opened and is quoted verbatim in `citations.json`. No off-unit non-Mathlib proof tool is used: the module convention and new criterion have the item's unit, and the triangulated-category definition is a Mathlib leaf.


## Second reading by Q73

- Item statement: checked every hypothesis and conclusion against Stacks `dga.tex`, Tags 09QJ, 09P6, 09QY and 09QU; verdict: agrees, including the zero/sum/shift/cone closures and the negative final arrow.
- Step 1: checked against `lem-coef-dgcat-formal-cone-enlargement` and the dg-category definitions in `dga.tex`; verdict: the Hom differential, composition, formal shift-label enlargement, and full-faithfulness argument are stated explicitly and use only the cited module-map interface.
- Step 2: checked against the ABC axiom (A) and the closure hypotheses; verdict: strict zero and binary dg direct sums are constructed by conjugating coordinate maps, so the step is elementary.
- Step 3: checked against ABC axiom (B), the shifted-module definition, and the graded-map sign convention; verdict: the shift action, Hom-complex identification, differential sign, composition compatibility, and inverse shifts are explicit and correct.
- Step 4: checked against ABC axiom (C), `lemma-get-triangle` (09P6), and the cone differential; verdict: conjugation, cone closure, graded splitting, boundary `f[1]`, and the sign convention are all supplied.
- Step 5: checked against Proposition 09QY and Lemma 09QU; verdict: the cited abstract criterion supplies triangulation and the precise cone-triangle characterization, including `-p`.
- Step 6: checked against the actual Hom complexes, strict representative isomorphisms, and `def-weil-triangulated-category`; verdict: the equivalence from formal shift labels back to original labels, lifted triangle isomorphisms, and cone characterization are explicit.
- Step 7: checked against TR1--TR4 in `def-weil-triangulated-category` and the conclusion of 09QY; verdict: additivity, rotation, triangle morphism completion, and octahedral lifting are all accounted for through the faithful full embedding.
- Step 8: checked against the explicit shift and cone comparison maps and exact-functor definition; verdict: changing representative choices gives a natural isomorphism and preserves distinguished triangles.
- New node `lem-coef-dg-abc-homotopy-category-triangulated`: checked against the complete ABC situation, 09QJ, 09P6, 09QY and 09QU; verdict: statement-only, self-contained, correctly tagged, and strictly more general than the module specialization.
- Small cases: checked zero labels/modules, duplicate labels, zero and identity maps, negative shifts, and a nonzero dg differential; verdict: no edge-case contradiction or hidden boundedness/cofibrancy assumption.
- Changes: no mathematical or node-file changes were needed; appended this second-reading audit only.
