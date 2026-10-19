# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometric-component-count-generic-constancy.json`: statement item; seven-step split, unchanged statement, no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-fibre-component-count-base-change.json`: new statement-only unsplit lemma, Stacks 0556; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-component-lower-bound.json`: new statement-only unsplit lemma, Stacks 0554; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every dependency of every proof step.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` by the item blueprint tag, geometric component vocabulary, generic component vocabulary, and separably-closed irreducible-component vocabulary. No project declaration states this item or either new lemma exactly. GenericConstancy.lean concerns constructible sheaves; RelativeComponentConstructible.lean concerns connected components. The master reference was also checked for generic component declarations and is not treated as completed proof evidence.

## Wanted

None. All mathematical sources used are in the repository's Stacks source.

## Findings and corrections

The imported statement is correct against Stacks 055A, including arbitrary finite-type morphisms, arbitrary base schemes, and the empty generic fibre. No statement or hypotheses were changed. Its old Mathlib searches are retained; Q104's actual searches and second phrasings are appended and logged by msearch.py. No new leaf was found: the candidate component equivalences in Mathlib require an already open map with irreducible fibres; they do not split arbitrary geometric components or spread counts. The connected-component bijection node `lem-weil-pbc-sepclosed-field-components-bijection` does not concern irreducible components and is not cited.

The Stacks proof's upper-bound closure/cover/shrinking argument is already available through `lem-sbc-geometric-generic-cover-spread`. Its intersection-persistence output is unused. Its supplied generic field and finite index are preserved, so its component-cover bound is the same n used in the lower bound. The finite etale generic field model is reused through `lem-sbc-etale-generic-residue-field-model`; its statement gives an etale morphism and a compatible generic residue-field isomorphism, not a finite surjective model. The proof requires only its open image, so it claims neither finiteness nor surjectivity of this model. These are generic geometry tools, declared in split_report.tool_uses, rather than changes to the trace unit's route.

## Unfinished work

The two new inputs are deliberately statement-only and unsplit, for later stage-1 items. Their proof source is identified by exact Stacks tag and label. No Lean files, compilers, Lake commands, repository writes, or direct git commands were used.

## Not duplicates

lem-trf-geometric-fibre-component-count-base-change vs lem-trf-geometric-component-count-generic-constancy: 0556 proves choice independence and a base-change identity for arbitrary scheme morphisms; the item proves generic constancy for finite-type families via upper and lower bounds. It does not assume or imply generic constancy by itself.

lem-trf-generic-fibre-component-lower-bound vs lem-zl-finite-type-fibre-component-lower-bound: the new 0554 statement bounds the NUMBER of ordinary components near an irreducible generic point over an arbitrary base; the existing 0B2L statement bounds the DIMENSION of each component in rational closed fibres of finite type algebras over a field.

lem-trf-geometric-fibre-component-count-base-change vs lem-weil-pbc-sepclosed-field-components-bijection: the existing connected-component statement cannot be used for the 0556 irreducible-component count; the notions differ, as the two lines meeting at a point demonstrate.

No node with primary source 0554 was found. The only existing primary-source 0556 collision is the item itself, distinguished above. Whole-DAG searches included exact labels, component-count phrases, source tags and related names; blueprint_refs.py searches for irreducible components, component count, geometric components, 0554 and 0556 found no equivalent blueprint node. The broad irreducible-components search returned eleven blueprint entries, primarily finite-component and affine-neighbourhood facts, none proving either new statement. The generic splitting, etale model and geometric cover-spreading nodes were read and reused rather than recreated.

## Review by Q104

I read Stacks more-morphisms.tex at 055A (lemma-nr-geom-irreducible-components-good), 0556 (lemma-base-change-fibres-nr-geometrically-irreducible-components), and 0554 (lemma-irreducible-components-in-neighbourhood), including their complete proofs. I also read 0551's field-splitting/model proof and 055G's closed-component-cover and shrinking paragraphs. For the reduction and auxiliary hypotheses I read schemes.tex 01J3 (lemma-reduced-closed-subscheme), morphisms.tex 01T6 (lemma-finite-type-noetherian), and 03WT (lemma-etale-open). The new 0556 statement has the source's arbitrary morphism and arbitrary separably closed extension hypotheses, including infinite counts. The new 0554 statement has its finite-type, irreducible base and finite ordinary generic count hypotheses, including n=0. Neither node contains proof data or a disguised proof sketch.

Step 1 uses the reduced-induced-closed-subscheme node's actual construction of a closed reduced scheme, finite-type base-change stability, and the new 0556 functional identity. Its generic-point claim is proved by the closed-cover definition of irreducibility; it does not need the entire original base to be irreducible or Noetherian. Step 2 uses the generic component-splitting statement for a finite-type scheme over a field, then applies finite-type-over-Noetherian and finite-components to G. Noetherianity of Spec L follows directly because a field has only two ideals. The extension and indexing set are fixed throughout the proof.

Step 3 takes exactly the general field-fibre, surjection and irreducible-cover output of geometric-generic-cover-spread, whose full statement I opened. Images need not be closed: the text takes their closures, then applies irreducibility to a FINITE closed cover and maximality to identify each component. This proves the upper bound without claiming that images or individual B_i are components. The empty cover is handled separately. Step 4 takes only the etale map, generic point and commuting residue-field isomorphism actually provided by etale-generic-residue-field-model. The ordinary generic fibre is G by associativity of fibre products and that isomorphism, using the fibre and fibre-product definitions. No finite/surjective property is smuggled in. A generic point of all of T ensures T is irreducible.

Step 5 uses the new ordinary lower-bound node with exactly its hypotheses: q is finite type, T has generic point xi, and P_xi has the fixed finite count n. Step 6 uses field-extension-surjective and surjective-base-change for the geometric projection, finite-type-base-change and the same Noetherian/finite-components nodes for finiteness. Continuous images of the geometric components, followed by closure, cover the ordinary fibre. Finite irreducibility and maximality give the count inequality; this is a written elementary topology argument, not a hidden algebraic geometry lemma. Step 7 uses etale-morphism-open-map for the image of the particular open U intersect g inverse W, and 0556 for the equality at a chosen lift. Nonemptiness follows at xi, not from an unproved global-surjectivity assertion. The two opposite bounds then give equality.

I checked B1--B10: self-contained statements, correct definition citations, single TeX escaping, local Stacks source paths and labels, real logged searches with second phrasings, no inappropriate Mathlib leaf or project attachment, and exact blueprint ancestry. I checked C1--C8 by opening every cited statement, constructing every citations.json entry from it, and declaring the four off-unit non-leaf generic tools. I checked D1--D5: the new nodes are base-change invariance and an ordinary lower bound, not copies of the generic-constancy result; upper-bound construction and open descent remain in the item, with no circular use of its constructibility parent. All steps are below 2000 characters, and none hides an additional non-elementary subclaim. I checked E1--E7 against empty fibres, nonreduced bases, arbitrary non-Noetherian domains, separably closed rather than algebraically closed fields, and nonseparated families. No additional hypotheses or SGA source are used.

Small cases: the empty family gives n=0; a constant union of r affine spaces gives r; xy=t illustrates that the special component count can increase from one to two; the punctured identity Spec k[t,t^-1] to Spec k[t] has generic count one and empty fibre at zero, showing why the ordinary lower bound requires shrinking; Spec C over Spec R illustrates why ordinary and geometric counts differ (one versus two), so Step 6 uses an inequality. Two crossing lines are connected but have two irreducible components, ruling out the nearby connected-component bijection as an input. The ordinary bound is not asserted at all special points, and the result uses an open in the point closure, not necessarily an ambient neighbourhood. No correction to the imported statement was needed. The proof was improved during drafting to state the open-image descent and the ordinary-to-geometric component comparison explicitly; this removed two possible hidden assumptions.

## Validation

The server dry run passed check_dag, review_split and delivery preflight at 78a52b4587. The first local citation gate required a quotation of at least 40 characters for finite-type-over-Noetherian; both entries now contain that full statement. The final report also records the punctured-identity edge case for the need to shrink.
