# Stage-1 delivery: lem-weil-point-transformation-rational-normalization

## Files written

- dag/nodes/sec-six-functors/lem-weil-point-transformation-rational-normalization.json — existing statement, now split in five explicit formal steps; no Mathlib match for the full statement.
- citations.json — one verbatim statement quotation for every dependency of every proof step.
- searches.jsonl — actual search-command log; retained alongside the item's upstream searches.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. The item statement, statement dependencies, source, creation record, and blueprint ancestry are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and rational-normalization/point-transformation terminology, and inspected the rationalization source family. No project declaration states this item's full functor-action and normalized-comparison assertion. Generic localization extension is not an attachment to this point-specific statement.

## WANTED

None. Deligne's paper and the algebra sources used for the explicit calculation are present.

## Corrections and source scope

The item arrived statement-only; no existing proof was discarded. Its statement is sound under the supplied functor and comparison hypotheses. No STATEMENT-DISPUTED correction is needed. The source explicitly distinguishes Deligne's coefficient-descent context from this agent-written completed pro-etale argument; this distinction is preserved in proof_origin and every step's source.

The specified unit record concerns finite-coefficient exceptional inverse image, whereas this historically attached node concerns the Frobenius transport ancestor. I preserve the inherited chapter, unit and blueprint ancestry, and do not change the unit's statement or route. The proof uses the same specified point and pullback comparisons as the item's assumptions. The three generic statement tools from other units are declared in split_report.tool_uses: coefficient-complex rationalization, integral operations/scalar extension, and point sections/scalar extension. None replaces a geometric step of the unit.

## Mathlib searches and reuse

Ran the required leanfinder, loogle, grep and leansearch commands, and a second semantic phrasing. LeanSearch and Loogle find CategoryTheory.Localization.Construction.natTransExtension, read at Mathlib/CategoryTheory/Localization/Construction.lean:247-289, with the declaration at line 269. It extends transformations for the constructed categorical localization, and does not state the specified raw tensor actions or this normalized point/pullback scalar equation. An identification of localizations and additional comparison arguments would be necessary. The LeanFinder module-extension hits are about module functors rather than these raw constructible categories. Accordingly the item is a split, not a Mathlib leaf. The successful LeanSearch call is recorded as successful; the old upstream unavailable call is retained as history.

Before deciding against new nodes, searched the whole DAG by scalar-localization, rationalization, balanced-tensor and coefficient-complex terms and used blueprint_refs.py searches for rationalization, natural transformation, scalar localization and point-section. The existing lem-weil-coefficient-complex-rationalization supplies exactly the potentially non-elementary derived tensor comparison and coherence. The existing lem-pur-semilinear-scalar-localization is a more general formal tool, but is unnecessary for the short direct calculations here. No duplicate or clause-restatement node is created.

## Not duplicates

No new nodes; no new/existing pairs.

## Review by Q10

I read Deligne, Weil II, printed pp. 150-151, (1.1.3) and (1.1.7), from PDF pages 15-16. The former displays coefficient extension on Hom groups; the latter explains point transport. Neither asserts the completed pro-etale normalization in this item. I also read the ancestor def-weil-global-geometric-frobenius in the blueprint, the chapter and unit records, and Stacks algebra.tex, labels section-tensor-product (Tag 00CV), lemma-tensor-product and definition-base-change (Tag 05G3). These give context and the elementary balancing calculation, not an unquoted theorem about sections commuting with completion. There are no new-node sources to audit.

For Step 1 I opened def-weil-finite-coefficient-point: its integral functor is linear and its rational functor has exactly the pure-tensor formula used. I opened def-weil-derived-pullback-tensor-hom: its rational clause gives P(v tensor a) = P(v) tensor a, with additive extension respecting balancing. The specified integral P is already an operation on the stated constructible categories. I opened def-weil-module-base-change for the linear action on maps and compatibility with composition. I opened lem-weil-coefficient-complex-rationalization: it states exactness and quasi-isomorphism preservation for the termwise tensors and their induced derived functors, so tensoring the supplied derived morphism eta is legitimate. The displayed balancing check is an argument on the tensor quotient, not an assumption that integral maps embed.

For Step 2 the only starting equality is the naturality hypothesis for eta at an integral arrow. Tensoring preserves that equality and its composite. I read lem-weil-linear-abelian-derived-category and def-weil-linear-category: they give the scalar-bilinearity and distributivity needed to multiply and add these equations in D(E). I read def-weil-rationalization-karoubi: objects are unchanged and every Hom group is the displayed tensor module. Hence finite sums of pure tensors exhaust the arrows. No separate representability of an arrow by an injectively embedded integral map is used.

For Step 3 I read def-weil-linear-scalar-localization, including identities and its composition rule. The explicit calculation for a uniformizer-power-torsion morphism vanishes in the balanced tensor quotient. Applied to an identity it also covers integral torsion objects, and if any object becomes zero the same identity argument works. Zero maps, zero scalars and the empty sum satisfy the equations. Nothing assumes flatness or torsion-freeness of the integral Hom groups.

For Step 4 I reread all of lem-weil-coefficient-complex-rationalization, not merely its chain-level formula. Its statement explicitly gives beta natural for arbitrary derived arrows. E and L here are finite subfields of the fixed algebraic closure, as that lemma requires. This identifies the rationalization of eta tensor O_L with t tensor L and fixes the iterated-tensor endpoints. I checked the order and domains: alpha inverse goes from P_L U K to U P_E K, then sections goes to the object on which phi at P_E K is defined. Thus applying q_L to the assumed equation gives the displayed b equation with the correct inverse and orientation. This step never invokes a fresh base-change theorem.

For Step 5 I opened the full statements of lem-pur-integral-operations-scalar-extension and lem-weil-point-sections-scalar-extension. They explicitly supply naturality, identity for equal fields and composition compatibility, exactly what is taken from them. A functor carries the two inverse equations to the inverse equations of the actual images; this proves the assertion about the supplied inverses. Integral naturality squares extend by the same scalar multiplication and summation as Step 2. The coefficient-complex lemma explicitly supplies beta's unit and three-field compatibility, so the tower identifications after tensoring are those in the statement. Equality fields E=L and E=L=M reduce to the stated identity identifications.

I checked delivery-errors B-E against the node and open sources: all objects already introduced by the statement remain unchanged; every non-elementary ingredient used is a cited existing statement; no definition is used for an extra geometric or exactness theorem; no proof text of a dependency is used as an interface; no new nodes, hidden rephrased clauses, circular argument, or forbidden SGA source are introduced. The remaining algebraic manipulations are written out and marked elementary, with the substantive input statements cited. All five steps are below 2000 characters. Every proof dependency was checked for a path back to this item; none has one. citations.json contains the entire verbatim statement of each cited node, so all portions used are available to review.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled. Required server dry run and direct delivery follow this review.
