# Q112 stage-1 report

Item: lem-sfb-field-scalar-projection-mate-coherence. Date: 2026-10-23.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-scalar-projection-mate-coherence.json: split statement, nine proof steps, existing nodes only; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each of the 22 step/node citations.
- report.md: this report. searches.jsonl is the unmodified search-command log. write_split.py is a sandbox-only preparation script, not a delivery node.

No new nodes and no Mathlib leaves. No unit realization is due: this item is an auxiliary created node, not the unit key statement.

## Attachments

None. Searched the live lean/WeilConjectures source both for the item identifier and the projection/scalar/mate notions. There is no declaration proving the whole item. The existing lean/Sheaf/AlgebraicGeometry/FieldActionDerivedSectionTransport.lean contains the parent theorem with sorry (line 184); its proof docstring steps 10–13 provide inherited source material, not an attachment. The FieldAction*Data modules specify data, and their fields are not existence proofs.

## WANTED

WANTED: a published treatment of the full normalized condensed field-action scalar/geometric/point derived projection comparison, for lem-sfb-field-scalar-projection-mate-coherence. The named literature supplies the general ingredients, not this combined assertion. The proof is accordingly marked agent, rather than attributed to Bhatt–Scholze Example 4.1.10.

## Corrections and route

The item had an empty proof. Kept its statement and stmt_deps verbatim, including arbitrary condensed coefficients, ordinary unbounded derived categories, normalized section maps, and non-flat coefficient maps. No STATEMENT-DISPUTED was needed. Retained the inherited blueprint ancestry: blueprint_refs.py ancestor reports from.node=None, with the same existing via chain and concrete Paragraph (3) place. The item is not the unit key theorem and no chapter/unit route changes.

Searches of the full imported blueprint with blueprint_refs.py search 'scalar projection' and 'coefficient projection' found the open-Tor direct-image argument and several unrelated coefficient constructions, not this statement. DAG searches by scalar projection, conjugacy, slice counit, composition normalization and first-variable shifts found all the general ingredients already present. Their statements were opened before use. In particular the exact-scalar-extension lemma lem-sfb-internal-scalar-projection-mate was deliberately not used: its hypothesis would exclude non-flat maps here. The generic non-flat internal normalization and ringed comparison nodes supply what is needed.

The inherited item Mathlib searches were read and retained. Five new command searches, two semantic phrasings, Loogle, source grep and LeanSearch, are recorded as actually returned in searches.jsonl and appended in mathlib_searches. Read Mathlib/CategoryTheory/Adjunction/Mates.lean around conjugateEquiv and conjugateEquiv_counit (lines 275 and 285). These prove formal adjunction identities, not this field-action/derived-section comparison. Other returned hits are derived unit/counit, exact-functor shift instances and scheme-module comparisons. No full exact or one-line specialization match.

## Not duplicates

No new nodes. All supporting facts are citations of existing DAG nodes; the item itself is the assigned live unsplit node. No same-tag new/existing pair is introduced.

## Review by Q112

I read coord/brief-stage1.md, stages/1-dag.md, the three fixed/followed/free blueprint levels in SETUP.md, GOAL.md, the chapter and unit records, and delivery-errors.md B–E. The main source is an agent expansion of the inherited FieldActionDerivedSectionTransport docstring steps 11–13. I read Bhatt–Scholze Example 4.1.10 in the local PDF: it supplies the profinite Galois presentation, not the new derived coherence claim. I also read sites-cohomology.tex lemma-adjoint (07A6), lemma-derived-pushforward-composition (0D6E), lemma-pullback-tensor-product (07A4) and equation-projection-formula-map (0B56); sites-modules.tex lemma-localize-morphism-ringed-topoi (04IF); and derived.tex lemma-derived-adjoint-functors (09T5). These justify the literature labels while the actual specialized normalization statements come from the cited DAG nodes.

Step 1 uses lem-sfb-internal-scalar-pullback-normalization for the actual internal K-flat exchange and its identification of independently derived geometric adjunctions. It uses lem-weil-pbc-ring-sheaf-change-adjunction for b and rho, with inverse orientations explicitly declared. The coefficient isomorphisms are pulled from the same point and the coefficient square commutes, as required. The lemma has no flatness requirement.

Step 2 applies lem-sfb-ringed-comparison-tensor-adjunction to the two ringed routes from (X,R'_X) to (s,R_s). The comparison is between composite adjunctions, not the bare geometric adjunctions; this matters when the scalar map is not flat. The cited theorem expressly permits non-exact underived module pullbacks. Its counit equation and the normalization in lem-sfb-kflat-scalar-comparison-normalization give the two written equations. The latter statement identifies its K-flat comparison as the scalar mate and explicitly excludes a flatness requirement. The b and rho directions are consistent with step 1.

Step 3 uses only the mate formulas and their inverse bijection from def-weil-pbc-adjunction-mate, plus naturality of units and counits. I checked each displayed arrow: A=FM, N=S_XM, t:L'S_sA to N; both scalar transposes have domain LA and codomain V_XN. Expanding the two equations from step 2 yields the displayed chain, rather than assuming the desired projection equality. This is the only elementary step. It contains the formal two-adjunction calculation; no geometric claim is hidden in it.

Step 4 uses the given scalar and geometric transport data only for properties their definitions actually require: preserving Hom transposes, identity section/derived-unit normalization and shifts. The needed square of derived composites is furnished by lem-pur-ringed-derived-composition-cocycle, whose statement explicitly includes coefficient changes on identity topoi. This proves equality with beta by its definition, without citing the coefficient-transport definition as an existence theorem.

Step 5 uses lem-sfb-field-free-orbit-derived-slice-sections for the actual forgotten identification and its explicit preservation of geometric counit and K-flat scalar comparison, not merely an object isomorphism. Its field data and qcqs hypotheses are those assumed here. The sheaf-slice comparison node applies to arbitrary sheaves of sets, so h_sbar need not be an original affine test object. Its statement gives the written counit equation and preservation of K-flat/K-injective representatives. Hence no unbounded acyclicity or affine small-site assumption has been introduced.

Step 6 uses lem-sfb-derived-composition-adjunction-normalization only for geometric pullbacks a_s^* and p_sbar^*, both exact; p_sbar^* is the separably closed presentation equivalence. It is not applied to scalar extension. Its statement identifies the counit with the composite counit. Expanding this counit and pasting the given normalized forgotten scalar square yields the point adjunct displayed in the item. This is the same object comparison fixed by geometric transport, not an alternative isomorphism.

Step 7 uses lem-sfb-internal-section-scalar-adjunction for the actual internal/ring-sheaf scalar units, counits and unbounded derived transposes on arbitrary small sites. It then applies the general ringed comparison theorem to p_Xs and the coefficient square, with the normalized K-flat exchange statement fixing the arrow. Finally lem-weil-pbc-ringed-projection-mate-exact defines the R-linear projection as exactly the computed counit transpose. No use is made of lem-sfb-internal-scalar-projection-mate, which assumes exact scalar extension. The point morphism need not be a morphism of schemes for the three general ringed/site statements used here.

Step 8 uses the direct-image cocycle for successive restrictions and the coefficient projection cocycle for successive extensions. Both statements explicitly cover coefficient maps without flatness. I distinguished these two uses: the latter does not serve as evidence for a restriction square. The input morphism squares follow from natural transformations and natural Hom bijections already in use, with no additional finiteness or representation hypothesis.

Step 9 uses lem-weil-pbc-derived-adjunction-shift for units/counits, the canonical tensor shifts in lem-weil-pbc-ringed-projection-mate-exact, and lem-sfb-ringed-projection-first-shift for the first input with R' fixed. This checks shifts in M explicitly, instead of misusing the projection theorem's shift in the tensor argument. The required coefficient datum is assembled only at the end using the actual clauses of def-sfb-field-action-coefficient-transport-data; that definition is not used to prove its own existence.

For delivery-errors B, no unsupported new statements or hollow data were created. For C1/C4, I opened every cited node, matched its actual statement to the precise use above, and generated citations.json by asserting each quote is a literal substring. Non-elementary imported facts are cited. For D, none of the conclusion is relocated into a restated new node; the proof contains the comparison calculation and the slice/composite-counit assembly itself. For E, I tested the identity coefficient map (units and comparisons reduce to identities), zero M, X=s with a=id (the geometric counit is identity), trivial G/separably closed k (the forgotten presentation is already the point one), and non-flat constant coefficients Z to Z/n. The proof uses K-flat scalar extension in the last case and never tensor-exactness or preservation of K-injectives by coefficient restriction. There is no finite cohomological-dimension hypothesis, no boundedness claim, and no assertion that a projection map is invertible. All steps are below 2000 characters; no long step hides a separate lemma.

Generic tools outside the item's unit are declared in split_report.tool_uses, for the maintainer to judge; no tool_uses field is written directly. No Lean file was written, no compiler/Lake/build command was run, and no shared repository or launcher file was changed.

## Unfinished

None of the requested stage-1 mathematics remains. Delivery validation and push are recorded below when complete.

First dry run returned a citation-format failure: step 7 used a short no-flatness quote. Replaced it with the full K-flat scalar-mate normalization sentence from that same node, which states the comparison actually used. Nothing was pushed by that run.
