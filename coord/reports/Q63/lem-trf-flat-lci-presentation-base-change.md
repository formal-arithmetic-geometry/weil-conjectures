# Worker report: lem-trf-flat-lci-presentation-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-lci-presentation-base-change.json: statement, split; eight proof steps, no Mathlib match. Original statement and its dependencies preserved.
- citations.json: one verbatim statement quotation per step/node citation (21 entries).
- report.md: worker report and signed self-review.
- searches.jsonl: five actual searches performed by the required msearch.py command; all services returned results. write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. There was no prior split/report in this sandbox to reuse. No Lean was written, compiled or built. No repository or launcher file was modified, and no git command was run in the read repository.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and regular-sequence/base-change/cotangent/conormal terminology. The exact tag has no hit. Existing partial algebraic conormal or regular-sequence results do not state the item, including its intrinsic determinant and coherence clauses. No attachment is claimed from Mathlib or from a declaration containing sorry.

## WANTED

None. All source passages needed for this assembly were present in literature/stacks-project.

## Problems found and changes

The imported item had a statement but no proof. The statement is retained verbatim: no disputed hypothesis or conclusion was found. In particular regularity is asserted only in ambient local rings at points of the closed subscheme. The last sentence of Stacks 0FUD would be false if read as regularity at every ambient point: a unit equation has zero final quotient and is not regular under the project's definition. Our proof uses regularity only at primes containing J', and proves contractibility at every other prime instead. This is a clarification of the source's intended locus, not a change to this item's already correct statement.

The tempting flat-scalar-extension argument is inapplicable because R' need not be flat over R. The proof instead cites the existing 0FUD relative-equations node, whose hypothesis is flatness of A/J over R. Likewise 0473 alone only gives a surjective conormal map for arbitrary base change; injectivity here is proved by matching the two Koszul conormal bases. The report does not silently treat the new base as Noetherian.

No missing proof was moved into a clause-shaped new node. All non-elementary inputs were already available. The assembly includes the explicit homotopy outside the closed chart and the naturality and composition equations for determinant lines. Every step is under 2000 characters (longest 1181).

## Searches and reuse

Read the current chapter sec-trace-formula and unit sk-i-curve-zero, and retained the existing blueprint ancestor lem-trf-local-term-locality and the item's full via path. This item serves the imported nearby-cycle/semistable-modification branch and its lci-adjunction subargument; it is not the unit's key statement and makes no unit-record changes. The current main snapshot is retained as required by the dispatch; this auxiliary node has no blueprint_update field.

Searched the whole dag/nodes tree by 0FUD, 0CEP, 08QQ, 0FJY and conormal/base-change/Koszul/regular-sequence terminology. Read the existing item, parent flat-lci-canonical-adjunction, lci-cotangent-presentation, two-term-perfect-determinant and all cited nodes. Ran tools/blueprint_refs.py ancestor for the item and search for regular sequence, conormal, differentials and base change across all blueprint nodes. No blueprint duplicate of this full assertion was found; same_as stays []. Existing lem-pur-relative-regular-equations-base-change supplies exactly the difficult 0FUD fact, so creating another such lemma would duplicate it. Existing lem-pur-quasi-regular-flat-quotient-base-change was also read but not needed in the final proof.

The five new search records are the literal queries and result records from searches.jsonl. LeanSearch returned faithful-flat regularity, flat-base-change stability, finite-presentation and smoothness facts. LeanFinder's first phrasing returned smooth base change; its second returned weak-regularity under flat scalar extension and tensor flatness. Loogle returned cotangentComplexBaseChange and its formulas. The grep found its exact source and the regular tensor lemmas. Read Mathlib/RingTheory/Extension/Cotangent/Basic.lean:80-112, Regular/Flat.lean:34-91 and Regular/RegularSequence.lean:532-547. The first is a linear map, not the intrinsic derived cotangent base-change isomorphism. The regularity hits require flatness of the new scalar algebra, unavailable here. Smoothness is stronger than the item's lci hypotheses. Thus the item is not a Mathlib leaf. Historical searches on the imported item are preserved, including the old unavailable LeanSearch call; those are not represented as our new searches.

## Not duplicates

No new nodes were created; no new/existing same-tag pairs arise.

## Review by Q63

I read divisors.tex Tag 0FUD (remark-relative-regular-immersion-elements), more-algebra.tex Tag 0CEP (lemma-relative-regular-immersion-algebra), and the 062F regular-to-Koszul proof and 062I first conormal-basis paragraph. I read morphisms.tex 01U5 (lemma-flat-characterize) and 01V0 (lemma-base-change-differentials), algebra.tex 00CS (proposition-localization-exact), 00HT (lemma-flat-localization), 00RX (lemma-differentials-polynomial-ring) and 00RT (lemma-differentials-localize). I read cotangent.tex 08QQ (lemma-flat-base-change-cotangent-complex), perfect.tex 0FJX/0FJY and the affine two-term determinant construction in more-algebra.tex 0FJI/0FJM. The proof is marked agent-written because its assembly, contraction and coherence equations are written out here rather than copied from one source proof. There are no new-node source claims to review.

Step 1 uses the actual affine-flatness equivalence in lem-weil-pbc-flat-morphism-affine-criterion, the flat polynomial projection, localization preserving R-flatness, and the explicit quotient-tensor isomorphism. These say the facts taken from them: flatness on local rings is converted to flatness of the affine section rings, and B' is really the pulled-back closed chart. Finite presentation of R[x]_h is checked by the displayed presentation with ht-1; it is not assumed for an arbitrary localization. Principal charts suffice to cover the ambient open. The open restrictions of f retain the same stalkwise flatness by its definition.

Step 2 uses exactly lem-pur-relative-regular-equations-base-change. I checked its statement requires A flat and finitely presented over R, a regular sequence in A, and A/(f) flat over R. Step 1 establishes all three algebra conditions; the sequence is from the presentation hypothesis. Its conclusion is regularity at primes containing all the pulled equations, exactly the needed points of U'. The node imposes no flatness on R' and no Noetherian assumption on R'.

Step 3 uses the statement of lem-weil-pbc-regular-sequence-koszul-regular both before base change and at the local rings provided by step 2. The statement of lem-sc-koszul-base-change-iso is an isomorphism of complexes for any scalar extension, so applies to localization regardless of flatness or regularity. The defining Leibniz formula in def-weil-pbc-koszul-complex gives the displayed contraction dh+hd=1 when a generator is a unit. The statement of lem-weil-pbc-localization-module-exact justifies localizing homology. I wrote the annihilator argument detecting a nonzero module element at a maximal ideal, so did not hide a local-to-global hypothesis. This handles all ambient primes, including those outside the closed subscheme.

Step 4 uses lem-sc-koszul-conormal-basis, whose statement gives the specified classes as a basis whenever the sequence is Koszul-regular. Step 3 supplies this hypothesis for both unprimed and primed rings, even when the quotient is zero. The ideal base-change node gives the canonical map and its representative formula, with no flatness needed for its existence. I deliberately do not use its flatness-only injectivity conclusion. The displayed inverse between bases proves injectivity here. The tilde-pullback node identifies module scalar extension with sheaf pullback, including its formula on generators. The maps glue because they are restrictions of the same ideal-induced map; no assertion that overlaps are affine is needed.

Step 5 uses the arbitrary-base-change isomorphism and da formula from lem-trf-relative-differential-sheaf-base-change; that statement has no smoothness or Noetherian hypothesis. Polynomial Kähler basis and localization are expressly supplied by their two cited nodes. Pullback composition is in def-pc-module-pullback. The resulting coordinate differential map is the canonical one, and gives rank n on both sides.

Step 6 specializes lem-trf-base-flat-polynomial-tor-bound with n=0. Its base-derived-tensor assertion applies to every R-flat module, so with M=B it proves B tensor-derived R' equals the ordinary B', irrespective of R'. This is the exact Tor-independence hypothesis of lem-trf-lci-cotangent-presentation. That latter statement explicitly supplies the base-change isomorphism, the conormal models and compatibility with the models, identities and composition; these are not facts extracted from its proof. The conormal chain square is also checked on [f_i] mapping to df_i.

Step 7 uses the two-term determinant functor's stated exterior formula and its canonical pullback comparison. Both terms have the established ranks and are locally free. I wrote the image of a local line generator and specified that the covariant map on the negative dual line is the inverse transpose; a direct dual of the conormal map would point the wrong way. Thus the local formula is the map asserted by the item.

Step 8 uses the stated naturality/coherence of the cotangent comparisons and determinant pullback. The equation for lambda'_i b_i gives the equation on presentation transitions by composing inverses; determinant functoriality then gives the line transition equation. For a second base change the equality beta_gk=beta_k Lk*beta_g and the determinant pullback composition law give the stated delta equation. These are explicit equalities of intrinsic maps, not an appeal to basis choices coinciding on an overlap. This also avoids a separatedness assumption.

Small cases checked: c=0 gives C=0, the empty Koszul complex and the unmodified ambient differential determinant; n=d=0 gives both empty wedges equal to 1. If R'=0 or a pulled-back chart is empty, there are no local rings at points of U', and the Koszul complex still has zero homology. If a pulled equation becomes a unit away from U', its contraction is valid and we never claim regularity with a zero final quotient. The test R=Z, A=Z[x], f=x, R'=F_2 is nonflat scalar base change with flat quotient B=Z and gives the expected regular equation x and conormal generator after pullback. In contrast f=2 over Z has nonflat quotient and is excluded, as necessary: its image would become zero over F_2. These tests verify the precise roles of quotient flatness and the closed-subscheme locus.

No correction to the original statement was needed. The main repairs to the missing proof were avoiding flatness of R', proving exactness off U' explicitly, deriving conormal invertibility from bases rather than 0473's flat-only clause, and writing the dual-map direction and coherence equations. Generic off-unit algebraic inputs are declared in split_report.tool_uses; they retain the existing lci-adjunction route and do not replace a unit step.

## Completion and validation

Nothing mathematical remains unfinished for this stage-1 split. The server review_split check passed before writing this report. Full delivery dry run and push follow; their actual outcome is reported in the dispatch response.
