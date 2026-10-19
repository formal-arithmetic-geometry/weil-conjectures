## Files written

- dag/nodes/sec-smooth-purity/lem-kun-complex-colimit-hocolim.json: repaired split, seven steps, including the derived coproduct comparison and module coefficients.
- dag/nodes/sec-smooth-purity/lem-kun-derived-countable-sums-exact.json: one new statement-only unsplit node, Stacks 0A5L; no exact Mathlib match.
- citations.json: verbatim statement quotations for every citation in every step.

## Attachments

None. Read-only searches of slopmaster2 WeilConjectures for the blueprint id, homotopyColimit, hocolim, telescope, and the derived coproduct terminology found no finished declaration for the item or the new comparison. The project extension files about coproducts of complexes concern stability of quasi-isomorphisms, not the coproduct universal property after localization. Upstream master was searched only as reference material; its unfinished declarations do not count as proofs.

## Wanted

None; all sources used are available locally.

## Corrections

STATEMENT-DISPUTED: the imported statement calls a morphism from an unspecified triangulated homotopy colimit a canonical quasi-isomorphism. A derived-category object is not itself a complex or a chain map; moreover 090Z specifies the object only up to nonunique isomorphism. The corrected statement specifies the actual cone complex and chain map, AND proves its image and the termwise colimit are homotopy colimits in the original triangulated sense. It does not weaken the derived conclusion. It explicitly includes module sheaves, as required by the unit's Z/n coefficients and the callers. No boundedness, monicity, finite-generation, or coefficient restriction has been introduced.

The previous delivery proved the cone-to-colimit quasi-isomorphism but omitted the derived coproduct comparison. Its report's claim that naming the cone a model sufficed was wrong. This repair replaces that assertion by an application of 0A5L with its hypotheses verified. The module version is proved inside the module category, using faithful exact forgetting solely to establish exact sequential colimits, not to identify derived categories.

The blueprint's recurrence is corrected to x_n=f_(n-1)x_(n-1), and its long-exact-triangle citation is replaced by the existing cone projection theorem. In the finite kernel calculation, “its kernel” is now explicitly ker(q_m).

## Not duplicates

lem-kun-derived-countable-sums-exact vs lem-kun-grothendieck-derived-coproducts: the existing statement requires a Grothendieck abelian category and treats arbitrary set-indexed sums; the new statement requires only exact countable sums, with no generator or arbitrary filtered-colimit hypothesis. The existing statement does not specialize to that weaker hypothesis. The new statement is precisely the general comparison 0A5L invoked by 0949, not a sheaf-specific restatement of the item's conclusion.

lem-kun-derived-countable-sums-exact vs lem-pc-derived-module-direct-sums: the existing node concerns modules over an ordinary ring, whereas the new statement is for any abelian category with exact countable sums, including sheaves on a site.

lem-kun-derived-countable-sums-exact vs lem-pc-derived-ambient-direct-sums: the existing statement concerns structure-sheaf modules on schemes, not arbitrary abelian categories with exact countable sums.

lem-kun-derived-countable-sums-exact vs lem-pc-complex-hocolim-colimit: the existing telescope assertion concerns a sequence and its filtered colimit; the new statement concerns unrelated countably many complexes and their derived coproduct universal property. It does not assert any telescope or colimit comparison.

I searched the entire DAG by 0A5L/lemma-direct-sums, exact countable sums, coproduct and derived localization vocabulary, and the entire blueprint using blueprint_refs.py searches “derived coproduct”, “exact countable”, “termwise direct”, “direct sums”, and “coproduct”. No blueprint node states the new hypothesis-general theorem. Its blueprint ancestor is this imported item and its from.place names the final triangle identification. Existing module, ambient, and Grothendieck coproduct nodes were opened to compare hypotheses; no generic theorem under only exact countable sums was found. New-node Lean searches found no attachment.

## Unfinished work

No gap remains in the item's split; the one new comparison is deliberately statement-only for its own later split. No new Mathlib leaves. LeanSearch was unavailable (HTTP Internal Server Error). Two LeanFinder phrasings found localization and AB4 infrastructure, not the derived coproduct assertion. Loogle's first pattern had an unknown identifier; this is recorded as an invalid-query result rather than evidence of absence. The second query DerivedCategory.Q successfully found the functor and localization/additivity/shift instances. Both grep searches were run through msearch.py; finite exact functor infrastructure is not the needed countable derived coproduct theorem. I read DerivedCategory/Basic.lean at Q (95), its localization (98), and additivity (146), and GrothendieckAxioms/Basic.lean for the CountableAB4 candidates; these justify no whole-node leaf. The exact search texts and returned names are recorded in the new node from searches.jsonl.

## Review by NK

I read the complete maintainer review at reviews/NK__lem-kun-complex-colimit-hocolim__6445c66acf7e/review.md, the master blueprint item (order 1719), the chapter and Kunneth unit records, and the stage-1 requirements. The unit's empty numbered route does not authorize discarding its derived module-coefficient content. I read Stacks derived.tex 093W (lemma-compute-colimit), 0949 (lemma-colim-hocolim), 0A5L (lemma-direct-sums), 090Z (definition-derived-colimit), and the cone/0152 comparison. I also read sites-modules.tex 03CO (lemma-limits-colimits-abelian-sheaves), 03DA (lemma-abelian) and 03DB (lemma-limits-colimits), including their proofs. The new node has exactly the hypothesis of 0A5L and introduces the category, countable family, exactness condition, localization, sum complex and coprojections. It carries no proof steps or proof sketch. Its conclusion holds for unbounded complexes, as 0A5L states; no common lower bound is assumed.

Step 1 opens and uses exactly the existence and exactness clauses of lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact and the faithful/exact/colimit-preserving clauses of lem-weil-pbc-module-sheaves-colimits-forgetful. The site's sets-of-objects convention is in def-weil-pbc-sites-and-cohomology, so all indexing and sheafification are within the chosen universe; N is small and filtered. Reflection of exactness is written using preservation of kernels/cokernels and faithfulness detecting zero objects. It follows by checking the middle homology and endpoint kernels/cokernels, not by an unproved equivalence between coefficient categories. The module-colimits node is declared as a generic off-unit tool in split_report.tool_uses, since no unit node supplies this coefficient bridge.

Step 2 is the finite matrix computation. At m=0 it is the identity sequence. At m=1, v(x)=(x,-f_0x) and q(y)=f_0y_0+y_1. At m=2, v(x_0,x_1)=(x_0,x_1-f_0x_0,-f_1x_1); the recursion in the text gives its inverse on ker(q). The section, monicity, kernel calculation and differential compatibility are all explicit. The formulas are finite biproduct morphisms, valid in either coefficient category; no assertion about sectionwise infinite sheaf sums is used.

Step 3 uses the colimit definition's actual universal property to identify both colimits of finite initial sums with A. Step 1 supplies exact sequential colimits in the selected coefficient category. The quotient square commutes by f_m f_(n,m)=f_(n,m+1), and the first map is u on each summand. The resulting short exact sequence is degreewise, with no boundedness or monicity of f_n assumed.

Step 4 uses the differential and shift signs in def-weil-abstract-derived-category: p d=q(db+ua)=d q(b), since qu=0 on each injection. This proves the canonical chain map, rather than choosing a triangulated-cone isomorphism.

Step 5 uses the full precise statement of lem-pc-cone-short-exact-quasi-iso. Step 3 provides its short exact sequence in the abelian category A, and its two restrictions match the chain map of step 4. This is the same Mathlib leaf as before; the statement applies to modules as well as abelian sheaves.

Step 6 verifies exact countable sums by finite initial sums and sequential exactness, as in 093W's first assertion. The finite-biproduct argument is coordinatewise; the universal-property identification is written out. It then uses the new node's exact assertion that Q of the termwise sum, with Q of the actual coprojections, is a coproduct in D(A). This is the missing 0A5L application, not merely preservation of quasi-isomorphisms under sums. The new node is a general tool for arbitrary countable families, strictly below the sequential-colimit/telescope theorem. It neither has transitions nor asserts the item's cone comparison.

Step 7 opens def-weil-abstract-derived-category, whose statement says Q is additive and its cone triangles distinguished, and def-kun-truncations, whose statement defines homotopy colimits through the 1-shift triangle. The equations on the coprojections identify Q(u) with that actual first arrow. The isomorphism Q(p) transports the last vertex; the text specifies both the new second arrow and the new last arrow, so there is no hidden “transport” inference. The second arrow is Q(q) by the concrete restriction equation. This proves precisely the triangulated conclusion the previous delivery omitted.

For the new statement's edge cases I checked the empty family (the zero complex and zero derived object), a singleton (the identity coproduct), complexes concentrated in degree zero, and genuinely unbounded complexes: exact sums commute with kernels/images in each degree, so sums of quasi-isomorphisms remain quasi-isomorphisms without any boundedness. The localization universal property is non-elementary and is left as the named 0A5L theorem, not inferred merely from this observation. For the item's edge cases I checked the zero system, zero transitions (u=1 and colimit zero), identity transitions, and nonmonic transitions such as multiplication by 2 on Z/4 in degree zero. The same examples over constant Z/4 module coefficients show why neither flatness nor transition injectivity is needed. The zero coefficient ring and empty-scheme site give zero objects and the same triangles.

Repair of C1/E4 point by point: the exact-countable-sums comparison 0A5L is now a cited node in step 6; the derived-coproduct conclusion is now explicit in both the statement and proof; the actual cone triangle is used only after that comparison; the termwise colimit is also exhibited as a homotopy colimit; module coefficients have their own exact-colimits verification in step 1 and all following arguments take place in that category. The previous report and second-reading claims that omitted this comparison have been replaced, not retained as a certification of the repaired version.

## Second reading by NK

- Step 1 checked against sites-modules.tex tags 03CO, 03DA, 03DB and the cited node statements: the abelian, faithful exact, and colimit-preserving hypotheses are all present; verdict correct.
- Step 2 checked against derived.tex tags 093W and 0949 and the displayed finite matrices: the zero, one-step, and general finite cases are explicit; verdict elementary and correct.
- Step 3 checked against 093W and the colimit definition: the finite-sum colimit identifications and exactness hypotheses are stated; verdict correct.
- Step 4 checked against the cone convention in the derived-category definition and 0949/0152: the differential calculation establishes the actual chain map; verdict correct.
- Step 5 checked against the statement of lem-pc-cone-short-exact-quasi-iso and the short exact sequence from step 3: both restrictions agree; verdict correct.
- Step 6 checked against derived.tex tags 093W and 0A5L and the new comparison node: countable exactness and the derived coproduct conclusion are both present; verdict correct.
- Step 7 checked against the derived-category and homotopy-colimit definition nodes: the distinguished cone triangle, coprojection equations, and transport along Q(p) are explicit; verdict correct.
- New node lem-kun-derived-countable-sums-exact checked against derived.tex tag 0A5L clause by clause: self-contained exact-countable-sums hypotheses, unbounded complexes, empty family, and derived coproduct conclusion; verdict valid statement-only tool.
- Item statement checked against the blueprint item and the cited definitions: cone map, derived coproducts, module coefficients, and homotopy-colimit clauses match; verdict valid after the recorded statement dispute.

Changes made in this second reading: no node text or citations required correction; added this hypothesis-by-hypothesis review record and retained the explicit 0A5L comparison that repairs the prior omission.

Against B-E, every new notion has a definition dependency or inline description; the new node is statement-only and sourced by the correct tag/label; all non-elementary claims are cited; every cited statement was opened and copied verbatim into citations.json; the source proof has not been moved wholesale into a child. The chapter/unit route remains the finite telescope, exact colimit, derived coproduct and cone triangle route of 0949. No Lean was written and no compiler/Lake/build tool was run.
