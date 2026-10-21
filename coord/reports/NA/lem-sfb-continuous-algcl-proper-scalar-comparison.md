# Stage-1 report: lem-sfb-continuous-algcl-proper-scalar-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-algcl-proper-scalar-comparison.json`: assigned statement, unchanged; split into six proof steps. The proof uses the existing proper finiteness theorem for the actual all-continuous coefficient, the existing rational comparison only for the finite-subextension-valued ring, and a separate coefficient-topology comparison. The normalized counit mate is checked by an explicit Hom calculation and then by the coefficient cocycle.
- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-algcl-topology-comparison.json`: one new statement, unsplit, no Mathlib match. It states that the actual derived extension along the inclusion of the two different coefficient rings is an equivalence on their bounded constructible full subcategories, for the standing finite-type schemes. It has no proper map, no direct-image assertion, and no proof or proof dependencies. Its exact reference is WANTED.
- `citations.json`: one verbatim statement quotation for each citation in every step. Whole statements are quoted so that hypotheses remain visible; the precise clauses used are identified below.
- `report.md`: this report. `searches.jsonl` was produced by the required msearch command. Source-text extracts and the writing script are local sandbox working material, not node deliveries.

There are 1 new nodes and 0 Mathlib leaves. Neither the repository nor launcher files were edited, and no compiler, Lake, or build tool was run.

## Attachments

None. I searched the upstream `lean/WeilConjectures` by the exact item tag and by proper/scalar/derived and continuous-algebraic-closure terminology. The proper finite-coefficient scalar theorems concern finite discrete rings. `ProperLowerStarEllAdic.lean` contains the related proper finiteness statements, explicitly with `sorry`; the finite-extension and locally-finite algebraic-closure constructions in FieldCoefficient/ScalarExtension and ModuleObject/Colimit do not give this item. The proposed new topology comparison has no project declaration found by its name or concept.

## WANTED

WANTED: an exact proof/reference for invariance of the bounded constructible ordinary pro-etale module derived category under the inclusion from finite-subextension-valued algebraic-closure sections to ALL norm-continuous algebraic-closure sections, for `lem-sfb-constructible-algcl-topology-comparison`.

This reference was not found. Bhatt--Scholze, Sections 4.3 and 6.8, and Hemo--Richarz--Scholbach, Section 7.2, Lemma 7.9, use the colimit topology for infinite algebraic extensions. They do not supply the new lemma. The new lemma is explicitly an agent statement-only obligation, not a claimed consequence of those references. The assigned split's proof_origin is agent. It is essential that the remaining topology theorem be proved or refuted in its own subsequent split.

## What was wrong or incomplete

The assigned item had no proof; its source place already said the exact all-continuous comparison was WANTED. Its mathematical statement is unchanged. The current blueprint paragraph (3) supplies the proper-image role in the alteration argument, but its rational coefficient proof cannot identify the norm-topology ring with the finite-subextension ring.

For clarity, take the profinite convergent sequence S consisting of a limit point and points s_n. Choose primitive ell^n-th roots of unity zeta_n in Omega and set a(s_n)=ell^n*zeta_n and a(limit)=0. This is norm-continuous, but its image is in no finite extension: such an extension would contain zeta_n for every n. Thus C(S) differs from B(S), although C(*)=B(*)=Omega. The split never replaces one ring by the other. It uses their actual inclusion, through an explicit new category comparison obligation.

The inherited unit record is the older sec-six-functors version; I read it and the current main-20261015 unit and paragraph (3) at the source path of the item. The current source controls the proof. The ancestor tool returns None because the created.item chain ends in a Lean module name. I retained the item's inherited blueprint metadata, and its child carries from.node=null and the item's exact via chain with the item prepended, as required by that tool. I did not edit the chapter, unit or any metadata owned by the maintainer.

## Not duplicates

lem-sfb-constructible-algcl-topology-comparison vs sk-thm-sfb-qlbar-two-colimit: the existing theorem compares finite fields with the finite-subextension-valued ring only; the new theorem compares that ring with the distinct all-norm-continuous ring through their inclusion.

lem-sfb-constructible-algcl-topology-comparison vs lem-sfb-continuous-algcl-stratified-finite-models: the existing theorem descends individual heart sheaves after a stratification; it supplies no comparison of derived Hom groups, extensions or entire derived objects. The new equivalence includes precisely those additional assertions.

lem-sfb-constructible-algcl-topology-comparison vs lem-sfb-normal-continuous-algcl-monodromy: the existing node is about lisse heart objects on connected normal schemes and continuous fundamental-group representations. The new statement includes singular standing schemes and higher morphisms of constructible derived objects.

lem-sfb-constructible-algcl-topology-comparison vs lem-sfb-condensed-coefficient-iso-constructible: the existing result assumes a ring-object isomorphism. The new map C to B is not an isomorphism, as the convergent-sequence example shows.

lem-sfb-constructible-algcl-topology-comparison vs lem-fd-rational-coefficient-category-comparison: the existing theorem compares two finite-field rationalization frameworks and their common-stage colimits. It does not change the topology on the coefficient algebraic closure or give the specified ambient-module derived scalar functor to B.

lem-sfb-constructible-algcl-topology-comparison vs lem-sfb-continuous-algcl-proper-scalar-comparison: the new theorem is an independent coefficient-category comparison, with no f and no pushforward, not a clause of the item. The item's geometric input is the already existing proper preservation for B, together with the already existing comparison for C. Steps 4--6 prove how restricted adjunctions and their canonical mates assemble those distinct inputs. Merely applying the new theorem would not establish the item's canonical-morphism assertion.

I searched the whole DAG for norm/colimit topology comparisons, finite-subextension plus full faithfulness/equivalence, the above candidate statements, and the whole blueprint using blueprint_refs search with 'coefficient topology', 'norm topology', 'topology comparison', 'continuous algebraic closure', and 'fully faithful constructible'. No existing node gives the new assertion. No Stacks tag is claimed for the new norm-topology theorem, hence there is no new same-tag pair to distinguish.

## Review by NA

I read the current chapter and unit, the main-20261015 direct-images proof paragraph (3), and the current proper-base-change proof, including its separate rational paragraph. For the coefficient issue I read Bhatt--Scholze Definition 6.8.1, Lemma 6.8.2 and the topology discussion, and Hemo--Richarz--Scholbach Definition 1.1, Theorem 4.13 as described in the introduction, Theorem 6.2, Theorem 7.7 and especially the paragraph immediately before Lemma 7.9. The latter explicitly fixes the colimit topology. I also examined the condensed-homotopy reference's warning 7.15: it rules out freely using ambient proper base change for arbitrary pro-etale sheaves. No such assertion is used here. These readings establish the scope of the existing results and why a new input is needed; none is claimed as a proof of the new topology lemma.

I opened and read the statements of every cited node. In step 1, sk-def-sfb-qlbar-condensed gives exactly the restricted sections defining C; alpha-iso applies to every condensed ring, hence to both C and B; the pd comparison preserves internal/section tensor, derived adjunctions and counits; and the ringed coefficient cocycle states both the balanced associator and the actual counit-mate comparisons without assuming flatness. I deliberately used alpha-iso rather than the admissible-only cartesian-coefficients theorem for B.

In step 2, extend-to-qlbar-constructible is used solely for the finite-subextension-valued C. Rational proper-base-change clause (2) gives P constructible; its clause (1) gives the canonical E-to-C comparison for the bounded-below input K. K is bounded by hypothesis, and f is proper in the standing setting. No part of that existing statement is applied directly to the all-continuous B.

In step 3, the new equivalence supplies constructibility of J_Z L and J_T P. Finite-type-over-Noetherian supplies the required Noetherian schemes over the field k. The continuous-algcl-constructible-tor theorem then supplies finite Tor amplitude, and continuous-algcl proper preservation is applied with that verified hypothesis. Its statement explicitly covers the all-continuous ring and bounded constructible finite-Tor objects, so it gives that Q is bounded constructible. No assumption of constructibility was added to the item: the proof derives it using named statements.

In step 4, upper-star-preserves gives constructibility of f_C^*M, so both uses of the new full-faithfulness assertion have objects in their specified domains. Module-derived-pushpull gives the two actual adjunction bijections. Kflat-scalar-comparison-normalization gives the exact inverse-image/tensor comparison, not an arbitrary isomorphism. I wrote out the image of J_Tu through the Hom chain, used naturality of sigma, and checked that it is composition with the defined counit mate. This is the critical canonical-map check, and requires no general claim that mates of arbitrary invertible squares are invertible.

Step 5 uses essential surjectivity on the full constructible subcategory, with both endpoints already proved to lie there. Surjectivity with test object Q gives a right inverse, and injectivity with test object J_TP gives the left inverse. This is a written elementary argument, not an uncited Yoneda theorem. Step 6 uses exactly the coefficient cocycle's displayed identity, with A_E to C to B. It proves invertibility of the original mate and identifies its normalization. The cocycle has no flatness hypothesis. All internal/ringed identifications used there were fixed in step 1.

I checked B1--B9: the new node is self-contained, statement-only, with every nonstandard notion either explicitly given or in stmt_deps; no proof sketch is inside the statement; TeX is singly escaped after JSON decoding; no unsupported Stacks tag or Mathlib match is present; the searches are actual logged msearch calls. The two semantic phrasings, Loogle, LeanSearch and Mathlib grep all returned no match. Loogle's equivalences present condensed categories on equivalent sites, not different coefficient rings. The grep's fullyFaithfulCompactlyGeneratedToCondensedSet concerns spaces, not derived constructible modules. Every search record copies its tool and query exactly. B10's attachment search found no exact closed project declaration.

For C1--C8, every non-elementary input is a cited statement, and citations.json copies those statements verbatim. In particular I did not infer a comparison from a definition, infer the norm topology from the finite-union theorem, or use only the proof of a dependency. I computed the current transitive dependencies of the existing major tools: none reaches this item, so the new proof introduces no back edge. The other-unit tools are declared with their reasons in split_report.tool_uses. This preserves the current unit's proper-image role; no trace-formula or Poincare-duality argument is substituted. The pd-named tool is a generic internal/section-module comparison.

For D1--D5, the new node is not a proper pushforward clause or a renaming of the item. The old C proper theorem and the old B proper-preservation theorem remain separate inputs, and the six steps contain the category argument and the exact composite-mate calculation. The unresolved issue is explicitly in the coefficient-category theorem. All proof steps are shorter than 2000 characters, with no hidden inverse, map normalization, or flatness assertion.

For E1--E7, I checked all geometric and coefficient hypotheses at the uses described above. The empty scheme and zero complex give zero comparisons. For f=id, the coefficient cocycle identifies all maps with the identity after unit multiplication. For a finite disjoint union of algebraically closed points, the new topology comparison reduces to extension between perfect complexes over the same scalar field Omega; there is no false equivalence of all condensed modules. At an algebraically closed point HRS Lemma 4.1 identifies the lisse finite objects with Perf(Omega), which supports that small case. These tests do not prove the new theorem for general schemes, which is why it remains unsplit and WANTED. I found no explicit counterexample to the assigned statement and did not mark it disputed. No source statement was silently changed and no SGA source is used.

## What remains

The assigned item is split by one level. The single new coefficient-topology comparison remains unsplit and requires a proof/reference; the delivery does not claim it is proved. The rest of the item is an explicit assembly from existing DAG statements. The preliminary server review_split check passed; full delivery dry-run results follow below when available.
