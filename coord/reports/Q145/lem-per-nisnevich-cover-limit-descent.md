# Q145: lem-per-nisnevich-cover-limit-descent

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-nisnevich-cover-limit-descent.json`: item, statement unchanged, split into seven steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-cd-finite-presentation-section-cover.json`: one new statement-only node, Stacks Tag 0GTL (`more-morphisms.tex`, `lemma-decompose`); searched and unsplit, no Mathlib match.
- `citations.json`: one verbatim statement quote for every step/node citation.

There are 1 new nodes and 0 Mathlib leaves. No unit or chapter record is changed. No Lean is written, and no compiler, Lake or build command is run.

## Attachments

None. Searches of the live `lean/WeilConjectures/` for the item id, Nisnevich, completely decomposed and splitting sequences found no declaration of this assertion. `lean/Sheaf/AlgebraicGeometry/PrimeToEllAlterationTopology.lean` defines a completely decomposed family but does not prove this descent statement. Existing declarations with sorry are not treated as finished results.

## WANTED

None. The ILO PDF and the Stacks source used below are present locally.

## Corrections and unfinished work

No statement dispute or change. The original item had an empty proof. Its ILO reference is accurate: Expose III Lemma 3.1.1, printed p.38, proves eventual Nisnevich covering by finite section strata. The source's word “immediately” suppresses the object, arrow, equation and property descent needed here. The split supplies those operations through existing nodes, keeping the given models rather than choosing unrelated replacements.

The new node is the non-limit finite section certificate, not the descent assertion or a clause of it. It is left statement-only as required. Its future proof is the explicit argument in Stacks 0GTL: approximate residue-field points by finitely presented immersions, factor each point lift using local finite presentation, and choose finitely many resulting constructible images by constructible compactness. That proof is not copied into its statement or proof fields.

## Searches and reuse

Read the current blueprint symlink `literature/blueprint/latest` (main-20261024), specifically the ancestor `lem-per-artin-gabber-affine-curve` statement/proof and the chapter/unit records `sec-deligne-laumon-a1` and `sk-p-dl-a1-perverse`. This item supplies the recorded III 3.1 approximation input on the ancestor's Step 3 finiteness/duality branch. It changes neither chapter nor unit route.

Whole-DAG searches covered completely decomposed morphisms, Nisnevich, splitting sequences, finite closed filtrations, sections over locally closed pieces, the existing inverse-limit/descent tools, and Stacks 0GTL/0GTM. `tools/blueprint_refs.py search` was run for Nisnevich, filtration sections, completely decomposed, Nisnevich filtration, 0GTL, stratification section, immersions sections, and finite closed filtration. No imported blueprint node states the new certificate. The rational-lift and finite-subcover nodes are related but do not give a finite cover by finitely presented immersions for arbitrary qcqs targets. The existing algebraic-space splitting filtration chooses a particular etale presentation of an algebraic space and is not a splitting certificate for the fixed morphism in this item.

All new Mathlib searches were executed through the prescribed msearch command and are recorded in `searches.jsonl`. Read every hit. LeanFinder returned Noetherian schemes and finite components, local spreading of individual maps, ordinary open covers and finite-presentation definitions; LeanSearch returned ordinary finite open subcovers, immersion definitions and ring/module filtrations. Loogle returned no hits for the two relevant class combinations. The grep hits for Nisnevich are explanatory comments in `MayerVietorisSquare.lean`, not a scheme theorem. The flat descent instances in `LocalFlatDescent.lean` concern faithfully flat descent, not eventual residue-field lifting. Read the candidate `spread_out_of_isGermInjective'` in `SpreadingOut.lean`: it extends one stalk map and does not construct the certificate or descend a covering. Read the relevant Noetherian and etale source definitions as well. Tried alternative plain-language phrasings before concluding no match. No service failure was classified as a negative result.

## Not duplicates

lem-per-cd-finite-presentation-section-cover vs lem-per-rational-lift-locally-closed-section: the existing statement gives one locally closed lift through one rational point over a Noetherian target; the new result gives a finite covering by immersions of finite presentation for any qcqs target and a locally finitely presented completely decomposed morphism.

lem-per-cd-finite-presentation-section-cover vs lem-per-completely-decomposed-etale-finite-subcover: the existing result selects finitely many members of an existing etale family over a Noetherian scheme; it does not construct section-bearing finitely presented immersions, and the new result does not select members of a family.

lem-per-cd-finite-presentation-section-cover vs lem-sfb-qcqs-space-splitting-filtration: that existing result constructs some schematic etale presentations of an algebraic space with prescribed trivial closed strata; it makes no assertion about sections of a given completely decomposed morphism.

There are no existing DAG nodes citing Stacks 0GTL or 0GTM in the source metadata searched before creation.

## Review by Q145

I read ILO Expose III Lemma 3.1.1 and its full proof on printed p.38 (the PDF text at the III approximation chapter). The proof describes a finite closed filtration with sections on the differences and then descends this finite data. I also read all four clauses and the proof of Stacks 0GTL (`more-morphisms.tex`, `lemma-decompose`) for the new node, and the complete proof of 0GTM (`lemma-descend-cd`). The latter makes explicit that one may work with a finite section-bearing immersion cover rather than insist on a nested closed filtration. This implements the same section-certificate route. I read the local source statements for Tags 01ZM, 01ZP, 0EUU, 07RP and 07RR, and the Noetherian finite-type/finite-presentation facts in `morphisms.tex`, `properties.tex` and `algebra.tex`.

For step 1, I opened the statements of finite-type-over-Noetherian, locally-Noetherian-quasi-separated, finite-type-Noetherian-finite-presentation, and qcqs-morphism-permanence. The first supplies Noetherian model objects, the second their quasi-separatedness, the third the actual finite-presentation upgrade of coordinate-ring maps, and the fourth quasi-compactness/quasi-separatedness and base-change permanence. I wrote out the generator argument showing a map between the specified finite-type models is locally of finite type. Thus none of the later descent tools is applied merely on the assumption that a morphism exists.

For step 2, the affine-transition limit statement identifies Spec of the ring colimit with the scheme limit, and scheme-over-limit identifies the actual prescribed P models with the base-changed limit system. The etale descent statement requires exactly qcqs model objects and a locally finitely presented model map; step 1 establishes those hypotheses. The etale scheme base-change statement is the source of the all-later-stages assertion, not an unstated strengthening of single-stage descent.

For step 3, the scheme-coproduct statement supplies open, disjoint components covering V. On these components local finite presentation is already known. The new certificate statement supplies both the covering immersions and the actual maps into V with their equations; neither is taken from its proof. Splitting each certificate by the finitely many coproduct components assigns a particular j(a), so later descent never requires a map to an unmodelled coproduct. The Noetherian and qcqs-permanence tools ensure these pieces remain quasi-compact and finitely presented. I also opened and cited lem-sbc-locally-finite-presentation-composition (Mathlib leaf, Stacks 01TR) for the composite local finite presentation after component restriction. The closed-immersion restriction is justified by its local idempotent quotient description. All schemes are allowed to be nonseparated.

For step 4, the closed-immersion definition explicitly gives a closed-then-open factorization. I retain the source of the closed immersion when restricting its open target. The quasi-compact source allows the finite affine shrink, so no arbitrary open is assumed quasi-compact. The local finite presentation of an open immersion follows from its principal-localization charts. The cited family-descent statement supplies objects with cartesian comparisons and no arrows; the proof does not attribute arrows or immersion properties to it.

For step 5, the finite-diagram-lift statement supplies arrows and exact path equations among the previously modelled finitely presented objects. I include the given V_j and P objects with their original models, so it preserves the prescribed v_j after base change. The relation is v_j s_a = o_a c_a, not just equality after taking residue fields. The model base is P_alpha, a qcqs affine-transition limit system by steps 1–2. The new objects are finite type over S_alpha, so the step-1 affine calculation applies again to their maps.

For step 6, I checked each property-descent statement's source and target finiteness hypotheses and its particular conclusion. Closed-immersion descent requires local finite type; open-immersion descent requires local finite presentation. Both have been verified. Persistence of the closed maps comes from the separate closed-immersion-base-change statement; persistence of the open maps is explicitly in the open-immersion descent statement. The finite-family-joint-surjectivity-stage statement applies to arbitrary locally finitely presented arrows between finitely presented models, not just etale arrows, and explicitly permits an empty family. It gives every later stage. Thus I use it only for joint surjectivity, not for rational residue fields.

For step 7, I checked the closed-immersion-residue-field statement gives the induced residue-field isomorphism, the open-immersion definition gives equality of local rings, and the residue-field definition gives the maps of fields. I wrote the elementary retraction argument: the composite kappa(p) -> kappa(z) -> kappa(t) is an isomorphism; after identification it is a retraction, and injectivity of a unital field homomorphism forces the other composite to be the identity. This proves the required isomorphism for the actual canonical map, with no unjustified factorization from containment of images.

I tested the new certificate on an empty target (n=0), the identity (one stratum), a field target with a rational lift (one field-valued section), and nonreduced targets (finite-presentation immersions may retain nilpotents; no reduction is silently imposed). For the item I checked empty family/empty target, a limit target that becomes empty only eventually, redundant or empty members, nonseparated finite-type models, and rings with noninjective transition maps. The argument uses no faithful flatness, injectivity of ring transitions, separatedness, or finite Krull dimension. The empty limit is handled by the existing eventual joint-surjectivity lemma, so it is not assumed that the original model was empty. Every non-elementary input is a cited statement and every cited statement has been opened; citations.json contains verbatim quotes. All steps are shorter than 2000 characters. No new node is an elementary reformulation, a duplicate, or the original item's conclusion. The off-unit tools are declared individually in split_report.tool_uses; they serve only the generic finite-data descent operations the source requires.
