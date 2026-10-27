# Stage-1 report: lem-trf-regular-component-etale-stalk-primes

## Files written

- dag/nodes/sec-trace-formula/lem-trf-regular-component-etale-stalk-primes.json: statement item, now split into six steps; no Mathlib match for the whole statement.
- citations.json: twelve entries, one for every step/node pair, copying the cited node's statement verbatim.
- searches.jsonl: five new actual searches made by the authorized msearch command; all available. Earlier search records in the inherited item were preserved.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compilers, builds, repository writes, or git commands were used.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id, regular components, component primes, and étale stalk terminology found no declaration stating the whole item. AlgebraicGeometry.isRegularLocalRing_stalk_of_etale in AlgebraicGeometry/Regular.lean:96 supplies an ingredient only. Regular-local component results in Mathlib/RingTheory/RegularLocalRing/Defs.lean are likewise not the whole statement. No sorry declaration was counted as a proof.

## WANTED

None for the proof. The cited Stacks files are available locally. The inherited brief mentions coord/dag-sync.md, which is absent; the current direct-delivery instructions supply the applicable synchronization/delivery process.

## What needed correction

The item was genuinely unsplit (empty proof) and its statement is true as written. No statement, hypotheses, blueprint ancestry, or inherited source metadata were changed. Its inherited Tag 07NF is regularity ascent for smooth ring maps, not a complete reference for the component and contraction assertions. The new proof_origin and step sources identify the actual ingredients, including 0AH0 for the étale local regularity assertion and 05CK for injectivity.

The current latest blueprint ancestor lem-trf-local-term-locality is a contracting-correspondence local-term theorem. The item's inherited ancestry reaches that theorem through the normal-crossings/alteration technical route; the ancestor does not itself state this commutative-algebra lemma. I retained the inherited ancestry and explained precisely that technical role in split_report.blueprint. Neither chapter nor unit nor any target was changed.

The principal hypothesis issue to avoid is using lem-sfb-closed-component-stalk-calculus globally: it assumes a Noetherian scheme, whereas this item assumes locally Noetherian. Step 1 first chooses a Noetherian affine neighborhood from the locally Noetherian cover, restricts the reduced boundary and its components there, and only then applies that node. No global quasi-compactness is inferred.

## Search and reuse

Read the existing DAG nodes for closed-component stalk calculus, finite-intersection étale stalk models, étale stalk invariants, regular local domains, flat local maps, universally injective faithful flat maps, spectrum components/minimal primes, open-subspace irreducible-closed correspondence, and affine tensor pullbacks. Searches for 07NF, 00HR, regularity/domain language, minimal primes, component/stalk language and closed immersions found the existing tools. Blueprint searches for regular, regular component, minimal primes and étale stalk found no blueprint statement of the whole item; same_as stays empty.

The five new item searches are precisely the queries in searches.jsonl, copied unchanged into mathlib_searches. Two LeanFinder formulations returned étale-locus, localization, and finite-algebra infrastructure. Loogle with "IsEtale", "IsRegularLocalRing" returned no hits. LeanSearch returned Ideal.primesOver, localization minimal-prime statements, finite étale splitting and local-ring facts; these do not state the component-prime family theorem. The grep returned Properties.lean:218 and Geometrically/Reduced.lean:77; I opened both. The first concerns field stalks at generic points, and the second reducedness under a geometrically reduced flat map. Neither is an exact theorem or one-line specialization of this item.

## Not duplicates

No new nodes were created. In particular no local-component clause, étale quotient clause or faithful-flat contraction clause was repackaged as a new node. The existing lem-sfb-closed-component-stalk-calculus and lem-sfb-etale-stalk-invariants supply their explicitly stated general assertions.

## Review by Q73

I read delivery-errors B through E, including the repeated merged copy, with the node and Stacks source open. For the item I read algebra.tex Tag 07NF (lemma-regular-goes-up), more-algebra.tex 0AH0 (lemma-regular-etale-extension), algebra.tex 00NP (lemma-regular-domain), 05CK (lemma-faithfully-flat-universally-injective), 00ES (lemma-irreducible and the adjacent component-through-a-point lemma), schemes.tex 01J3 (lemma-reduced-closed-subscheme), 01I4 (lemma-fibre-product-affine-schemes), 01JU (lemma-fibre-product-immersion), and morphisms.tex 02GO (lemma-base-change-etale). I also read etale.tex 0BIA for the component/parameter interpretation, the topology.tex closure argument behind the open-subspace correspondence, and the surrounding Gabber Exposé VIII normal-crossings discussion. There are no new nodes needing separate source review. No SGA source is used.

Step 1 uses pqf-def-locnoeth for the affine Noetherian neighborhood. The open-subspace correspondence states both a bijection and preservation/reflection of inclusion, so it really does identify maximal irreducible closed subsets on restriction. Apply it to the space D and its open D intersect U. Reducedness is retained because def-pc-reduced-scheme defines it stalkwise. The closed-component calculus explicitly states the stalk-quotient formula, the bijection between components through the point and minimal primes over the stalk ideal, the intersection formula, and unit ideals for missing components. Its Noetherian hypothesis is met on U, even if X is not quasi-compact. Thus this citation uses the statement, not an argument hidden in its proof.

Step 2 applies the finite-intersection étale stalk model to a singleton D_a. This node explicitly gives the quotient R/p_a R as the ring of the closed pullback to Spec R and as the local ring at the unique point over w. Its point-membership assumption holds because a belongs to F_x. Its locally Noetherian and étale assumptions are exactly those in the item. No generalization from a closed point to all points is being silently made.

Step 3 uses étale-scheme-base-change for E_a to D_a. Étale-stalk-invariants explicitly asserts faithful flatness and the equivalence of regularity of the two local rings; it applies to this base-changed morphism. The definition of a regular scheme gives regularity of A/p_a. The regular-local-domain node states both nonzeroness and the product-zero criterion, which proves properness and primality of q_a. I do not assume that an arbitrary étale extension of a domain is a domain: it is this local quotient, with regular source stalk, to which the cited regularity theorem applies.

Step 4 uses the universal-injectivity statement for the faithfully flat quotient map from Step 3, with module equal to its source ring C. I wrote the two maps C tensor_C S to S and back, so this proves injectivity of the actual quotient stalk map and hence the exact contraction formula. Distinctness then follows from the distinct original minimal primes. The citation's statement gives injectivity for every module; it need not itself contain an ideal-contraction formula.

Step 5 is elementary from Step 1: the finite product of the component ideals is contained in their intersection, and a prime containing that product contains one factor. The contrapositive argument choosing one element outside the prime from every factor is written explicitly. It uses no flatness-preserves-intersections assertion. For no components I=A, so V(IR) is empty. No new lemma is hidden in this short ideal calculation.

Step 6 uses the affine closed-immersion description and the singleton case of the finite-affine-tensor-base-change statement. That statement permits arbitrary commutative base algebras, including R, and assumes no Artinianity or finiteness. The canonical pullback factors through the chosen open neighborhood; this is restriction to an open, not an inference of factorization through a closed subscheme from set containment. The explicit tensor/quotient isomorphism is written with both directions. The unit stalk ideal from Step 1 therefore makes its ring zero and its scheme empty.

For B, the item remains self-contained, definitions are cited in stmt_deps, and no new statement-only nodes or new leaves have formatting/source/line obligations. TeX is single escaped after JSON decoding. For C, I opened every cited node and copied exact statements into citations.json; proof_deps is the union of step uses. I checked the transitive dependencies of the main reused nodes do not return to this item. Off-unit generic tools have individual reasons in split_report.tool_uses; none replaces the unit's local-term argument. For D, the proof carries the assembly and elementary algebra, with zero new clause-restatement nodes. For E, no extra global Noetherian, excellence, henselian, Cartier, dimension, separable-closed-residue-field or connectedness assumption appears.

I tested: empty D or x outside D (F_x empty, I=A); a single regular component; the identity étale map; two coordinate axes meeting at x (distinct quotients and contractions); and an étale cover whose component pullback is globally disconnected. The latter is harmless because the ring used is the local ring at w. The case D=X irreducible regular gives p=0 and the usual regular local étale domain assertion. A globally non-quasi-compact locally Noetherian X is handled on U. These checks found no statement dispute. All six steps are shorter than 2000 characters, so none triggers the long-step review threshold.

## Unfinished work

No mathematical work remains in this stage-1 split. The reused unsplit statement nodes remain their own independent tasks; they were not edited or silently treated as proved Lean declarations. The required server preflight and final push are performed after this report is written.
