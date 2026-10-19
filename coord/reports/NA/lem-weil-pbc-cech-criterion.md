# Stage-1 report: lem-weil-pbc-cech-criterion

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-cech-criterion.json: statement, six proof steps, split; searched Mathlib, no exact match. No new nodes and no new Mathlib leaves.
- citations.json: a verbatim statement quotation for every proof-step citation.

## Attachments

None. Searched the slopmaster2 project for the blueprint tag and Cech/vanishing/criterion notions. CategoryTheory.Sites.CechCriterion proves an abelian-sheaf criterion, with a terminal object and its own explicit family hypotheses; it does not state both clauses of this general ringed-site module result. The module-presheaf cocycle lifting declarations are already assigned to existing nodes. Master sorry declarations are not evidence of completion.

## Wanted literature

None. Read the imported blueprint node and Stacks sites-cohomology.tex: 03F9 (lemma-cech-vanish-collection), 03F8 (lemma-ses-cech-h1), and 03FB/03FC (lemma-injective-module-injective-presheaf / lemma-injective-module-trivial-cech); also 03FA and 03FD to distinguish the coefficient categories. The dimension-shifting proof is 03F9 carried out directly in modules, so it does not require a new general module/abelian cohomology comparison.

## STATEMENT-DISPUTED: general-site definition references

The imported general-site statement cited def-weil-pbc-cover-cech, whose current statement introduces a scheme and restricts to its small etale or pro-etale site, and def-weil-pbc-etale-cohomology, whose current statement introduces an etale abelian sheaf on a scheme. On a general ringed site (for example the singleton site with coefficients an arbitrary ring) those references do not provide the claimed module-derived evaluation groups. This is a scope/type mismatch, not a counterexample to the mathematical assertion. Replaced them with the existing general-site Cech definition and the generic right-derived-functor definition, and explicitly introduced the ring sheaf and evaluation in module sheaves. The two vanishing conclusions and finite-cover hypothesis are unchanged. The smallness/common-universe convention is the standard meaning of the set-based site and coefficients, needed by the cited module-presheaf theorem; no independent smaller coefficient universe is asserted. Rings need not be commutative.

The imported proof also assumes a coproduct V of cover objects exists in the site. General sites need not have such coproducts. The existing tuple-based presheaf cocycle lifting result avoids that unnecessary construction and carries the first paragraph's free-module/Hom argument. This does not alter the unit or chapter route.

## Unfinished work

None for the one-level split. Every non-elementary input is an existing node; those nodes retain their own status. This delivery does not claim that the complete transitive DAG is finished.

## Not duplicates

No new nodes. Searches of the whole DAG, Stacks tags 03FB, 03FC, 03F5, 03AS, 03FD, and blueprint searches for Cech, ringed site and enough injectives found the existing general ringed-site tools. The existing site-cech-vanishing-criterion concerns abelian-sheaf cohomology; module-cech-vanishing-criterion concerns the Zariski site of a scheme and all open coverings. Neither is silently identified with this finite-basis ringed-site module statement. The item's blueprint.same_as is empty: the whole-blueprint Cech search found no other imported node stating both clauses here.

## Review by NA

I read the chapter sec-proper-base-change and the unit sk-thm-properbasechange before auditing the node. This auxiliary acyclicity argument is below that unit; it does not replace any of the three unit steps. Its first paragraph realizes injective Cech vanishing, and its second realizes finite-cover lifting and dimension shifting. No unit realization fields need changing because this is not the unit's key statement node.

For step 1 I read def-weil-pbc-site-cech-complex: its ordered tuples and alternating restriction formula give exactly the complex used. The basis assumption supplies all intersections, including repeated indices, and the refinement assumption supplies cofinality; neither is inferred from an unrelated compactness theorem. For step 2 I opened the statements of ringed-site-injective-module-injective-presheaf and injective-presheaf-module-cech-cocycle-lift. The first gives injectivity in module presheaves and the second gives a primitive for every positive cocycle; substituting q=p-1 is legitimate for p>0. Its common-universe restriction is now explicit. Read 03FB and 03FC against these statements. This uses no points of the topos and no coproduct in the site.

For step 3 I read ring-sheaves-grothendieck (arbitrary rings, small site, common universe), grothendieck-enough-injectives (every Grothendieck abelian category), and the definitions of module sheaves and module-presheaf sheafification. These really give the embedding and cokernel used here. In particular the latter definition takes the abelian sheafification and extends the module action, while the former computes kernels sectionwise and cokernels by sheafification. Thus forgetting this particular short exact sequence is exact for the stated reason, without claiming that forgetting preserves injectives. I read Injectives 01DU, the module embedding theorem, and the project SheafOfModules.isGrothendieckAbelian implementation as a further check of the general ringed-site input.

For step 4 I opened site-ses-cech-h1-surjective: it asks for a short exact sequence of abelian sheaves, a cofinal covering collection at U, and vanishing H1 of the kernel on that collection. Step 3 and the hypotheses meet all three. I also checked its 03F8 proof against the written difference cocycle: with differential b_b-b_a, c_ab=i_b-i_a and delta c=0, subtracting b_a from i_a produces agreement. The sheaf axiom glues the adjusted lifts, and sectionwise kernels supply left exactness.

For step 5 I read complex-ses-homology-long-exact, whose hypothesis is degreewise short exactness. Every degree is a finite product over finite ordered tuples, so selecting coordinate preimages proves surjectivity directly; no product-exactness lemma is hidden. Naturality ensures a complex sequence. The exact segment H^p(I)->H^p(Q)->H^(p+1)(A) has zero outside terms for p>0. This checks the quotient invariant required for induction, rather than assuming it. Source: 03F9 proof and Homology 0117.

For step 6 I opened both derived-functor-long-exact and derived-functor-injective-vanishing. Their category must be abelian with enough injectives, supplied in step 3, and their evaluation functor additive and left exact, proved from sectionwise kernels. They therefore apply in module sheaves. The argument uses surjectivity at degree zero, vanishing of the positive derived evaluations of I, and the isomorphism for q>1; it explicitly inducts on the degree for every sheaf with the Cech invariant, so applying the induction hypothesis to Q is valid. Source: 03F9 final argument and Derived Categories 015B. No assumption that the underlying abelian injective is injective enters this argument.

I checked delivery-errors B–E against the written split. No new elementary, duplicate, or clause-restatement nodes exist; every non-elementary fact is cited, and citations.json quotes the actual statement of each cited node. All off-unit nonclosed tools are declared in split_report.tool_uses as generic homological or ringed-site tools. Definitions have the required scope. Cech complexes are nonnegative, p>0 is translated to q=p-1 only where valid, and dimension shifting is used only for q>1.

Small cases: for a one-member identity cover the alternating complex has differentials 0,id,0,id,... and zero positive cohomology, as expected. For an empty covering of an object, the sheaf axiom forces sections there to be zero; every Cech group there is zero, and the section-surjectivity step remains valid. For the zero sheaf every step gives zero. A repeated member is allowed because all ordered tuples are used. A site in which every basis covering splits has vanishing evaluation cohomology by the same argument. With Z/n coefficients the underlying additive sheaf of a module injective is not assumed injective; keeping the resolution in modules avoids that invalid inference.

Mathlib searches were run only by msearch.py and read as returned. LeanFinder found K-injective and derived-functor results and sheaf cohomology definitions, not this theorem. Loogle's cech/injective hit was a Stone-Cech embedding, unrelated; the second cechComplex query found only the complex definition. I read Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean, which constructs the complex but gives neither vanishing assertion. Both phrasings were searched. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. No unavailable service is reported as mathematical absence.

## Second reading by NA

- Statement: checked against the imported blueprint node and Stacks Tag 03F9, including the ringed-site, basis, finite-refinement, injective-vanishing, and derived-evaluation clauses; verdict: agrees after the recorded general-site scope correction.
- Step 1: checked against the Cech-complex definition and 03F9 assumptions (1)--(2); verdict: cofinal finite refinements and iterated fibre products are stated explicitly, with no coproduct assumption.
- Step 2: checked against the statements of the injective-presheaf and cocycle-lifting nodes and Tags 03FB/03FC; verdict: the q=p-1 application is valid for p>0 and the universe condition is explicit.
- Step 3: checked against the Grothendieck, enough-injectives, module-category, and module-sheafification node statements; verdict: the short exact sequence and underlying abelian exactness use only stated kernel/cokernel facts.
- Step 4: checked against the stated Cech H1 surjectivity lemma and Tag 03F8; verdict: local lifts, the difference cocycle, its cocycle identity, correction, and gluing are all written.
- Step 5: checked against the Cech-complex definition and complex long-exact-sequence node; verdict: finite-coordinate surjectivity gives degreewise exactness and the two vanishing outer terms give quotient vanishing.
- Step 6: checked against the left-exact evaluation definition and both derived-functor nodes; verdict: degree-zero surjectivity, injective vanishing, and induction on q are correctly applied in module sheaves.
- New nodes: none; therefore B1--B7, duplicate searches, and Mathlib-leaf checks have no new-node cases.
- Edge cases: checked zero modules, one-member identity covers, repeated indices, empty covers, and arbitrary (including noncommutative) coefficient rings; verdict: no altered clause is exposed.

Changes made during second reading: none. The worker's recorded general-site statement correction, explicit universe convention, removal of the unnecessary coproduct assumption, and citation quotations were rechecked and retained.
