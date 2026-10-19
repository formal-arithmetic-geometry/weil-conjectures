# Worker report

## Files written

- dag/nodes/sec-smooth-purity/thm-fin-proper-constructibility-complete.json: item, statement, split into six steps; no Mathlib match.
- citations.json: every citation of every step, with the cited statement copied verbatim.

No new nodes or Mathlib leaves. The item is not the key statement of sk-prop-sf-cbc, so no unit realization record is changed.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 by the blueprint id, proper/constructibility phrases, and rightDerivedLowerStar names. Read SixFunctors/Etale/Derived/Finiteness/DirectImage.lean: the general bounded-constructible direct-image theorem has a sorry, and the derived wrappers use it. These are not completed attachments. No upstream master sorry declaration was treated as a finished proof.

## WANTED

None: the blueprint and Stacks sources used are available locally.

## Corrections and limitations

The imported statement is retained, read with the finite allowable coefficient convention of def-finrepair-property-c. Its predicate has no uniform cohomological vanishing assertion. The finite-components node only states finiteness of components assuming Noetherianness; it cannot establish that the schemes are Noetherian. Replaced that use with finite-type-over-Noetherian and the minimal-closed-subset node. Added the actual locality statements and properness/reduction hypotheses. The projective and modification cases remain cited statements to be split by their owners; this delivery does not claim their proofs are closed.

The source is an agent-written blueprint proof, so proof_origin remains agent, despite the supporting locality and geometry results being read in Stacks. The unit has no steps and is a compact-support base-change statement, not this theorem. Its route has not been replaced.

Mathlib queries ran through msearch.py, with two semantic phrasings, Loogle and grep. LeanFinder's hits were Chevalley's theorem on constructible subsets and underived module pushforward, neither the higher direct images of finite-coefficient etale sheaves. LeanSearch returned HTTP 500 and is recorded unavailable. Queries are recorded exactly in the item and searches.jsonl.

## Not duplicates

No new nodes. Searched the whole DAG by statements and ids for constructible locality, etale restriction, Noetherianness, closed proper restrictions and reductions, and blueprint_refs.py for constructibility, proper direct-image, minimal element and derived restriction. Reused existing nodes instead of creating variants. No other blueprint node was found stating this exact item in a distinct form.

## Review by NB

I read the item's complete blueprint proof and the chapter/unit records, then opened every cited node's statement. I also read the complete blueprint statements/proofs of lem-fin-noetherian-chow-modification and lem-finrepair-modification-c, Stacks morphisms.tex 01T6 (lemma-finite-type-noetherian), properties.tex 01OV/01OY/01OZ (definition-noetherian, lemma-locally-Noetherian-quasi-separated, lemma-Noetherian-topology), etale-cohomology.tex 095E (lemma-constructible-quasi-compact-quasi-separated), and morphisms.tex 054M (lemma-reduction-universal-homeomorphism). There are no new nodes whose sources need separate checking.

Step 1 uses the predicate's exact finite-module coefficient convention, the finite-type-over-Noetherian statement and locally-Noetherian/quasi-separated statement. The field is Noetherian by its two ideals; finite type and quasi-compactness are the given hypotheses, not inferred from the finite-components lemma. Step 2 uses proper-base-change for the restricted morphism, derived-open-restriction for the actual small etale finite-module D+ categories, and the open-local equivalence of 095E for the higher-image sheaf. I checked that the target is qcqs before 095E, and the ring is finite (hence Noetherian). Restricting a finite partition and presenting principal localizations as k-algebras supplies the elementary constructibility/finite-type details. No ordinary O_X-module restriction node is substituted for an etale one.

Step 3 uses the closed-immersion-proper node's explicit composite clause and the minimal-closed-subset node's actual minimal-element assertion. The induction property quantifies over all constructible sheaves and all q for each reduced closed subset, so the complement in step 5 has exactly the property the transfer lemma requests. Empty X or empty Z gives the zero sheaf category, and the zero sheaf has a constructible partition. No induction on components or on a dimension bound is assumed.

Step 4 applies Chow modification only to a reduced Z over an affine Noetherian S. Its statement really supplies an isomorphism over a dense open and a projective composite, not just a quasi-projective modification. The projective theorem is used only after Y is seen to be finite type over k from projective affine charts. Step 5 uses the modification lemma exactly with f_Z, pi and the reduced complement W: properness, finite type and the isomorphism-over-U hypothesis are all present; the two C predicates are obtained in step 4 and by minimality. Density ensures W is proper even when Z is reducible. This is an induction argument, not a new lemma restating the item.

Step 6 uses the reduction-universal-homeomorphism statement to verify the hypothesis of topological invariance. That invariance explicitly identifies inverse/direct images and cohomology. Its equivalence passes to finite coefficient module objects by retaining scalar actions, and exact equivalences preserve injective resolutions. The enough-injectives node supplies embeddings into injectives in the actual constant-coefficient module category; iteration through cokernels gives the resolution. The inverse-image-modules-exact statement identifies the constant coefficient rings, lifts inverse image to modules, and states its exactness, also used when taking cohomology in step 2. The direct-image definition provides the evaluation formula used to identify f_*r_*I with (fr)_*I term by term; the equality is written rather than hidden behind transport. The constructible partition definition justifies restriction to the reduction. This works for a nonreduced scheme such as Spec(k[epsilon]/epsilon^2), for the empty scheme, for the zero coefficient ring, and for q=0. None of those cases requires dropping higher direct images of an arbitrary modification pullback.

I checked C1/C4 by reading all the cited statements, and copied their statements into citations.json without bending quotes. B1-B9 are vacuous for new nodes; the item's searches actually ran and unavailable was distinguished from absence. D1-D5 are addressed by the minimal-counterexample induction and the explicit resolution calculation. E1-E7 were checked through the affine, Noetherian, reduced, proper, finite-type and finite-coefficient hypotheses above. Off-unit generic tools are declared in split_report.tool_uses; the existing Chow/projective/modification route remains intact. No cited dependency has a path back to this item in the current DAG.

## Unfinished work

None for this one-level split. The second reader must independently review and deliver; this worker runs only --no-push.

Final self-review correction: explicitly cited prop-weil-pbc-inverse-image-modules-exact in steps 2 and 6 and lem-weil-pbc-module-sheaves-enough-injectives in step 6, after opening their full statements. This removes any reliance on an abelian-only enough-injectives interpretation. The first dry run passed; the corrected version was dry-run again.


## Second reading by NB

I independently opened the item, all 19 distinct cited statements (including its statement dependencies), the finite allowable coefficient convention, and the blueprint sources for the item, Chow modification, modification transfer, projective constructibility and derived open restriction. The item agrees verbatim with its blueprint theorem, order 1621. Its finite ring is annihilated by a positive integer invertible on the coefficient schemes, as required by def-finrepair-property-c through sbc-def-coefficient-conventions; the assertion is per degree and does not assert uniform vanishing. No statement dispute was found.

- Step 1: checked against def-finrepair-property-c, Stacks 01T6 (morphisms.tex, lemma-finite-type-noetherian), 01OV (properties.tex, definition-noetherian) and 01OY (lemma-locally-Noetherian-quasi-separated); finite type over a field supplies exactly the required Noetherianness, quasi-compactness and quasi-separatedness. PASS.
- Step 2: opened proper-base-change, derived-open-restriction, inverse-image-modules-exact, constructible-complexes and constructible-qcqs-affine-local; checked Stacks morphisms.tex lemma-base-change-proper and etale-cohomology.tex 095E (lemma-constructible-quasi-compact-quasi-separated). The derived comparison is in the actual constant-coefficient module category; exactness gives the stated cohomology comparison, and 095E applies on qcqs S. Added the minimal-closed-subset citation and a two-line finite-union/complement argument proving open quasi-compactness, which the finite principal-open chart argument needs. PASS after repair.
- Step 3: checked closed-immersion-proper against Stacks 01W5/01W3 (lemma-closed-immersion-proper/lemma-composition-proper), and the minimal-subset statement against 01OZ (properties.tex, lemma-Noetherian-topology) and topology.tex 0051 (definition-noetherian). The induction quantifies over every constructible sheaf and every nonnegative degree; quotient charts give finite type. The empty source has only the zero module sheaf. PASS.
- Step 4: opened lem-fin-noetherian-chow-modification and thm-fin-projective-constructibility-complete and their blueprint sources. The former supplies exactly proper pi, dense U, an isomorphism above U, and a projective composite for reduced Z over affine Noetherian S. Added def-pc-projective-morphism, whose actual closed-embedding convention gives the finite projective chart cover and quotient polynomial algebras used to check Y is finite type over k. All coefficient invertibility conditions pull back along the structural maps. PASS after repair.
- Step 5: opened lem-finrepair-modification-c and its complete blueprint proof, including the two C hypotheses in its statement. Density makes the complement proper even for reducible Z; its reduced induced structure is the same whether formed in Z or X. Proper pi is finite type by the proper definition. The two predicates are supplied by step 4 and minimality, so no acyclicity of an arbitrary modification pullback is asserted. PASS.
- Step 6: checked reduction-universal-homeomorphism against Stacks 054M (morphisms.tex, lemma-reduction-universal-homeomorphism), topological invariance against etale-cohomology.tex theorem-topological-invariance, inverse-image-modules-exact against sites-modules.tex 04JC (lemma-flat-pullback-exact), and module-sheaves-enough-injectives against injectives.tex 01DU (theorem-sheaves-modules-injectives). Read the full module clause of direct-image. Expanded the scalar-action construction, the pulled-back trivializing cover, and the monomorphism extension proof that r_* preserves injectives. The termwise direct-image identification includes restrictions and differentials, so taking cohomology proves the required higher-image isomorphism. PASS after repair.
- New nodes: none; checked the sandbox node inventory. B1-B7 and searches for each new node are vacuous. No node restates a clause of the item, and no elementary auxiliary node needs removal. PASS.

Small cases checked: empty X and empty closed induction subset, zero sheaf and zero coefficient ring, the identity of Spec(k), a nonreduced Spec(k[epsilon]/epsilon^2), q=0 and q=1, and projective dimension r=0 or r=1. Empty strata and vanishing cohomology remain allowed. For a disconnected reduced Z, density still makes W proper; the Chow statement is used only for its statement, not its problematic proposed dense-intersection construction. These cases introduce no extra hypothesis or omitted conclusion.

I ran an independent Mathlib grep through msearch.py with `IsProper.*(Constructible|constructible)|higherDirectImage|higher_direct_image`; it returned zero hits and the raw search is retained in searches.jsonl. I read DirectImage.lean lines 75-138 in the read-only slopmaster2 source: its more general constructible direct-image input still has sorry and cannot be a finished attachment. No compiler, Lake, source edit, or direct git command was used. A read-only dependency traversal of statement and proof edges found no path from any cited dependency back to the item.

Changes: added two existing-node citations (Noetherian minimality in step 2 and the projective definition in step 4); wrote the open quasi-compactness argument, module-action and injectivity arguments, and pulled-back trivializing-cover argument explicitly; regenerated citations.json as verbatim full statements for every repaired citation; updated proof_deps and the split summary. The statement and the first worker's sections, including Review by NB, are retained. No new nodes or Mathlib leaves.
