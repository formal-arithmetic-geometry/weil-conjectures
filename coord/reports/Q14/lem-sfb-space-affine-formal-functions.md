# Q14: lem-sfb-space-affine-formal-functions

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-formal-functions.json: item, statement, split into twelve proof steps; no Mathlib match.
- citations.json: twenty citations, each quoting the cited node's statement verbatim.
- report.md: this report. searches.jsonl contains the actual search-command records. write_split.py is a sandbox-only JSON assembly helper, not a repository tool.

Zero new nodes, zero Mathlib leaves. The item's statement, statement dependencies, source, inherited blueprint fields and old search records are retained. Only proof, proof dependencies, proof origin, status, split report and additional actual search records are supplied.

## Attachments

None. Searched the live WeilConjectures source by the exact blueprint tag and by formal-functions terminology. TheoremFormalFunctions.lean states AlgebraicGeometry.theorem_formal_functions for Scheme and Zariski module cohomology, not proper algebraic spaces on their small etale ringed sites; it does not state this item. Related ML declarations likewise concern schemes. No project declaration found gives this item in full.

## WANTED

None.

## Corrections and source observations

The item was statement-only, with no proof. Its statement is correct, so it is unchanged. The proof now derives eventual image stabilization and the kernel estimate instead of citing the scheme-only lem-weil-pbc-ml-cohomology-powers-ideal. It uses existing geometric, algebraic and homological inputs, not a new node restating formal functions.

Read spaces-cohomology.tex Situation 08AV, 08AX (lemma-cohomology-powers-ideal-application), 08AY (lemma-ML-cohomology-powers-ideal), 08AZ (theorem-formal-functions), and the last paragraph of 08B1 (lemma-formal-functions-stalk). The 08AZ proof omits verification of an inverse identity: steps 10 and 11 give the explicit lift modulo I^n and prove both identities. The 08AY proof's bound on m must be converted to a bound on the source index r=n+m: step 9 uses r >= 2n+b+d_n. No uniform Artin-Rees constant in n is asserted.

The final paragraph of 08B1 writes H^p(X,i_{n,*}F) where the typed expression is H^p(X,i_{n,*}F_n); the preceding line identifies this with F/m^nF. Step 3 uses the typed expression j_{n,*}F_n=F/J^nF. This is a notation correction in the source proof, not a change of the item's statement. The chart formula uses tensor quotient P/I^nP, without flatness and without claiming the finite-level cohomology maps are isomorphisms.

## Not duplicates

No new nodes were created. Searches of the entire DAG for 08AY, 07UH, formal functions, Mittag-Leffler, ideal-power cohomology, affine cohomology and Artin-Rees located the existing inputs. tools/blueprint_refs.py search 'formal functions' found only pqf-lem-fff-vanishing (a scheme vanishing theorem, not this statement); search '08AY' found none; search 'Mittag' found the finite-abelian-group Mittag-Leffler result, not coherent cohomology. The ancestry command returns blueprint.from.node = null for this inherited branch. I preserved that ancestry and its detailed place/via chain rather than inventing an imported ancestor.

In particular lem-sfb-space-infinitesimal-section-image-stabilization only states degree-zero sections of a line module over a local ring, so does not cover the current arbitrary degree/coherent module/general ideal. lem-weil-pbc-ml-cohomology-powers-ideal is scheme-only. The existing space image-bound node is exactly the reusable 08AX estimate, and its statement was read, not just its proof.

## Mathlib searches

The sandbox log records the actual leanfinder, loogle, grep and leansearch commands. Two natural-language formulations of formal functions returned affine-transition-limit scheme section results, completion infrastructure and local cohomology; none states the item. Additional formulations for the cohomological kernel/image estimate returned localCohomology, completion coordinate formulas and ordinary module Artin-Rees. The Artin-Rees hit is already represented by lem-weil-pbc-artin-rees and is reused, not recreated. Read Mathlib/Algebra/Homology/LocalCohomology.lean: its cohomology is an Ext colimit with ideal support, not coherent cohomology on a proper algebraic space. Loogle's completion/cohomology and MittagLeffler/cohomology conjunctions have no hits. Grep's 'formal functions' hits are unrelated monoid algebra and complex conformality.

The additional estimate searches were exploratory: there is no new estimate node because steps 5-9 carry its argument using the existing cited inputs. All new search entries match the command log exactly; old supplied search history remains intact.

## Review by Q14

I read the live item, its unit and chapter, the three-level rule in SETUP, GOAL, the worker/stage-1 contract and delivery-errors B-E, and compared the route with literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images.proof.md (latest snapshot recorded as 7284bb09). The inherited alteration branch reaches algebraic-space formal functions as a supporting input. This work stays on that branch. No Lean was written or compiled and nothing in the shared repository or launcher was changed.

For step 1 I opened lem-sfb-space-flat-proper-fp-locality, pqf-lem-locnoeth-lft, def-weil-pbc-noetherian-ring and lem-sfb-space-coherent-abelian. The first supplies chartwise finite type from properness; the second applies to the scheme charts over the Noetherian affine base; the third supplies finite ideal generators; the fourth supplies exactly kernels, cokernels and finite sums of coherent modules. Finite sums of scalar multiplications then construct J^nF as an image. This is not an assumption of flatness. I read the coherent-abelian source 07UC in spaces-cohomology.tex.

For step 2 I opened lem-trf-space-enlarged-etale-ringed-site-model, lem-sfb-module-resolution-derived-presheaf-comparison, lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison and lem-weil-pbc-right-derived-universal-delta-functor. Their statements supply respectively the site equivalence with terminal object, actual nonnegative injective module resolutions, the natural module/additive comparison at that terminal object, and natural long exact sequences for a left exact additive functor into A-modules. The transport of injectivity along an equivalence follows directly from its lifting property. This checks the terminal-object and module/additive conventions instead of presuming the scheme-valued small etale site has X as an object. Generic inputs from another unit are explicitly declared in split_report.tool_uses.

For step 3 I opened lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, def-trf-space-etale-module-functors, lem-sfb-space-affine-cohomology, lem-sfb-space-affine-module-higher-image-vanishing and lem-sfb-ringed-site-cohomology-fmap-calculus. The scheme comparison states compatibility with tensor pullback and with quasi-compact separated direct image; each chart's closed immersion meets both hypotheses. The functor definition specifies the adjunction and unit. The affine edge node gives precisely H^q(X,j_*F_n) -> H^q(X_n,F_n); the vanishing node states positive module higher images vanish. Finally the fmap-calculus node explicitly states the acyclic-resolution edge normalization, coefficient naturality and the composition identity for coefficient maps. Those clauses justify the actual transition and scalar maps, not just an arbitrary cohomology isomorphism. The displayed chart tensor formula proves j_*F_n=Q_n and its quotient projection directly. Its unit is the canonical restriction. I checked the affine comparison source 0D2U and the 08B1 paragraph; no special strict-local-base property is used here.

Step 4 uses the additive functor assertion of the delta-functor node to preserve zero scalar maps and establish factorization; step 5 uses its exactness and explicit boundary naturality clause. Its statement was opened and copied verbatim in citations.json at each use. Step 6 cites lem-sfb-space-proper-coherent-higher-images for coherence of R^(q+1)f_*G_n and lem-sfb-space-affine-base-higher-image-sections for its sections/cohomology identification. The latter requires qcqs and quasi-coherence, which properness and step 1 provide. The former's statement explicitly includes the finite-module characterization on the Noetherian affine base, so sections give a finite A-module without a new finiteness assertion. I read 08AS (proper-over-affine-cohomology-finite) and 08EX (quasi-coherence-higher-direct-images-application) to check this implication.

Step 7 uses the exact statement of lem-sfb-space-ideal-power-cohomology-image-bound with target index zero and degree q, giving K_(n+c) inside I^nM. Step 8 uses that node again, in degree q+1 and arbitrary target n, and lem-weil-pbc-artin-rees for the finite module L_n and its submodule Im(delta_n). The latter states the required intersection containment; it does not require the submodule to be independently assumed finite. I read 08AX and algebra.tex lemma-map-AR and its preceding Artin-Rees lemma. Expanding finite sums proves I^u Im(delta)=delta(I^uD), so I^nD_n=0 makes the relevant intersection zero. Step 9 is then a three-line application of boundary naturality, exactness and the index inequality, with the reverse inclusion from rho_n=tau rho_r. It cites no new unproved stabilization claim.

Steps 10 and 11 construct an inverse using x_(n+c), independence modulo I^n from the kernel estimate, and compatibility of the quotient maps. Every compatible sequence lies in each stable image by choosing a sufficiently deep source index; no surjectivity of rho_n is claimed. Checking the two composites uses the same representatives and gives equality in every component. These are explicit elementary arguments from the preceding estimates, not a hidden abstract limit theorem. Step 12 checks completed-ring linearity coordinatewise over A/I^n and naturality from the quotient diagrams and the already-cited natural edge. The inverse is natural because it is inverse to this specified natural bijection. Every proof step is shorter than 2000 characters, and I checked that no long step hides a separate comparison lemma: the non-elementary comparison is the existing fmap-calculus node.

Small cases checked: F=0 and X empty give zero limits. I=A gives empty thickenings and zero completions; the argument still applies, with the zero quotient maps and trivial kernel bound exponent zero if necessary. I=0 gives the constant tower X_n=X and Q_n=F and the identity comparison. A=0 is covered by the empty case. For f=id on an affine Noetherian base and q=0 the formula is the definition of completion; for higher q it is zero. Nilpotent I yields an eventually constant tower, with the same lift formulas. The nonflat example A=Z, I=(2), X=Spec(Z/2), F=O_X gives a constant nonzero tower and confirms that no identification of a tensor power with its image or finite-level cohomology base-change is assumed. The q=0 long exact sequence and c=0 shifted indices both work with n>=1.

Every citation quote was generated from the opened live node's statement, and I checked that the fact used in the corresponding step is in that statement. B1-B10: no new statement-only nodes, duplicate definitions, unrun searches or fabricated blueprint ancestry. C1-C8: all non-elementary inputs cited, generic off-unit tools declared, no use of a cited node's proof as an interface. D1-D5: the proof carries its kernel/image/limit argument; nothing is moved to an equivalent new node, and omitted inverse details are supplied. E1-E7: hypotheses checked chartwise; target objects, source indices and actual canonical maps tracked; no completeness or flatness introduced. No SGA source is used.

## Unfinished work

None in the stage-1 split. Existing dependencies keep their current independent states and may still require formal proofs. Preliminary server check_dag and review_split passed. Final dry run and push are recorded by the delivery command.
