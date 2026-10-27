# Stage-1 report: lem-pur-clopen-derived-scalar-compositor

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-clopen-derived-scalar-compositor.json: statement, split using existing nodes; full item absent from Mathlib.
- citations.json: 16 entries, one for every step/node pair, each quoting the cited statement verbatim.
- report.md: this review and delivery report.

New nodes: 0. New Mathlib leaves: 0. The existing tensor, ringed pullback, scalar compositor and localization nodes already supply all non-elementary inputs.

## Attachments

None. Searches throughout lean/WeilConjectures for the blueprint tag and clopen/scalar/derived terminology found no project declaration stating the item. General ChangeOfScalarsSquare and ExtendScalars constructions cover ordinary module functors, not this entire unbounded sheaf-derived assertion. No compiler, Lake, or Lean editing was used.

## WANTED

None.

## Corrections and observations

The item had a statement but no proof. Its statement and statement dependencies are retained. In particular, flatness is over the target coefficient ring after extension; no flatness of the coefficient map is introduced. The proof uses the full resolving-class localization equivalence, rather than assuming objectwise K-flat computation alone supplies naturality on all derived arrows. The ordinary clopen tensor node is applied to S[0] without incorrectly requiring S to be R-flat.

Blueprint searches: tools/blueprint_refs.py ancestor identifies def-pur-section-invariant. Searches for scalar compositor, restriction tensor, K-flat, scalar, localization and clopen revealed no imported node stating this normalized comparison. Read the current main-20261015 section-invariant source, the recorded chapter and unit, and the live ancestor and parent tensor-calculus statements. The final invertibility claim is the ancestor place served, through the existing finite-clopen derived decomposition. No route above the node level is changed.

Mathlib: ran msearch.py under Q27 with LeanFinder (two phrasings), LeanSearch, Loogle and grep, recording the actual outcomes. All services answered. The full item is not a one-line specialization of a hit: Scheme.Modules.restrictFunctorAdjCounitIso is ordinary structural-sheaf restriction; ModuleCat.homEquiv_extendScalarsComp is ordinary modules; SheafOfModules.pullbackComp is an underived pullback comparison. The latter's source constructs it by uniqueness of adjoints and has no unbounded derived or K-flat assertion. Localization.liftNatIso is a genuine general tool already represented by lem-weil-pbc-localization-universal-property, so no duplicate leaf is created. Read its implementation and natTrans_ext/fullyFaithfulWhiskeringLeft. The inherited searches are retained as historical evidence; newly executed queries are appended from this sandbox's search log.

## Unfinished work

None within this one-level split. The cited unsplit clopen tensor and localization nodes remain their own independent stage-1 items, as required; their statements, not any unproved hidden content, are the inputs used here.

## Not duplicates

No new node is created, so there are no new/existing pairs to distinguish. In particular a generic K-flat preservation node, a new localization-of-resolving-class node, and a scalar-compositor node would duplicate existing statements and were not created.

## Review by Q27

I read coord/delivery-errors.md B through E in both copies, with the actual input statements and source passages open. For the item I read Stacks sites-cohomology.tex Tag 06YY (lemma-derived-base-change), Tag 0D6D (lemma-derived-pullback-composition), Tag 0G7E (lemma-pullback-K-flat), Tag 06YS (lemma-K-flat-resolution), and Tag 0G7D (lemma-factor-through-K-flat, including its flat-term clause). I also read sites-modules.tex Tag 05V4 (lemma-flat-change-of-rings) and the sheaf tensor/sheafification construction. Its displayed flat-change-of-rings proof has an apparent F/G variable typo; I do not rely on that typo, instead using the existing stronger ringed-topos K-flat pullback statement. The normalization calculation below is explicitly agent-written. There are no new nodes needing separate sources.

Step 1 uses lem-pur-clopen-total-tensor-kflat-detection: I checked that its statement gives a natural chain isomorphism for every pair of unbounded complexes, its pure-tensor formula and differential, not merely a derived or homology isomorphism. Taking the second complex S[0] is legitimate for arbitrary a. The additional S_i-linearity and compatibility with homotopies are written out and require only multiplication and degreewise naturality. This step is elementary relative to that cited comparison.

Step 2 uses lem-weil-pbc-ringed-topos-kflat-pullback on the identity underlying topos, with structure ring map a. I read its statement and checked both hypotheses, K-flatness and flat terms, are exactly the hypotheses on P. Its conclusion is K-flatness and flat terms over S, even for nonflat a. The clopen tensor-detection statement supplies both flat-module detection and K-flat detection for any coefficient sheaf; these give the same conditions after restricting. The computation clause of lem-pur-derived-change-of-rings is then applicable on both sites. Fixed small sites and coefficient universes are inherited from the item, as required by the generic pullback statement.

Step 3 uses lem-weil-pbc-site-derived-tensor-descent specifically for the sentence that the localization of the full flat-term K-flat homotopy subcategory is equivalent to D(R). This is stronger than mere existence of resolutions and is exactly what is needed here. I read its whole statement. The scalar computation/choice compatibility used is stated in lem-pur-derived-change-of-rings; the restriction localization comparison and preservation of quasi-isomorphisms used are stated in lem-pur-clopen-unbounded-derived-localization. The existing Mathlib leaf lem-weil-pbc-localization-universal-property explicitly supplies lifting of natural transformations with the specified component formula, preservation of identities/composition, and lifting of isomorphisms. Hence descending beta and its inverse gives a natural isomorphism, and uniqueness establishes independence of resolution. This step does not take a Yoneda or Kan-extension assertion from a definition that lacks it.

Step 4 uses the full statement of lem-sfb-successive-derived-quotient-normalization: it is for arbitrary ring-sheaf maps on a small site, not only quotient maps despite its name, and explicitly gives (x tensor s) tensor t mapping to x tensor b(s)t. The component application has the same hypotheses. I checked the domain of the two composites is restriction of the iterated scalar extension over T and the codomain is scalar extension over R_i to T_i, so the equation is typed. Step 2 permits the same P and P tensor_R S throughout. I calculate both paths, including r_i(psi(s)t)=psi_i(r_i s)r_i t, rather than asserting unspecified coherence. The sheaf tensor definition supplies local sheafified tensor generators and their additive extension. The localization leaf and resolving-class equivalence carry the equality of the resulting natural transformations from those models to all derived objects and morphisms. No sign appears because both coefficient factors have degree zero and nothing is permuted.

Step 5 first checks the unit formula on those models and uses precisely the same cited localization uniqueness to extend it. I read lem-pur-clopen-ringed-module-gluing and verified it states preservation of completed/finite coefficient identifications, projections and actual transition maps. These are all that the specialization uses; existence of new derived identifications is not assumed from a definition. The final zero-case argument uses the explicit zero-derived-category conclusions of lem-pur-clopen-unbounded-derived-localization. For an empty index set the covering forces X empty; for an empty component or zero ring sheaf every module and derived arrow is unique. The formulas therefore remain meaningful. I also tested the one-component identity restriction, identity coefficient map and nonflat example Z to Z/2 to Z/2: no step assumes exactness of extension of scalars, and flatness always changes to the output ring.

No step exceeds 2000 characters (lengths 789, 682, 1192, 985, 953), and each is one assembly or explicit calculation using named inputs. All non-elementary steps name all their inputs; proof_deps is exactly their uses union. All 16 citation quotes are verbatim complete statements so every clause cited is exposed to review. I checked the transitive dependencies of the generic pullback, resolving-class descent, scalar compositor and clopen tensor nodes do not reach this item, preventing a cycle. The generic tools in other units are declared in split_report.tool_uses with their purpose; they preserve the unit's route. No new lemma restates a clause of the item, no data are chosen from a hollow definition, and no SGA source is used.
