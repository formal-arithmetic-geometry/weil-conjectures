# NH — lem-sp-compactification-refinement-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-compactification-refinement-coherence.json`: existing statement node, now split into eleven explicit steps. Statement, statement dependencies, creation stamp and blueprint ancestry retained. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every proof-step citation.
- `searches.jsonl`: actual searches performed through the required msearch command; the node retains inherited searches and appends the searches of this run.

## Attachments

None. Searched the project source by the exact blueprint tag and by compactification/refinement/coherence concepts. Read `WeilConjectures/SixFunctors/LowerShriek/Formalism/{Basic,Compactification,Composition,Associativity}.lean` and the relevant part of `SixFunctors/Etale/Derived/LowerShriekCoherence.lean`. In particular, `AlgebraicGeometry.CompactSupportFormalism.compIso_hom_eq` and `AlgebraicGeometry.CompactSupportFormalism.lowerShriekCompIso_assoc` give related results for a formalism containing pullbacks and their adjoints, with exchange defined by adjunction mates and pullback conditions on refinement comparisons. The present statement instead takes arbitrary P, J and gamma satisfying explicit pasting axioms, includes noncartesian proper/open squares and quantifies over the supplied categories of schemes. Those declarations do not state the whole item with its hypotheses. The coefficient-specific derived statements likewise do not attach to this abstract assertion. No upstream master sorry declaration was treated as a finished proof.

## WANTED

None. Both Stacks sources and the current blueprint source are available locally.

## Audit of the imported item and blueprint

The item was a statement-only child of `lem-sp-coefficient-tower-shriek-calculus`, with ancestor `det-sp-tower-gluing`. Its statement is retained exactly: geometric existence, cofilteredness and invertibility are hypotheses, not conclusions of this formal lemma. This distinction permits a proof solely by the supplied pasting identities and naturality, without an extra geometric or derived-category theorem.

Read the unit `sk-prop-sp-tower-geometric` and its current Local pairs proof in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md`. The split supplies the compact-support composition coherence required when composing the affine-line and etale adjunctions in that paragraph. It does not alter the unit or chapter route. No statement dispute was found.

The source in the item named 0F7J only. I also read Tag 0F7K (`lemma-pseudo-functor`), immediately following it in `literature/stacks-project/more-etale.tex`, which supplies the explicit three-map staircase calculation. The proof_origin and individual step sources now identify both tags. These are formal extractions written by the worker, rather than assertions that Stacks proves an arbitrary coefficient-tower theorem. Tags 0F7C and 0F7D identify the two pasting rules already assumed in the statement. No SGA source is used.

## Mathlib searches

Used leanfinder twice, loogle twice, leansearch once, and three logged source searches, all through msearch.py. The whole-tree compactification grep returned topological Stone-Cech/one-point compactifications; the algebraic-geometry grep for compactification, compactifiable, staircase and refinementComparison returned no hits. The second leanfinder wording suggested `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`. A further logged grep located it in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:273`; reading its statement shows an associativity equation for the ordinary module pullback compositors. This does not state the present assertion. Loogle's IsCofiltered hits and the semantic cofiltered-limit hits concern the assumptions or unrelated limits, not the proper/open staircase assertion. No exact match or one-line specialization was found. All services used here returned results successfully; no unavailable service was reported as a failed match. Existing inherited search entries were preserved rather than relabelled as this worker's searches.

## Not duplicates

No new nodes were created. Searched the whole DAG and blueprint by common refinement, staircase, compactification coherence, the abstract proper/open formulation and Tags 0F7J/0F7K. `prop-compactification-coherence-detailed`, `det-sf-comp-coherence-cocycle` and `lem-amb-etale-compact-comparisons` concern particular coefficient categories, not arbitrary supplied P,J,gamma data. The existing generic geometric nodes were reused. No new node restates a clause of the item.

## Review by NH

I read Stacks `more-etale.tex`, `lemma-shriek-composition` (0F7J) from its construction through the A,B,C,D,E,F diagram and final calculation, and `lemma-pseudo-functor` (0F7K) including its three-square staircase. I checked the local tags table for these labels and for the vertical and horizontal pasting Tags 0F7C/0F7D. This is the source for the item; there are no new-node sources to review. I read both geometric dependency statements in full and checked their exact hypotheses against the schemes and compactifications in this item.

Step 1 normalizes only the supplied compositors and unitors. Vertical pasting of two refinement squares gives tau_vw = P_v(tau_w) tau_v, so applying P_p gives rho_vw = rho_w rho_v. Invertibility is the assumed invertibility of gamma and the compositors. There is no inference from an object's being isomorphic to equality of maps.

Step 2 cites `lem-cbc-compactifiable-cofiltered` for exactly its parallel-arrow equalization clause; its supplied compactification and separated-finite-type hypotheses are present. Cancellation of rho_t proves equality of parallel-arrow comparisons. Step 3 cites the same node for a common refinement of d,d'; further-refinement invariance is written as an explicit inverse cancellation. Step 4 constructs a triple refinement by two pairwise choices and writes the cocycle product on it, so it invokes neither small colimits nor an unmentioned cofiltered-limit theorem.

Step 5 cites `lem-cbc-compactifiable-compatible-tower`. Its statement explicitly supplies proper maps on both ambient compactifications AND on the intermediate schemes, commuting with all tower arrows; the detailed equations in the step are those in its statement. In particular, t:V_+ to V_- is proper even though no cartesian condition is imposed on a refinement square. Each of A,B,C,D,E,F has open horizontal maps and proper vertical maps. Step 6 applies precisely the horizontal and vertical pasting axioms of the item's hypotheses. The two vertical pastes have the same entire boundary by p_- h = k p_+ and r_- t = r_+.

Step 7 supplies the naturality equation that commutes A past B, then substitutes the two equations of step 6. I checked that gamma_B is evaluated on the morphism gamma_A(M) in D_(V_-), and that the resulting equality has source H_(g,-) H_(f,-) and target H_(gf,+). This is the actual refinement-compatibility argument; it is not delegated to a new node restating the conclusion. Step 8 cites the compatible-tower node only for common refining towers; the conclusion then follows by inverting the already constructed comparisons. No theorem about finite coefficients or varying rings is being generalized silently: `lem-sp-varying-ring-proper-open-pasting` remains a statement reference for the shape of the supplied axioms, not a proof citation applied outside its coefficient hypotheses.

Steps 9 and 10 use the three-map staircase assumed in the item. I checked every map's source and target: gamma_A maps D_U to D_W, gamma_C maps D_W to D_(bar Z), and naturality of gamma_C at gamma_A(M) gives exactly the displayed commuting equation. Expanding the A+B and B+C pastes leaves a common final gamma_B factor and that one naturality square. The input is P_s J_o P_u J_i P_r J_j and the output before compositors is P_s P_q P_p J_b J_c J_j. After the compositors it is P_(sqp) J_a because a=bcj. Step 11 inserts the comparison equations of step 8 and cancels the internal comparisons using step 4; for identity towers the identity-square axiom and unitors give the asserted identity maps.

I marked algebraic steps elementary only where they consist of substitution into an assumed pasting law, a written naturality square, or cancellation of displayed inverse pairs. The geometric existence applications are marked non-elementary and cite the actual generic geometric nodes. The statement already assumes the abstract coherence axioms, so proving them again or introducing a new generic grid-coherence lemma would duplicate assumptions. All eleven steps are shorter than 2000 characters; none hides an independent standard identification or an auxiliary lemma.

I checked the edge cases: coincident compactifications, identity refinements, different parallel refinement arrows (explicitly equalized), a triple with repeated compactifications, empty schemes/zero or terminal supplied categories, and towers with an identity map. The equations still type-check and reduce to inverse/unit cancellation. The noncartesian refinement case is explicitly allowed throughout; no scheme-theoretic density or uniqueness of ambient maps was assumed. No Noetherian, qcqs, coefficient, adjoint or conservativity hypothesis was added.

Against delivery-errors B--E: the existing statement is self-contained with its inline P,J,gamma definitions; all statement dependencies were retained, no new statement-only node is needed; actual searches and exact inherited blueprint ancestry are recorded; every external proof-step use has a statement quote in citations.json; all other operations are explicit consequences of the supplied axioms; no definition node is used as a theorem, no new node relocates the item's content, and no source/type error was found. Corrections during this review were to supply the previously absent proof, expose parallel-arrow equalization, type the six-square naturality interchange, and cite 0F7K for the staircase instead of leaving three-map coherence implicit.

## Unfinished work

None in this one-level split. No Lean files were written or compiled. The required dry-run and push are performed by the delivery tool after this report is written; the final response records the resulting delivery commit.
