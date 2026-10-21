# Stage-1 report: lem-sfb-integral-ambient-tower-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-ambient-tower-comparison.json`: statement; split into eight steps, no Mathlib match. The statement is unchanged.
- No new DAG nodes; zero Mathlib leaves.
- `citations.json`: nineteen verbatim statement extracts, one for each step/cited-node pair.
- `searches.jsonl`: actual Q63 msearch results. The inherited searches, citations and metadata of the item are retained. `write_split.py` and `bhatt-scholze.txt` are sandbox working material.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, ambient tower comparisons, completeness, reduction and direct image found no declaration stating all clauses for the continuous completed coefficient sheaves. In particular `AlgebraicGeometry.ProEtale.derivedComplete_and_exists_iso_of_isNormalizedTower` in `SixFunctors/ProEtale/FiniteCoefficient/Derived/AdicRealization.lean:104` concerns realization of a normalized constant-coefficient tower on one scheme, not this ordinary completed-coefficient direct-image comparison. The completeness declaration in `SixFunctors/Etale/Derived/DerivedComplete.lean:131` is on the etale site with constant coefficients. Neither is an attachment for this item. No source declaration containing sorry has been treated as a finished proof.

## WANTED

None for this split. The local Bhatt--Scholze PDF and Stacks TeX provide the route. The existing arithmetic nodes describe their own literature situation; no new arithmetic lemma is asserted here.

## Corrections and scope

The imported item had no proof. I supplied the DVR verification, ordinary coefficient-action comparisons, perfect-coefficient argument, finite-coefficient linear mate, compatibility before evaluation, canonical completion identification, and bounded-below etale comparison. No statement dispute was found and no hypotheses were changed.

I did not use the pro-object part of Bhatt--Scholze 6.5.9(1) as a levelwise comparison: 6.5.9(3) applies because the quotients have explicit finite free resolutions. I did not apply Stacks 099N directly to sheaves of modules over a nonconstant completed ring: the completed-coefficient comparison is a cited existing node. The etale-origin clause uses D-plus, not an unbounded comparison. In 6.5.9 the paper writes qcqs schemes; the actual arguments used here are the more general ringed-topos projection and limit tools, while 5.4.3 requires only a qcqs morphism. Thus no absolute quasi-compactness of X or Y is silently added.

The ancestor's integral paragraph is realized without using its finiteness assertion. The source material used for the proof is Bhatt--Scholze and Stacks. The chapter and unit are untouched: this is a subordinate node, not the unit's key statement.

## Searches and reuse

Read the inherited five Mathlib search records before adding Q63 searches. Ran leanfinder on complete ordinary pro-etale image and inverse limits, loogle `SheafOfModules, DerivedCategory`, grep for pro-etale/module sheaf completeness, and leansearch for derived direct image as the inverse limit of reductions. A second leanfinder phrasing asked for a perfect coefficient projection formula on ringed topoi. Returned material concerns scalar AdicCompletion, ordinary scheme module pushforward composition, K-projectivity and general derived categories; none states this item. Queries and returned names are copied from the actual search log, not invented. There is no Mathlib leaf claim.

Before proposing any nodes, searched the whole DAG for 6.5.9, 5.4.3, 099L, 099N, 09A6, 0A07 and perfect projection; also searched all imported blueprint records with `tools/blueprint_refs.py search` for `perfect projection`, `direct image`, `finite reduction`, and `adic`. Read the relevant matches. This exposed the existing perfect projection formula, completed-coefficient comparison, augmented diagram mate and strict system adjunction, so no new node was needed. No blueprint node is exactly the full combination in this item; `blueprint.same_as` remains empty. Opened all cited node statements and checked the transitive dependency graph for paths back to this item: none.

## Not duplicates

There are no new nodes. In particular, the finite projection formula is reused from `lemma-weil-pbc-perfect-projection-formula`; completed-coefficient reconstruction is reused from `lem-pur-completed-coefficient-pushforward-comparison`; the bounded-below site comparison is reused from `sk-thm-pe-direct-image-comparison`. The broader strict-diagram tools supply coherence rather than duplicate clauses of the item.

## Review by Q63

I read Bhatt--Scholze Lemma 6.5.9 and its proof (PDF printed pages 50--51), including the distinction between its pro-object clause (1) and perfect scalar clause (3), and Lemma 5.4.3 with its bounded-below hypothesis and the following warning about unbounded complexes. I also read Stacks `proetale.tex`, Tag 099N (`lemma-pushforward-Noetherian-case`) and Tag 09A6 (`lemma-morphism-comparison`), and `sites-cohomology.tex`, Tag 0A07 (`lemma-Rf-commutes-with-Rlim`), including the strict diagram-topos proof. There are no new nodes needing separate sources. The specialized argument is marked agent-written because coefficient actions and strict-tower unit normalization are assembled using existing general DAG statements, not asserted to be a verbatim single theorem of the PDF.

For step 1 I read the statements of `lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients` and `def-weil-pbc-adic-coefficient-datum`. The first gives exactly a principal ideal domain, nonzero uniformizers, and the extending valuation; the second gives finite quotients. The one-line deductions are written out: principal ideals imply Noetherian, multiplication by a nonzero element in a domain is injective, and ell in the maximal ideal implies ell^n kills P_n. The exact two-term resolution verifies perfection, rather than assuming every finite module is perfect.

For step 2 I read `lem-sfb-integers-profinite-tower` for A as its topological quotient limit, `sk-prop-sfb-qlbar-colimit-x` for the pulled-back condensed coefficient limit and constant finite coefficients, `sk-prop-sfb-cartesian-coefficients` for the inverse-image ring isomorphisms, and `lem-weil-pbc-profinite-coefficient-inverse-image` for the actual projection and transition equations. These nodes supply precisely the coefficient identifications used; there is no identification of the continuous integral sheaf with the constant A-sheaf. Completeness of scalar A also checks the hypothesis of the coefficient-system lemma later.

For step 3 the statement of `sk-def-sfb-module-derived-pushpull` explicitly defines the total derived functor of the ordinary module direct-image composite using K-injectives; it does not replace it by a different derived abelian construction. I read both scalar restriction formulas and the strict-system clause of `lem-pur-completed-coefficient-pushforward-comparison`. This node allows arbitrary schemes and morphisms. Its named auxiliary distinct prime p can be chosen independently of the schemes; it is not an assumption of positive characteristic on the schemes. Consequently its integral coefficient hypotheses are all met here, and its restriction comparison retains the prescribed actions.

For step 4 `lem-weil-pbc-completed-constant-sheaf-reduction` really asserts that extension of a finite projective scalar resolution represents the quotient sheaf over the completed coefficients. This is the needed bridge to `lemma-weil-pbc-perfect-projection-formula`, whose statement allows unbounded K, ordinary completed-coefficient direct image, every finite level, and the canonical projection morphism. Its statement gives the maps used here, not merely existence of some isomorphism of underlying abelian complexes.

For step 5 I checked all four cited statements. `lem-pur-coefficient-system-derived-comparison` gives the levelwise exact pullback/derived direct-image adjunction for strict finite quotient systems and its evaluated adjunctions. Its optional fully faithful comparison/descent clause is not used. `lem-weil-pbc-reduction-pullback-derived-tower` provides normalized reduction/pullback comparison on flat-term K-flat representatives. `lem-pur-diagram-ring-restriction-pushforward` gives restriction versus derived pushforward on diagram categories before evaluation. `lem-weil-pbc-augmented-diagram-projection-mate` identifies the underlying augmented mate with the counit-tensor map. The resulting morphism is first constructed over the finite ring diagram. Only after that do I forget the quotient action to test that its cone is acyclic; exact restriction preserves underlying abelian sheaves and therefore detects quasi-isomorphisms. This addresses the possible gap between A-linearity and P_n-linearity.

For step 6 I checked the augmented equality and the evaluation description in `lem-weil-pbc-augmented-diagram-projection-mate`. I wrote out the quotient naturality square on the adjuncts: both routes apply the same counit and coefficient quotient in different tensor factors. The cited node supplies this at the derived strict-tower level, so this is not an unjustified inference from a family of evaluated arrows. It also records the exact augmentation equation needed for the completion map.

For step 7 I reread the completion and projection normalization clauses of `lem-pur-completed-coefficient-pushforward-comparison`, and the statement of `lem-weil-ringed-tower-pushforward-limit-comparison`. The latter uses a small countable tower index and works for unbounded objects without exact product assumptions. Its comparison is induced by the common underived composite, not by treating an inverse limit in a triangulated category as an ordinary categorical limit. The former uses the same `def-weil-derived-complete` as the item and explicitly supplies preservation and canonical reconstruction. Applying the augmented equation of step 6 identifies the resulting canonical map, including all quotient projections.

For step 8 I checked `sk-thm-pe-direct-image-comparison`: it is a statement for arbitrary discrete commutative Lambda, D-plus on the etale side, a qcqs morphism, and canonical coefficient-linear comparison. Setting Lambda=P_n and using the specified isomorphism from K_n gives exactly the claimed result. Properness, a finite-type base field, and constructibility are not among this tool's hypotheses.

I checked B--E of `coord/delivery-errors.md` against this split: no unsplit new-node proof, no new notion missing its definition, no unlogged searches, no duplicate creation, no cyclic citation, no proof of a cited node used in place of its statement, and no unsupported statement from a source tag alone. Off-unit statement tools are declared in `split_report.tool_uses` with their particular purpose; they implement the integral unit route rather than replacing it. All eight proof steps are shorter than 2000 characters. Edge cases checked were n=1, E=Q_ell, a ramified E (ell^n annihilation still follows from ell=varpi a), zero K, identity f, schemes in characteristic ell, and genuinely unbounded complete K. The proof never needs ell invertible on a scheme, or a common lower bound except in the separately assumed etale-origin clause.

## Unfinished work

None in the one-level split. No Lean was written and no compiler, Lake or build tool was run. Server `review_split` passed with zero new nodes and `check_dag` reported no finding introduced by the sandbox. The required final delivery dry run and push follow this report.
