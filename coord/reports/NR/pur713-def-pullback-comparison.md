# Stage-1 report: pur713-def-pullback-comparison

## Files written

- `dag/nodes/sec-smooth-purity/pur713-def-pullback-comparison.json`: definition, split into six existing statement dependencies; Mathlib searched, no exact match.
- `citations.json`: empty list, since this item is a definition and has no proof steps.
- `searches.jsonl`: the actual msearch records; six searches, all available, with results read.

## New nodes

None. Zero new nodes and zero Mathlib leaves.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 checkout for the exact blueprint tag, pullback comparison, pullbackSquareComparison, and composition of pro-etale pullbacks. Read SixFunctors/BaseChange/DerivedComparison.lean:74-86 and Etale/BaseChangeTheorems/MorphismDefs.lean:145-155. Their comparison is for bounded-below etale categories, so it cannot attach to this ambient unbounded pro-etale definition. The exact master reference SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/MorphismDefs.lean:90-100 defines a bounded constructible module-object comparison; that also has the wrong category and master is reference material only. The item's slopmaster2 audit is `none`.

## WANTED

None. The construction is supplied by existing DAG statements and Stacks 0D6D, whose local source was read.

## Corrections and source alignment

Read the current main-20261015 node pur713-def-pullback-comparison, its unit sk-prop-sp-purity-bc (the source/target identifications and the three proof paragraphs in the unit record), and the fixed sec-smooth-purity chapter record. The imported definition had no statement dependencies and referred by textual ID to pur713-def-pull-composition and pur713-lem-pull-composition, neither of which exists as a node in the whole current DAG or as a source file in the current blueprint. This is a missing-reference defect, not a false mathematical assertion. I replaced these references with the existing general lem-weil-pbc-proetale-derived-pullback-composition and made the direction explicit: the blueprint's mu_{k,h,A} is the inverse of that node's c_{h,k}. No statement dispute or change of purity proof route is needed.

The statement now introduces ell, E, its valuation ring/uniformizer, n>=1 and A, every arrow of the square, the constant ring sheaves, the ambient unbounded categories, and the canonical coefficient maps. No boundedness, constructibility, finite Tor amplitude, smoothness, or exceptional-adjoint datum is inserted in the comparison definition. The unit uses its restriction to the purity setting, and no assertion about preservation of a smaller category is added. Equal composites are handled by transport along the scheme-morphism equality rather than a claimed definitional equality of separately constructed functors.

## Existing-node and blueprint searches

Used whole-DAG keyword and ID searches, plus blueprint_refs.py search for `pullback comparison`, `Cartesian square`, `composition comparison`, `finite-coefficient inverse`, `derived pullback composition`, and `comparison of the two pullbacks`. The existing Stacks 0D6D node covers all required composition/invertibility content, so neither missing pur713 ID was recreated. The item is already an imported blueprint definition (`blueprint.is` itself, `from` null); no other complete blueprint definition has precisely the same finite-coefficient statement, so `same_as` is [].

## Not duplicates

No new-node pairs. The related pur713-def-pullback-comparison-module concerns module-object categories at integral and field coefficients, whereas this item concerns ordinary sheaves of modules over finite constant rings. def-exchange-projection contains the same theta as part of a larger exchange/projection construction with more geometric inputs; it is not a new prerequisite, and using it here would add irrelevant compact-support/projection dependencies. The general existing composition lemma is reused directly.

## Review by NR

I read the definition verbatim in main-20261015/sec-smooth-purity/sk-prop-sp-purity-bc/pur713-def-pullback-comparison.md and all six prerequisite statements, including the full constructions in def-weil-pbc-proetale-operations and the constant-map construction in prop-weil-pbc-proetale-constant-ring-map. I also read sites-cohomology.tex, label lemma-derived-pullback-composition (Tag 0D6D), including its proof with a K-flat complex with flat terms. Its conclusion is about all unbounded derived objects and agrees with the existing DAG composition lemma, so no bounded-below substitution is hidden here. No new nodes require a separate source check.

This is a definition, so there are no theorem proof steps to audit and no non-elementary argument to hide in a step. Here is the precise construction audit. def-weil-l-adic-coefficient-extension defines exactly A=O_E/varpi^n for n>=1. def-weil-pbc-cartesian-square supplies the four arrow types, the chosen fibre product, and fg'=gf'; I use only these clauses and not its separate etale comparison. def-weil-pbc-proetale-site defines both the constant ring sheaf and D(T_proet,A), with compatible universes. prop-weil-pbc-proetale-constant-ring-map supplies the canonical isomorphism u^{-1}A_V -> A_U; def-weil-pbc-proetale-operations accepts such identifications and defines the exact termwise-induced unbounded pullback. Finally the statement of lem-weil-pbc-proetale-derived-pullback-composition supplies the canonical natural isomorphism L(kh)^* -> Lh^* Lk^*, including its termwise interpretation. It is the theorem ensuring the data used in this definition exist, not merely a definition of composition.

I checked that the coefficient identification for a composite meets that lemma's compatibility hypothesis. The map for k followed by h and the map for kh both send each constant coefficient a to the constant coefficient a: this is the defining formula for rho in the constant-ring-map node, applied twice. On the constant presheaf these formulas agree, and uniqueness of extension through sheafification gives equality on the constant ring sheaf. Thus the ringed composite is the canonical constant-coefficient composite, rather than one with an unrelated ring action. This is an elementary check of the specified maps, not a new general coherence theorem.

For the formula, mu_{g,f'} goes from Lf'^* Lg^* to L(gf')^*; equality of scheme composites transports that middle category functor to L(fg')^*; mu_{f,g'}^{-1} then goes to Lg'^* Lf^*. The inverse is mu_{g,f'}^{-1} after the reverse middle transport after mu_{f,g'}. The two composites cancel the mutually inverse maps and transports, so the displayed data are a natural isomorphism. Naturality follows by composing the natural-isomorphism squares already supplied by the composition lemma. The generic inverse/composition operations are elementary and were not made into nodes.

Checked n=1 and nonreduced coefficient quotients n>1 (no flatness of A over O_E is required), the zero complex, schemes or fibre product empty (the constant-ring-map node explicitly includes the empty scheme), the square with all arrows identities, and a square in which both factorizations coincide. In the last case the two composition isomorphisms cancel, as the orientation requires. The definition uses only commutativity for the comparison; retaining the Cartesian datum from the source does not demand smoothness or properness. Six dependency paths were inspected by a source-only graph traversal; none returns to the item.

For delivery-errors B-E: all objects and notions in the expanded definition have actual existing definitions; all non-elementary existence/invertibility content is the statement of the cited composition lemma, not a proof-only fact; no theorem clause has been moved into a new node; TeX is written once; searches are exactly those in searches.jsonl, including the second semantic phrasing. Read the closest Mathlib sources at Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:148-174 and AlgebraicGeometry/Modules/Sheaf.lean:233-250; these supply underived comparisons, which do not make the derived pro-etale definition a Mathlib leaf. There is no SGA citation.

## Unfinished work

None within this one-level split. Existing prerequisites remain separate DAG items. A second reader must review and deliver; this worker will run only --no-push.


## Second reading by NR

I independently opened the current blueprint definition (main-20261015, order
2353), its unit record sk-prop-sp-purity-bc including all three proof paragraphs,
the fixed chapter record, all six cited dependency statements, and Stacks
sites-cohomology.tex, label lemma-derived-pullback-composition (Tag 0D6D,
confirmed in stacks-project/tags/tags). The item has no blueprint_update.

- Item statement: compared every coefficient, arrow, category and displayed map with pur713-def-pullback-comparison.md; PASS. The construction has the original ambient unbounded pro-etale category and the original direction, with no smoothness, properness or constructibility hypothesis added.
- Proof steps: none (kind definition, proof and proof_deps empty); PASS. citations.json remains [] because there are no proof-step citations.
- Construction clause 1: checked ell, finite E, uniformizer and n >= 1 against def-weil-l-adic-coefficient-extension, especially clause 4; PASS. It supplies the finite commutative coefficient ring needed by the constant-ring-map theorem.
- Construction clause 2: checked all four arrow types and fg' = gf' against def-weil-pbc-cartesian-square; PASS. Only its Cartesian datum and commutativity are used, without importing its etale sheaf comparison into the pro-etale category.
- Construction clause 3: checked the constant sheaf and unbounded D against def-weil-pbc-proetale-site and the module pullback against def-weil-pbc-proetale-operations; PASS. The latter accepts precisely an isomorphism u^{-1}A_V -> A_U, which prop-weil-pbc-proetale-constant-ring-map supplies for finite A, including the empty scheme.
- Construction clause 4: checked mu against the full statement of lem-weil-pbc-proetale-derived-pullback-composition and Stacks 0D6D; PASS. Its c_{h,k} goes from L(kh)^* to Lh^* Lk^*, so taking its inverse gives the specified mu. Its composite ring identification hypothesis holds: both direct and iterated structure maps send a constant a to the same constant a; their adjuncts agree on the defining constant presheaf and hence on its sheafification. This checks the hypothesis rather than using material hidden in a cited proof.
- Construction clause 5: checked the final composite and equality transport against the displayed blueprint formula; PASS. Starting at Lf'^* Lg^*, mu_{g,f'} reaches L(gf')^*, the commutativity transport reaches L(fg')^*, and mu_{f,g'}^{-1} reaches Lg'^* Lf^*. Reversing these three isomorphisms gives its inverse; the naturality squares compose. These elementary operations need no new node.
- New nodes: none; PASS. B1-B7 and the duplicate/restatement audit have no new-node cases. Whole-DAG source-tag searches found the existing general pro-etale 0D6D lemma; the nearby def-weil-pbc-derived-square-iso is etale with a bounded-below restriction, and pur713-def-pullback-comparison-module is for integral/field module objects, so neither replaces this definition.

Small cases checked independently: the zero complex; n = 1 (residue field);
n > 1 with nonreduced coefficients (no coefficient flatness needed); empty X'
or all schemes empty (the coefficient-map theorem explicitly covers it);
identity squares and identical factorizations (the same composition comparison
and its inverse cancel). No false or ill-typed assertion was found and no
STATEMENT-DISPUTED correction is needed. This is an ordinary inverse-image
construction, with no use of SGA or of a purity trace route.

I independently searched slopmaster2 for the item ID, pullbackSquareComparison
and derivedPullbackComp, then read MorphismDefs.lean:145-155 and
DerivedComparison.lean:74-86. Their types are bounded-below etale, so they do
not attach here. I also read the master reference's module-object
MorphismDefs.lean:90-100; its bounded constructible type is different and was
not treated as a finished proof.

Changes made: appended two independent, differently phrased Mathlib searches
(LeanFinder and grep) to the item's mathlib_searches, retaining the actual
msearch.py records in searches.jsonl; appended this review. LeanFinder found
mapDerivedCategory and its factorization isomorphisms. Reading the pinned
Mathlib ExactFunctor.lean:29-144 confirms these do not supply a square
comparison; grep found six factorization-related occurrences and no
mapDerivedCategoryCompIso. I independently read the underived pullbackComp
signatures at PullbackContinuous.lean:167 and Modules/Sheaf.lean:241 as well.
No Mathlib leaf was gained. The mathematical statement, six dependencies,
empty proof, empty citations, and first worker's report/review were retained.
This avoids changing already correct work. Final counts: zero new nodes,
zero Mathlib leaves.
