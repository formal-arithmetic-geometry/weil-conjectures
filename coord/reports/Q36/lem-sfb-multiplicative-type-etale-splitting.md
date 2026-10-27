# Worker report: lem-sfb-multiplicative-type-etale-splitting

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-type-etale-splitting.json: statement, split; no Mathlib match. Eight proof steps, all shorter than 2000 characters.
- citations.json: all 32 step/node citations, with the verbatim statement of each cited node so the precise clause and its hypotheses are available together.
- report.md. Supporting sandbox-only write_split.py and searches.jsonl retain the construction and the actual search log.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches under lean/WeilConjectures for the blueprint tag, multiplicative-type, diagonalizable/diagonalisable and related group-scheme notions found no declaration stating the item. The ordinary multiplicative groups, Kummer sheaves and unrelated multiplicative constructions do not provide this assertion. No compiler or Lake was invoked.

## Wanted literature

WANTED: Brian Conrad, Reductive group schemes, Appendix B.1 and Proposition B.3.4, printed pp.280-281 and 290-292, for lem-sfb-multiplicative-type-etale-splitting; local path literature/conrad-reductive-group-schemes.pdf. The specified Stanford PDF was read online without downloading it. The local Stacks sources were read for every descent/bootstrap input. No SGA source was used.

## Findings and proof route

The item statement is correct and remains verbatim. Its empty imported proof was not a split. The source's proof by completion is unsuitable here as a direct citation of the existing deformation chain: that chain already uses this item. Instead, below the fixed unit route, the proof uses the isomorphism-sheaf descent argument also used for the existing torus-etale-trivialization node. The relative character-duality node explicitly allows arbitrary finitely generated abelian groups, including torsion, and nonreduced rings. It therefore supplies the required generalization of the torus argument without assuming the item or any infinitesimal-lifting theorem.

The latest blueprint unit and its direct-images proof were read. This item is the Conrad B.3.4 structural prerequisite in the inherited direct-images (3) chain, not a new realization of the unit theorem. No unit/chapter file is changed. The ancestor utility reports None for this existing chain; the item's existing from.node=null and via list are retained, and from.place already specifies the structural prerequisite precisely. Whole-blueprint searches for multiplicative, diagonalizable and diagonalisable found no equivalent blueprint statement. The torus statement is only the torsion-free special case; it is not cited to assert the more general conclusion.

Mathlib searches used only msearch.py. The new log contains LeanSearch, two LeanFinder phrasings, Loogle and grep in AlgebraicGeometry. I read all returned hits. They concern general etale morphisms, affine diagonals or constant condensed modules. None is a theorem about diagonalizable group schemes or their fppf forms. The inherited searches from Q109 were preserved as historical records and the fresh actual queries/results appended. The grep's zero hits and the GroupScheme/Etale Loogle zero hits agree with the semantic searches. No service was reported unavailable.

## Not duplicates

No new nodes are proposed. The search by B.3.4 and multiplicative/diagonalizable keywords located the torus special case, character duality, fpqc multiplicative-type descent, and the nilpotent-deformation parent; their statements were read. Existing character duality and general covering/space foundations suffice. The proof does not introduce a new node for a clause of this item or for the elementary evaluation of its isomorphism functor.

## Review by Q36

I read Conrad Proposition B.3.4 online, including its fppf-local finite-type hypothesis and its etale-local conclusion, and Appendix B.1 for the character description. I did not use the character-sheaf anti-equivalence asserted by B.3.4 as an input, since that would assume this theorem. I read Stacks bootstrap.tex theorem-final-bootstrap (04S6), descent.tex lemma-descending-property-etale (02VN), lemma-local-source-target-characterize and remark-list-local-source-target (04R1/04R3), etale-cohomology.tex lemma-representable-sheaf-fpqc (03O3), topologies.tex lemma-fppf (021O), and spaces.tex definition-algebraic-space (025Y), with the stated hypotheses. All cited DAG statements were opened; citations.json quotes their statements verbatim rather than extracting an assertion from a proof.

Step 1 uses the ring-diagonalizable definition for the Hopf operations, the affine fibre-product and tensor pushout statements for base change, the affine adjunction to pass from algebra maps to scheme maps, and morphism gluing for arbitrary bases. The explicit two inverse tensor formulas preserve all operations on each basis element. This avoids silently assuming a base-change theorem for group schemes. The size-convention definition bounds the covering index sets and their isomorphism-label sets.

Step 2 uses exactly the base-change-of-fppf-covering statement, fppf-is-fpqc, and representable descent. It descends BOTH the map and its inverse on covers of their respective source schemes; uniqueness applied on product-source covers gives the group identities and compatibility equations. Representable descent is a statement about maps into an arbitrary scheme, so neither global affineness nor separation nor quasi-compactness of the source is required.

Step 3 uses the relative character-duality statement's locally constant homomorphism classification, not its quotient or closed-immersion clauses. Apply it also to the inverse: uniqueness then says that the lattice homomorphism is invertible. The affine-cover statement permits this on every test scheme, with no connectedness assumption. The coproduct statement gives disjoint open-and-closed label components, and the scheme-morphism-gluing statement glues both directions. The contravariant label is Isom(M_alpha,M_beta) for a map D(M_beta) to D(M_alpha), so the variance has been checked. The nonzero-ring condition on character duality is enforced by restricting its application to nonempty affine opens; empty charts and empty label sets are handled separately.

Step 4 spells out the entire scheme test for the atlas map. The coproduct and fppf-base-change statements give the source and its joint surjectivity. Source locality in the five-property node applies to flatness and local finite presentation; the components are etale open immersions by the coproduct and etale-composition statements. Thus ALL tests, and not only tests already in the splitting cover, satisfy 04S6's hypotheses.

Step 5 uses the definition of algebraic space and representable descent to check that a scheme is an algebraic space (identity atlas and scheme fibre products), then the existing fppf-space-atlas-bootstrap statement for precisely the tests of step 4. No diagonal representability assumption on F_beta was inserted, since the bootstrap node does not assume one. No hidden application of effective descent for arbitrary schemes occurs. The atlas W_beta is a scheme by the algebraic-space definition.

Step 6 takes base changes of that REPRESENTABLE atlas, exactly as the definition of an etale map of sheaves prescribes. The scheme-etale source-locality node proves that a coproduct of identities is etale; etale composition proves that W_beta times V_alpha to V_alpha is etale. The fpqc descent node applies to the scheme map W_beta to U. This avoids assuming the etale algebraic space F_beta to U is representable. The original cover is fpqc by the cited fppf-is-fpqc statement.

Step 7 is elementary evaluation and surjectivity of a representable atlas, as in the quoted definition: a point of U lifts to some V_alpha, its given splitting determines a point in F_alpha, and a nonempty fibre of the surjective scheme atlas has a point with some residue field. No rational point over the initial field is claimed. Evaluating at the identity of W_beta yields the universal isomorphism by the explicit definition of F_beta.

Step 8 uses the existing affine-open-cover statement and the open-immersion/composition clauses of the etale node. Restriction and inversion give exactly the requested direction H|U_j to D(N_j). No finite covering is claimed, and no quasi-compactness is used. The label M_beta already is finitely generated, so no classification theorem for finitely generated abelian groups is needed.

I tested the argument on the empty base, the zero character group, a nonreduced affine base, and M=Z/pZ in characteristic p (so the diagonalizable group is mu_p and is not smooth). The isomorphism labels and character duality remain valid in the last two cases; the proof uses etaleness of the PARAMETER cover, not etaleness of H. For distinct nonisomorphic character groups the corresponding label set is empty, but F_alpha has the given local section on V_alpha, which is enough for joint surjectivity. No uniform character group, connected base, finite constant automorphism group, or finite etale splitting cover is presumed. Aut(M) may be infinite; its set-indexed coproduct is still etale without being quasi-compact.

Against delivery-errors B through E: there are no new nodes to which B1/B2/B6 could fail; the item's notions and statement dependencies are retained. Each cited statement actually supplies the asserted clause (C4), and every additional non-elementary input appears among the uses of that step (C1). The complete argument stays in the item's steps (D1-D3), not in a new equivalent node. Every step is under 2000 characters. The proof avoids the nilpotent and complete-local nodes to prevent circularity (D4). No hypothesis is added or statement weakened (E1-E4). All gluing and comparison formulas used are written explicitly (E5). I corrected the tempting use of a torus-only statement by using the already-general relative character-duality theorem instead.

The split_report.tool_uses declares off-unit foundations as generic tools; these are scheme/topology foundations, not a replacement for a step of the fixed constructible-functor route.

## Unfinished work

None in this one-level split. The dependencies remain their own existing DAG items. Server dry-run and delivery results follow below when available.
