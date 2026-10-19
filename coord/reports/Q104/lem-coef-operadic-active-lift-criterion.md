# Stage-1 Q104 direct repair

## Files written

- dag/nodes/sec-six-functors/lem-coef-operadic-active-lift-criterion.json: split item; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-operadic-minimal-interval-reflection.json: new statement-only prerequisite, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-generalized-operadic-fibration-replacement.json: new statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: thirteen current-statement quotations covering every cited node of every item step.
- report.md, retained-proof.json, prior-report.md, prepare.py and searches.jsonl: review, retained arguments, historical report, preparation script and actual search log. These supporting sandbox files are not proposed library files.

## Attachments

None. Searches of both authorized read-only WeilConjectures trees for the item id, operad terminology, active lifting and weak approximation found no declaration stating the item. Neither audit supplies one. The upstream master is reference material only.

## WANTED

WANTED: archived Gepner–Haugseng, Enriched infinity-Categories via Nonsymmetric infinity-Operads, arXiv:1312.3178v4, Definition A.6.1, Proposition A.6.3 and Erratum Proposition E.0.2, for the item and both new prerequisites. I read the online source at https://arxiv.org/html/1312.3178. No Stacks tag states these infinity-operadic assertions. The new prerequisites are explicitly agent-formulated extractions of the retained argument, rather than claimed verbatim numbered theorems of the paper. The proof remains agent-written. No SGA source is used.

## Returned findings and repairs

I read the dedicated handoff in coord/returns/Q104.md. It requires extracting the arguments hidden in non-elementary Steps 3 (2070 characters) and 5 (3514 characters), retaining the statement, route and other steps. I copied the current repository item into the previously empty sandbox and preserved its full old proof as retained-proof.json and its historical report as prior-report.md.

Step 3 now applies the minimal-interval reflection prerequisite. That prerequisite states its own objects, the full factorization category, the precise minimal subcategory, the adjunction, the representing mapping-space equivalence, and the restriction describing the unit. Its comparison edges are unrestricted. It assumes no contractibility. It is the intermediate reflection argument, not the weak-approximation conclusion.

Step 5 now applies the strict categorical-fibration replacement prerequisite. It gives an equivalence of generalized operads with an operadic quasi-inverse, a categorical fibration, exact equality of simplicial maps, the same universe, and the Kan zero-fiber and incidence axioms. It applies even to a generalized target. It asserts no weak approximation or active lifting criterion. The old step's substantial verification that an underlying Joyal replacement retains the operadic structure is therefore a separate task.

The other five steps, statement, source and Lean metadata are unchanged. The item proof dependencies are recomputed from the step uses; the formerly direct Joyal and pointwise-adjoint tools now belong to the future proofs of the extracted tasks. No generic off-unit theorem is needed directly by the new item proof. Chapter, unit, blueprint ancestry and maintainer fields are retained, and no unit record is changed.

## Not duplicates

- lem-coef-operadic-minimal-interval-reflection vs lem-coef-operadic-active-lift-criterion: the new assertion constructs the reflector on factorization triangles for any base arrow; it asserts no weak approximation or contractibility criterion.
- lem-coef-operadic-minimal-interval-reflection vs lem-coef-infinity-pointwise-adjoint-criterion: the existing criterion assembles adjoints from representability; it does not prove representability for this operadic category or provide its interval restriction.
- lem-coef-operadic-minimal-interval-reflection vs lem-coef-infinity-cocartesian-composition-initiality: the existing result concerns individual lift categories and composites; it does not supply this full factorization-category adjunction.
- lem-coef-generalized-operadic-fibration-replacement vs lem-coef-operadic-active-lift-criterion: replacement is independent of any weak-approximation predicate and imposes no active-lifting contractibility assumption.
- lem-coef-generalized-operadic-fibration-replacement vs lem-coef-infinity-relative-joyal-factorization: the latter concerns extension over a particular 3-horn; it neither supplies this operad structure nor factors an arbitrary operadic map.
- lem-coef-generalized-operadic-fibration-replacement vs lem-coef-symmetric-operadic-fibration-recognition: recognition uses a symmetric pattern over Fin_* and relative product hypotheses; it does not give strict replacement of generalized nonsymmetric operads over Delta-op.
- lem-coef-generalized-operadic-fibration-replacement vs lem-coef-categorical-pattern-model-calculus: the general pattern model structure does not by itself state this unmarked underlying categorical-fibration replacement or its generalized operadic quasi-inverse.

I searched the whole DAG for interval/reflection, operadic replacement, categorical fibration and equivalence transfer, and opened the closest statements. Whole-blueprint searches for operad, reflection, fibration, A.6.3 and E.0.2 yielded no equivalent blueprint node; generic equivalence hits do not state either prerequisite. The ancestor tool confirms prop-coef-integral-exceptional-adjoint. Both new nodes extend the item's recorded ancestry through the item, with the exact finite-coefficient adjunct/operadic place retained.

## Mathlib searches

All new-node searches were run through msearch.py and are recorded exactly by query and tool in the nodes and searches.jsonl. Both first and second semantic phrasings were read. LeanSearch was available. The initial reflection Loogle query rejected an unknown Full identifier, so I followed it with the successful CategoryTheory.reflector query. Ordinary reflectors, ordinary factorization categories, ordinal epi-mono decomposition, model-category factorization and ordinary cocartesian arrows do not state either prerequisite for quasicategories with coherent triangles.

The follow-up grep reads Reflective.lean lines 38, 47 and 50: it assumes an ordinary Reflective structure, so it does not establish our reflection. ModelCategory.Basic lines 49 and 63 assume a model structure; its factorization clause does not transfer generalized operadic axioms to an underlying Joyal replacement. JoyalTrick concerns lifting properties in an abstract model category. The broad operad grep found only bibliography entries and absolute-value approximation. No result is an exact match or one-line specialization. Neither new node is marked mathlib.

## Review by Q104

I read AGENTS.md, the worker/stage-1 brief, stages/1-dag.md, SETUP.md's three levels, GOAL.md, coord/dag-sync.md, the chapter and unit records, and delivery-errors B–E in full. The actual new work is the dedicated re-split, not a statement repair. In Gepner–Haugseng I read Definition A.6.1's factorization category and exact factorization clause, A.6.3's categorical-fibration case, and the corrected Erratum E.0.2 statement. The item matches E.0.2: ordinary target, generalized source, inert-preserving map, every C and active alpha, the complete lifting category, no positive-arity space hypothesis. There is no statement dispute.

For the reflection prerequisite I used A.6.1/A.6.3 and reread the retained original Step 3. Its subclaim has its own hypotheses and conclusion and requires the cocartesian mapping-space criterion plus pointwise adjoint assembly. It is not an elementary fact; it is now statement-only. The base equation j_A eta=j_B forces eta(j)=a-t+j even for arbitrary comparison edges, so it applies to the full category in the current definition. This equation and the representing mapping equivalence are retained in the old argument for its future worker.

For the replacement prerequisite I used the replacement clause of A.6.1 and reread the original Step 5, the Joyal model-structure and quasicategory-characterization statements, the cocartesian mapping-square statement and the functor/core calculus statement. The old argument contains exactly the Joyal factorization and nontrivial transfer of generalized Segal/incidence and inert-edge data now assigned to the new node. I do not claim that A.6.1 alone proves those transfers. The new node records this as an agent-formulated prerequisite, with no proof of its own.

I opened every statement cited by the final item and checked the actual clauses:

1. Step 1 uses the weak-approximation definition for the join-slice full factorization category, the operadic statement for the endpoint/inert convention, and the cocartesian mapping-square criterion to identify a cocartesian identity-base edge as an equivalence. The endpoint calculation forces the entire interval. Inverting the equivalence compares the coherent triangles with the lifting homotopy fiber. This remains one argument, with its higher data explicit, and is below 2000 characters.
2. Step 2 uses those same statements. The opposite order map factors through [phi(0),phi(k)]; the target has the specified inert lifts and its projection is an inner fibration, as the mapping-square criterion requires. The contractible factorization space and comparison of two such lifts identify A_0 with the active factorization category. No unproved contractibility of the final lifting category is assumed.
3. Step 3 uses exactly the new reflection statement. Its generalized source, ordinary target, categorical-fibration, inert-preservation, arbitrary arrow and full-category hypotheses match the objects fixed in Steps 1–2. Its A_0 is literally the same subcategory, and it states the unit and equivalence counit used in Step 4.
4. Step 4 uses the weak-approximation definition's all-arrows criterion and diagrams/cones' definitions of coherent transformations and realization. The written standard simplex-prism argument gives the homotopies from the unit and counit already supplied in Step 3. It then combines Steps 1–2 with that homotopy equivalence. Its elementary label refers to this explicit realization calculation and combination of established assertions.
5. Step 5 uses exactly the new replacement statement, whose conclusion supplies every structural property required in the following steps, including the strict equality f=ge and an operadic equivalence, rather than just a bare underlying equivalence.
6. Step 6 uses diagrams/cones for quasi-inverses, coherent comparisons and homotopy fibers, and the operadic statement for the base/active convention. The displayed inverse slice functor and its counit comparison f r=g e r equivalent to g explicitly give inverse operations on the pullback data. Essential surjectivity handles objects outside the image. Base equivalences in Delta-op are identities, so activeness is preserved. This is an elementary inverse calculation, retained exactly.
7. Step 7 uses the current weak-approximation definition's strict existential factorization. Forward uses its witness, Step 4 and Step 6; reverse uses the new Step 5 witness and the same two steps. Its equality and hypotheses therefore agree with the definition.

I checked B–E against the delivered records. Both children are self-contained statement-only nodes with no proof or proof dependencies. All their notions have cited definitions, TeX is singly escaped, source places are explicit, blueprint fields complete, and their search records come from actual commands. Neither child states the item's weak-approximation equivalence or one of its implications. The new proofs remain future tasks rather than hidden arguments still left in the item. All item step uses are covered by verbatim quotations of current statements; no proof-body-only claim is taken from a citation.

Small cases: for reflection, active alpha has [a,b]=[0,n] and A_0=F, so the reflector can be the identity; k=0 gives a=b and restriction to a vertex; n=0 gives only [0,0]. For an empty F both the full subcategory and reflection are empty, and no false nonemptiness is asserted. The identity map satisfies replacement with itself and its own generalized structure; for an empty source no nonempty object is forced; Kan zero fibers and nullary incidence are explicitly retained. A generalized target is allowed in replacement because the old Joyal/inert transfer argument uses its inner fibration and inert lifts, not its ordinary Segal product formula.

I inspected all final non-elementary steps: their lengths are 1941, 1379, 768 and 749 characters. The two flagged long arguments are now separate tasks. No compiler, Lake, local DAG/preflight/review tool, live-project write, git command in the shared repository, or subagent was used. Required server dry run and direct delivery follow.
