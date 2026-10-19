# Repair report: lem-coef-brown-cocone-equivalence-transport

This is a repair of the returned Q45 delivery. I retained the item statement, endpoint-lifting step, blueprint ancestry, and prior Mathlib search records. I added one strictly smaller generic node and rewrote the mapping-space comparison so the invalid Hom-bifunctor dependency is absent.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-composition.json`: statement-only unsplit child, no Mathlib match. It isolates inverse pre/postcomposition and 2-simplex composition homotopies on complete quasicategorical mapping spaces.
- `dag/nodes/sec-six-functors/lem-coef-brown-cocone-equivalence-transport.json`: repaired five-step split; no Mathlib match.
- `citations.json`: regenerated from the current proof and current node statements, with one verbatim statement quote for every cited node in every step.
- `report.md`: this repair review.

No Lean file, compiler, Lake, build tool, live project, or launcher was written or run.

## Attachments

None. The project source contains no completed declaration tagged `(blueprint: lem-coef-brown-cocone-equivalence-transport)`, and no declaration states the item exactly.

## WANTED

WANTED: archival copy of Cisinski, *Higher Categories and Homotopical Algebra*, CatLR.pdf, for the contextual cocone comparison at printed p. 373.

WANTED: archival copies of Kerodon 046J and 03PD for coherent mapping-space composition and functoriality. The repair does not cite the invalid Hom-bifunctor node; its replacement is proved from the existing canonical-composition node and the displayed inverse/2-simplex calculations.

## Return repair

The returned review invalidated `lem-coef-infinity-hom-bifunctor-functoriality` because its straightening/classification route is circular. The old steps 2–4 and the functor-image clause cited that node for whole-space inverse maps and naturality. I removed every occurrence from the item proof, proof dependencies, and citations. The replacement node `lem-coef-infinity-equivalence-composition` is generic and strictly smaller: it has no cocones, colimit criterion, functor-category endpoint lifting, or Brown argument. Its future proof must use only `lem-coef-infinity-mapping-composition`, whose statement supplies canonical composition, unit and associativity homotopies, inverse-triangle composition, and dependence of pre/postcomposition on component classes.

## Review by Q45

I reread the item, `def-cbc-enhanced-diagrams-cones`, `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-isofibration-exponentiation`, and `lem-coef-infinity-mapping-composition` in the current shared DAG. I also read the new helper statement. It is intentionally unsplit, so its future worker must prove its inverse-edge and 2-simplex clauses from the canonical mapping-composition statement; the current item uses only those stated clauses. The helper statement records the inverse-edge and 2-simplex clauses needed by the item; its future worker must prove that these are homotopies of complete mapping spaces from the canonical composition, unit, associativity, and component-dependence clauses. The helper's search records are the four commands actually run for its own id; LeanFinder and LeanSearch returned only 2-truncated or ordinary-category results, Loogle reported an unknown identifier, and grep had no hits. The whole blueprint and DAG were searched for this generic statement; no duplicate or blueprint statement was found.

For item Step 1, I checked that the cone-calculus statement makes `Fun(K,C)` a quasicategory and gives the pointwise equivalence criterion, that the boundary inclusion is degreewise injective, and that the isofibration node lifts the equivalence edge `(e, Delta_K a)` with prescribed source exactly. The constant-diagram definition supplies inverse triangles for `Delta_K a`.

For item Step 2, the new helper says precisely that precomposition by `a`, `e`, and `Delta_K a` is a whole-space equivalence with inverse induced by the chosen inverse edge. No Hom-bifunctor or extra local-smallness hypothesis is used.

For item Step 3, the two triangular faces of the specified square `H` give the actual 2-simplex relation between `sigma' e` and `(Delta_K a) sigma`. The helper's 2-simplex clause, followed by its fixed-composition stability and the canonical associativity homotopies, gives the displayed homotopy `e^* U_sigma' ≃ U_sigma a^*` on all simplices. The variable has the correct direction `u : p' -> z`, and the two parenthesizations are written explicitly in the step.

For item Step 4, the cone-calculus statement gives the dual mapping-space criterion for a colimiting cocone. Since both vertical maps in Step 3 are equivalences by Step 2, conjugation in the homotopy category of spaces proves the iff in both directions.

For item Step 5, postcomposition by an arbitrary simplicial functor preserves the endpoint square, constant diagrams, and inverse-triangle witnesses degreewise, so Steps 2–4 apply in the target quasicategory without any colimit-preservation assumption. The empty shape is checked directly from the degreewise cocone pullback: its diagram simplicial set is the point and the cocone category is the original quasicategory, so the assertion is initiality invariance.

I verified every current `uses` entry against the cited node's statement and regenerated `citations.json` from those exact statements. The invalid Hom-bifunctor id no longer occurs in the item proof, proof dependencies, or citations. The helper and item have no proof step over 2000 characters. Small cases checked again are the identity edge, an ordinary category nerve, the empty shape, and a target functor that fails to preserve colimits; each gives the stated result without an added existence hypothesis. No SGA source is used.

## Not duplicates

lem-coef-infinity-equivalence-composition vs lem-coef-infinity-relative-hom-evaluation: the new node is a generic statement about inverse pre/postcomposition maps and 2-simplex composition homotopies for one quasicategory; the existing node is a relative, parameterized Hom/left-fibration evaluation transformation for a family (T:K\times C\to E), with no equivalence assertion about its maps and no generic inverse-composition clause.
