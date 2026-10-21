1. Files written

- `dag/nodes/sec-poincare-duality/lem-pod-formal-verdier-exchange-equivariance.json`: existing statement, split into eight steps; no exact Mathlib match. Statement, statement dependencies, source and imported/creation metadata are unchanged.
- `citations.json`: verbatim statement witnesses for each node cited in the proof.
- `searches.jsonl`: the search command's own log, retained without editing. The inherited Mathlib records are retained and the five newly executed searches are appended to the item.
- `report.md`: this report. `write_split.py` is sandbox-only preparation code, not a DAG delivery file.

There are no new nodes and no new Mathlib leaves.

2. Attachments

None. I searched the current project source for the item's blueprint tag and for Verdier/duality equivariance. I read WeilSheaf/Operations.lean and WeilSheaf/VerdierDual.lean: the former explicitly says the comparison-equivariance infrastructure is incomplete, while the latter's relevant duality preservation, biduality and exchange statements contain `sorry`. Their category of derived Weil sheaves is also not automatically the rational fixed-pair category in this item. The generic IsoAlgebraAdjunction.lean proves lifted adjunction facts but does not give all clauses of this item. None is an exact attachment.

3. WANTED

None. This proof expands the current blueprint using existing DAG statements and elementary categorical formulas; it does not invoke a missing external reference.

4. Problems found and repairs

The item was statement-only, with no proof. I preserved its conditional domains and its distinction between constructible exceptional adjoints and ambient exceptional admissibility. The preliminary duality and coefficient assertions already have the exact existing node cor-coef-verdier-weil-equivariance, so creating separate new nodes for them would duplicate it. The rest is elementary once the lifted functors, adjunctions, evaluation and compositor in the hypothesis are supplied. I wrote their component formulas instead of introducing nodes for mere composition, inverse equivariance, or transposition. The canonical exchange normalization is stated in the existing def-sf-verdier-exchange-data; this avoids an unproved identification with some unspecified isomorphism. No source or statement dispute was found. The unit's finiteness theorem is not this item's statement, so its realization fields are not changed.

5. Unfinished work

None for this one-level split. Existing dependency nodes retain their own proof obligations. No Lean was written or compiled, and no repository or launcher file was changed.

## Blueprint and Mathlib searches

I searched the complete imported blueprint with blueprint_refs.py for `Verdier`, `equivariant` and `transpose`, and searched DAG statements for duality, coefficient comparisons and mate coherence. The ancestor command gives prop-weil-operations. The nearest exact match for the first clause is cor-coef-verdier-weil-equivariance; fix-cor-verdier-exchange supplies the specified conditional isomorphism, not all of this item. There is no blueprint node stating this entire construction and all its clauses, so same_as remains empty. The eight steps expand sentence 4 of prop-weil-operations.proof.md in main-20261015.

The five new searches were run through msearch.py: two differently phrased LeanFinder queries, Loogle for Adjunction and ihom, grep for Verdier/dualizing/IsoAlgebra, and LeanSearch for equivariant exchange. All services answered. I read the returned declarations/types: ihom.adjunction and mateEquiv are general categorical tools, and frobeniusMorphism_mate and its neighbors concern Cartesian closed functors, not the geometric Frobenius action on rational Weil complexes. The grep hits are textual dualizing mentions. None covers the item even by a one-line specialization. No invented or unavailable search result is recorded.

## Not duplicates

No new nodes. Reused cor-coef-verdier-weil-equivariance for the existing coefficient-duality theorem rather than restating it. Reused fix-lem-tensor-adjunction, fix-cor-verdier-exchange and their canonical-map definition only for the invertibility clause explicitly present in the item.

## Review by O3

I read the current item, its chapter and unit records, and the source prop-weil-operations.md/.proof.md in main-20261015. The source's fourth sentence says to use the same evaluation and adjunction maps; it does not itself calculate their transposes. I also read the current blueprint cor-coef-verdier-weil-equivariance.md/.proof.md and fix-lem-tensor-adjunction.proof.md and fix-cor-verdier-exchange.proof.md, and the full statements of every cited DAG node. This review is the author's self-check, not an independent review.

Step 1 uses precisely cor-coef-verdier-weil-equivariance: its statement gives contravariant duality, evaluation, biduality, the two finite scalar-extension comparisons, their diagrams, the common-stage assertion, and absence of a stable-lattice requirement. I checked separatedness of X_0 and Y_0, finite type, distinct primes and the rational coefficient fields against its hypotheses. I do not use the corollary to infer a tensor-Hom preservation theorem on a larger domain.

Step 2 uses its evaluation assertion at Rf_!M and the morphism equation in def-weil-weil-sheaf-complex. The projection isomorphism is supplied in the item's hypothesis: I do not invoke an unproved projection formula. Multiplying the Weil equation on both sides gives the inverse's equation, and substitution gives the composite's equation. The factor order is Rf_!M tensor A, the evaluation order already in that corollary. These are two-line consequences, not separate new lemmas.

Steps 3 and 4 have no external theorem invocation. They use exactly the assumed lifted adjunctions. I checked all three types: V -> G omega_Y, PA -> Hom(M,G omega_Y), and A -> Q Hom(M,G omega_Y). Each transpose is its unit followed by the right adjoint of the preceding arrow. Equivariance follows because both factors are already arrows of Weil pairs. The tensor-Hom adjunction is used only on the domain expressly supplied in the statement. Thus no unsupported generic theorem is being hidden behind the word transpose.

Step 5 uses the formula actually stated in def-weil-pbc-adjunction-mate, not a claim that arbitrary mates of isomorphisms are invertible. For alpha:HF -> U, alpha^{-1} at GJZ has source U(GJZ); the pasted counit ends in Z, and transposition under U adjoint W therefore has target WZ. The formula in the proof is typed exactly this way. The unit, the two counits and the compact-support compositor are the equivariant data assumed by the item. At Z=Lambda_s it gives the specified c; its invertibility is part of the specified composition comparison, not inferred from equivariance.

Step 6 applies only the supplied lifted Hom and ordinary direct-image functors to c, then composes. The resulting underlying map has exactly the pairing and three transposes fixed in Steps 2–4. This checks map identity, rather than merely establishing the existence of some equivariant isomorphism.

Step 7 uses the actual statements of fix-lem-tensor-adjunction, fix-cor-verdier-exchange and def-sf-verdier-exchange-data. The definition explicitly specifies the evaluation/projection/transposition arrow, the composition mate, and the auxiliary inverse tensor-Hom exchange with substitution. Its order of substitution is before the last two transposes. I checked the unit formula R(vh)eta = R(v)R(h)eta, which moves that substitution through them and identifies its map with Step 6. Only after this identification do I invoke the corollary's isomorphism assertion. I retain all the admissibility, finite-Tor and operation-datum hypotheses of those theorems in this conditional step; they are not added to the preliminary operation lifts or to the formal equivariance argument. These three off-unit statements are declared as tools (the map-definition node is a definition), for exactly the clauses the item explicitly asks to compare.

Step 8 is again the explicit inverse Weil equation from Step 2. It uses no theorem about preservation or a new domain. It also records why the formal construction uses only rational arrows: none of the steps chooses a lattice or reduces a rational Frobenius automorphism.

For the B–E checklist, every cited statement is quoted verbatim in citations.json and supplies the asserted input; hypotheses were checked above. There are no new unsplit nodes with disguised proofs, elementary nodes, duplicates or unlogged searches. No proof uses another node's proof as an unstated interface. No step exceeds 2000 characters, and each elementary step is a displayed unit/composition calculation from the assumed data. The statement and its definitions are retained. The proof follows the source's evaluation-and-adjunction route and cites no SGA source.

I tested the formulas on f=id (unit/compositor identifications give the identity exchange), M=0 (both duality outputs and all maps are zero), and the empty source (the same zero-object case). On a point with an arbitrary invertible Frobenius operator T on M, the dual action is precomposition by T^{-1}, so evaluation is invariant; this also checks that using theta^{-1} is essential. Scalar extension E=L gives identity comparisons; passage through a larger common field uses exactly the corollary's stated comparison diagrams, not a newly asserted integral descent result. No counterexample or missing hypothesis appeared.
