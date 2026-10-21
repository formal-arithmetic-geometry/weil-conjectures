# Worker report — Q126

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-curve-testing-irreducibility.json`: existing item re-split; its statement is byte-for-byte unchanged. Six assembly steps, 2341 characters in total, replace the returned 4739-character proof.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-common-irreducibility-detecting-cover.json`: new statement-only lemma, status `unsplit`, no proof steps or proof dependencies, no Mathlib match after seven logged searches.
- `citations.json`: verbatim statement extracts for every citation of every parent step.

## Attachments

None. `AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`, `lean/WeilConjectures/DeligneLaumon/Reduction/RealSheaves.lean:111–137`, has `sorry` in its own proof. The upstream finite-matrix theorem belongs to the existing node `lem-zl-finite-matrix-irreducibility`, not to the new common-cover lemma. The project source contains no theorem giving the common-cover statement.

## WANTED

None. The current blueprint statement and proof, the cited DAG statements and the relevant Stacks sources are available locally. No SGA source is used.

## Repair of the return

The sandbox initially contained only dispatcher marker files: no retained item, report, citations or searches. I copied the current read-only repository item and retained its statement, historical fields, previous searches and blueprint update. The returned proof is the current repository's eight-step proof, so it supplies the comparison head. This is a mathematical re-split, not an unchanged re-push.

The human requests distributed work, at least one substantive new statement-only node, and a parent proof of at most 3000 characters. The common-cover lemma is strictly smaller than curve testing: it has no smoothness, dimension, finite field, prescribed points, curve, closed immersion, Bertini conclusion, or Frobenius datum. It isolates the representation/coefficient/finite-cover argument and can be worked on separately from Bertini and the parent assembly. Its eventual proof contains the following complete argument, recorded here rather than inside its statement-only node:

Choose finite coefficient fields for the finitely many lisse sheaves using `def-pod-lisse-l-adic-sheaves`(4). Apply the exact stalk equivalence of `cor-galois-lisse-representations`(2) to get continuous finite-dimensional representations; the given irreducibility makes their scalar extensions absolutely irreducible. Apply the statement of `lem-zl-finite-matrix-irreducibility` to each representation, obtaining a stable full lattice and a reduction exponent. Continuity makes each reduction kernel open and normal; the finite intersection K is again open normal. Set Q=Pi/K, with its quotient map q. Each reduction factors through Q and q induces a surjection onto its reduction image. The regular Q-set with Pi-action through q corresponds, under `thm-galois-fundamental` (Stacks Tag 0BND, `pione.tex`, `theorem-fundamental-group`(1)), to a finite etale cover T. Its transitive fibre makes the cover connected, using the equivalence and Stacks Tag 0BNB (`lemma-finite-etale-connected-galois-category`); the open-subgroup classification `cor-galois-open-subgroups` equally supplies the cover for K. If q(H)=Q, then every group element has an H-element with the same Q-image and hence the same image on every chosen finite lattice quotient. Apply the finite-matrix statement again to conclude absolute irreducibility on H for all j. For r=0 the empty kernel intersection is Pi, Q is trivial and T=X. This construction includes all the coefficient, stable-lattice, finite reduction and common quotient work from the old proof; none is replaced by a vague assertion of irreducibility.

Every old argument has an explicit home:

1. Old step 1 (finite coefficient geometric representations) is in the new lemma's finite E_j, continuous rho_j and equivariant scalar-extension isomorphisms. The original invariant-lattice requirement is supplied by its L_j. The parent uses this on the geometric local systems underlying the Weil sheaves.
2. Old step 2 (finite matrix witnesses) is in the new lemma's L_j,N_j and universal detection conclusion; its future proof uses the existing finite-matrix lemma, rather than restating Burnside's argument.
3. Old step 3 (intersection of open normal kernels and finite Galois cover) is in the exact kernel-intersection equality, continuous surjective q, connected finite etale T and equivariant regular fibre of the new lemma.
4. Old step 4 remains parent step 2, by the unchanged Bertini lemma, including its finite-field/Frobenius conclusion. The product computation phi=id x sigma^m remains parent step 5.
5. Old step 5 remains parent step 3: connected scheme -> connected Galois object -> transitive restricted fibre, whose orbit of 1 is q(H), so q(H)=Q.
6. Old step 6 is divided precisely: equality of reduction images and the finite-matrix consequence are the new lemma's universal detection property. Parent step 4 retains the full justification that the pulled-back sheaf has the restricted action: finite-level fibre base change, inverse limits, rationalization, coefficient extension, and the exact lisse stalk equivalence. Thus the sheaf conclusion is not inferred from an uncited identification.
7. Old step 7 remains parent step 5: iterate the Weil datum m times and pull it back along the Frobenius-equivariant immersion, giving the actual inherited Weil isomorphism.
8. Old step 8 remains parent step 6, C=X and m=1 in dimension one.

No statement dispute or route departure is involved. The source field now points to the current main-20261015 statement (order 3176), following the existing blueprint_update and the earlier maintainer review. All blueprint_* historical fields remain intact.

## Searches and Not duplicates

I searched the entire DAG statements for detection/irreducibility, finite reduction images, regular finite-group fibres and connected pullbacks; inspected the existing finite-matrix, fundamental-group, open-subgroup and lisse-representation nodes; and ran blueprint_refs searches for `monodromy`, `torsor`, `finite quotient`, `irreducibility`, `irreducible lisse`, `finite etale Galois cover` and `lisse`. The ancestor command returns the item itself, so the new node has that blueprint ancestor with empty via and no same_as match. These searches found ingredients, not the combined sheaf-family common-cover assertion. Broad searches also found unrelated roots, torsors, and geometric irreducibility statements, which are not used as replacements.

## Not duplicates

lem-zl-common-irreducibility-detecting-cover vs lem-zl-finite-matrix-irreducibility: the existing lemma treats one given profinite representation, its lattice and a finite congruence witness; it neither descends a family of sheaves to finite coefficient fields nor constructs a single connected finite etale cover with its specified regular fibre.

lem-zl-common-irreducibility-detecting-cover vs thm-galois-fundamental: the latter supplies the generic finite-cover/fibre equivalence and base-change compatibility; it does not supply coefficient representations, lattices or an irreducibility-detecting finite quotient for a family.

lem-zl-common-irreducibility-detecting-cover vs cor-galois-open-subgroups: the latter classifies connected covers by open subgroups, and has no lisse coefficient representations or detection property.

lem-zl-common-irreducibility-detecting-cover vs cor-galois-lisse-representations: the latter supplies the exact stalk equivalence; it does not produce a simultaneous finite quotient, stable lattices, congruence exponents or a common detecting cover.

lem-zl-common-irreducibility-detecting-cover vs sbc-thm-spreading-finite-etale-galois: the latter spreads geometric-generic covers over a normal integral base; no spreading is asserted or needed by the new lemma, whose input is instead a family of irreducible local systems on one connected scheme.

lem-zl-common-irreducibility-detecting-cover vs lem-zl-curve-testing-irreducibility: the new lemma ends with finite monodromy detection on arbitrary subgroups and contains no curve or geometric slicing conclusion. The parent still needs Bertini, the transitivity computation and pullback functoriality.

All seven Mathlib queries were executed by the required msearch.py, and their exact tool/query strings and actual results are in the node and searches.jsonl. Both semantic phrasings were read. LeanFinder returned abstract Galois category infrastructure on the first query and ordinary irreducibility/profinite invariant algebra on the second. Loogle's combined Galois/irreducibility query returned no hits; the second returned Representation.IsIrreducible and Schur-type consequences. LeanSearch returned etale algebra decompositions and topological irreducibility. Grep found no relevant geometry declarations and only order-lattice/ordinary irreducibility results in RepresentationTheory. I read Mathlib RepresentationTheory/Irreducible.lean:25–40 and CategoryTheory/Galois/Decomposition.lean:310–319: neither is an exact or one-line specialization of the new statement. There are no Mathlib leaves in this delivery.

## Review by Q126

I read the current blueprint's complete statement and proof for the item, and its complete finite-matrix statement/proof and finite-cover Bertini statement, plus RealSheaves.lean:103–137 and FiniteMatrixWitness.lean's module docstring. The main blueprint already gives the finite-quotient route used by the returned proof. The common-cover source is the first six sentences and the finite-matrix detection sentence of that proof. The old finite-matrix DAG statement directly provides stable lattices; the updated generalized blueprint formulation assumes an integral basis but its proof explains lattice existence. The new node requires only existence and does not silently strengthen the theorem to an arithmetic Frobenius-stable lattice, which is unnecessary and not supplied. I read Stacks pione.tex, Tag 0BNB at lemma-finite-etale-connected-galois-category and Tag 0BND at theorem-fundamental-group, especially the connected-object equivalence, regular finite-set realization and base-change square. These support the extracted construction and the retained transitivity argument without an SGA citation.

For parent step 1, I read the new node's entire statement: it supplies the finite cover, the precise regular fibre and detection property actually used. The sheaves are the geometric local systems of the hypotheses; smooth affine finite type X over the algebraic closure is connected, Noetherian, separated and has ell invertible, so every hypothesis of the new node holds. I chose a fixed s in the nonempty S before forming the cover, and later choose its lift on C. This removes the old postponed-basepoint convention and avoids claiming an uncited basepoint-transport statement.

For step 2, I read lem-zl-bertini-finite-cover-curve: it assumes exactly smooth geometrically connected affine X_0, d>=2, connected finite etale T, and a nonempty finite S. It explicitly concludes the smooth connected affine closed curve, containment of S, connected pulled-back cover, positive m and Frobenius equation. No smoothness or irreducibility theorem is smuggled into this application.

For step 3, I read lem-galois-finite-etale-connected-object (scheme connectedness gives a connected object), lem-galois-transitive (connected Galois object gives transitive fibre action), and thm-galois-fundamental's base-change clause (identifies this fibre action through i_*). Their hypotheses hold because C is connected, T times_X C is connected finite etale, and the fixed base point factors through C. The only remaining inference is the explicit elementary orbit computation q(H). No claim that i_* surjects onto the entire profinite group is used.

For step 4, I read the new detection clause and thm-galois-fundamental's natural finite-level base-change identification. I also read all five clauses of def-pod-lisse-l-adic-sheaves and clause (2) of cor-galois-lisse-representations: the former specifies the inverse-limit, rational and scalar-extension fibres, and the latter is an exact equivalence for Noetherian separated schemes with ell invertible. Both X and C meet those hypotheses. Thus the natural finite-level action really becomes rho_j composed with i_*, and the equivalence carries the absence of invariant subspaces to the absence of lisse subsheaves. I added the explicit exact equivalence citation, instead of asking a definition to prove irreducibility.

For step 5, I read the Frobenius/descent clause of the Bertini node and the defining Weil isomorphism in def-wf-fundamental-representation. Iterating that isomorphism m times and using i composed with phi = Phi_X^m composed with i gives precisely phi^* i^* S_j isomorphic to i^* S_j. This is a short manipulation of the supplied data, correctly marked elementary. The explicit finite-field product formula preserves the returned proof's descent calculation.

Step 6 is the identity restriction in dimension one, with the given finite-field model, so it is elementary without citations. Edge cases checked for the new node include r=0 (trivial Q and T=X), rank one (any restricted action remains irreducible), and X a geometric point (trivial fundamental group, so only rank-one irreducibles). Rank zero is excluded by the nonzero definition of irreducible. The parent handles d=1 separately and never applies Bertini there; repeated prescribed points are irrelevant because S is a set. Lattices are required only for geometric compact monodromy, not the Weil Frobenius operator.

Against B–E: the child introduces every object and has statement-only status unsplit; definitions of lisse sheaf, continuous representation, finite etale fibre and fundamental group are cited, while lattice and irreducibility meanings are written explicitly. It has genuine sources, seven real searches, blueprint provenance, and no proof sketch inside its statement. The extracted task includes several theorem applications and a cover construction, so it is not a two-line elementary node, a new name for a clause of curve testing, or an entire proof moved wholesale. Every parent citation was opened and its actual statement checked above; citations.json records verbatim parts, not inferred paraphrases. No new dependency points back to the parent. No non-elementary parent step is over 2000 characters, and the complete parent proof is below the 3000-character return limit. The new proof task is deferred as requested, with all of its argument preserved above for the next worker.

The off-unit tools thm-galois-fundamental, lem-galois-finite-etale-connected-object, lem-galois-transitive and cor-galois-lisse-representations are declared in split_report.tool_uses: these are generic foundational interfaces for covers and local systems; they do not replace the unit's Bertini/finite-matrix route. I retained pre-existing maintainer metadata and did not set new top-level tool_uses.

## Unfinished work

Only the proof of the new statement-only child is deferred to its own stage-1 worker, exactly as the re-split instruction requires. No Lean file was written and no compiler, Lake or build tool was run.
