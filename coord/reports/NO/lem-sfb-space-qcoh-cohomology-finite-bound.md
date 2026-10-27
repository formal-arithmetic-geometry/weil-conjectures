# Stage-1 delivery: lem-sfb-space-qcoh-cohomology-finite-bound

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-cohomology-finite-bound.json: item, complete five-step split; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-alternating-sign-cohomology-spectral.json: statement, unsplit; no Mathlib match. Alternating configuration spectral sequence, sign local system, and finite abutment filtration (0728, 0727).
- dag/nodes/sec-six-functors-basics/lem-sfb-free-finite-space-quotient-separated.json: statement, unsplit; no Mathlib match. Separatedness of the algebraic-space quotient of a separated scheme by a free finite group (02Z4).
- dag/nodes/sec-six-functors-basics/lem-sfb-separated-space-atlas-cohomology-bound.json: statement, unsplit; no Mathlib match. Separated-space quasi-coherent cohomology bound in terms of an affine atlas (072B).
- citations.json: thirteen step/node records, each quoting the cited statement verbatim.
- searches.jsonl: search-command log; actual queries and results copied into the appropriate nodes.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag, cohomology bounds, alternating spectral sequences, and free finite quotient separation. No declaration states the item. The closest declaration, AlgebraicGeometry.Scheme.exists_quasicoherent_cohomology_bound (QuasicoherentFiniteCohomologicalDimension.lean:102), assumes a scheme over a field with affine diagonal and concerns module cohomology. It is neither the arbitrary algebraic-space theorem nor an attachment. Its proof being closed does not remove its additional hypotheses.

## WANTED

None. All three new results and the item's proof are in the local Stacks source.

## Corrections and route

The imported item was correctly stated but had no proof. It retains its statement and statement dependencies. I read SETUP's chapter/unit/node distinction, both recorded chapter and unit files, and the current blueprint/latest unit and direct-images statement/proof. The historical ancestry has blueprint.from.node null; blueprint_refs.py ancestor confirms None. I retain it and the exact existing via chain. The current paragraph (3) describes direct-image stability through proper and open cases, rather than restating every historical alteration prerequisite. This delivery handles the already recorded ordinary cohomology prerequisite beneath that ancestry; it changes no chapter or unit route. No other unit's theorem is used as a substitute.

The Stacks 072C proof contains the instruction to choose V_p → W_p where the statement specifies V_p → U_p. The subsequent use of 072B is on U_p. I use V_p → Q_p, where Q_p denotes Stacks' U_p, throughout. This corrects a target typo, not the item's statement. Geometric fibre cardinality bounds are used explicitly, avoiding confusion with the number of points in a non-geometric fibre. The 072B proof's finite-configuration argument is valid with these degree bounds. Sign twists are not replaced by invariants of higher cohomology and no factorial is inverted.

The only elementary conclusions are finite arithmetic, the explicitly written finite-filtration induction, local preservation of presentations under an etale restriction and tensoring with a locally trivial integral line, and quasi-compactness of a continuous surjective image. These are steps, not new nodes. The spectral sequence is distinct from ordinary Cech spectral sequences: its terms use unordered *distinct* tuples and integral sign local systems, and terminate in the horizontal direction after a fibre bound. The separated-space input has an additional separatedness hypothesis and a specified atlas bound. It does not restate the qcqs item: the item assembles it on finitely many separated quotients, which themselves are constructed in its proof.

## Not duplicates

lem-sfb-free-finite-space-quotient-separated vs lem-per-admissible-finite-quotient-separated: the existing node assumes a Noetherian base, finite type and an admissible scheme quotient (every orbit in an affine open); the new node concerns a free finite action with an algebraic-space quotient and requires none of those hypotheses. Its scheme quotient hypothesis is unavailable for the configuration schemes here. The existing source mentions 02Z4 only to distinguish it.
lem-sfb-free-finite-space-quotient-separated vs lem-sfb-admissible-free-finite-quotient: the existing node assumes every orbit lies in an affine open and produces a scheme quotient; the new statement proves algebraic-space separatedness without this orbit hypothesis.
lem-sfb-free-finite-space-quotient-separated vs lem-sfb-free-flat-group-space-quotient: the latter gives quotient existence, flatness, local sections and a relation isomorphism for a flat group, but no separatedness conclusion.
lem-sfb-separated-space-atlas-cohomology-bound vs lem-sfb-space-qcoh-vanishing-above-dimension: the existing bound assumes a finite topological dimension bound and uses module cohomology; the new separated-space input uses the geometric fibre bound of a specified affine atlas, with arbitrary dimension and abelian-sheaf cohomology.
lem-sfb-space-alternating-sign-cohomology-spectral vs lem-sfb-space-relative-cech-module-spectral-sequence: the latter is the ordinary full Cech nerve, a relative module-sheaf spectral sequence with arbitrarily long repeated tuples; the new result is global abelian-sheaf cohomology with distinct-tuple symmetric quotients and integral sign twists.
lem-sfb-space-alternating-sign-cohomology-spectral vs lem-sc-cech-spectral: the existing result has E2 page ordinary Cech cohomology of cohomology presheaves on an object of a site, not the configuration-quotient E1 page or its sign local system.

Searched the full DAG by tags 072C, 0728, 0727, 072B, 02Z4, labels and concepts, and searched the whole blueprint with blueprint_refs.py. No blueprint node states any of the three new facts. Apparent raw 0728 occurrences in reviewer identifiers and search digests are not Stacks citations or duplicate mathematical statements. The existing atlas, geometric-fibre bound and distinct-tuple geometry are reused rather than recreated.

## Review by NO

I read spaces-cohomology.tex, lemma-vanishing-quasi-separated (072C), including its finite choices, displayed E1 page and conclusion. For the three new nodes I read lemma-alternating-spectral-sequence (0728), lemma-twist (0727) and its rank-one trivialization on the torsor; spaces.tex lemma-quotient-finite-separated (02Z4), especially its part (2) and the disjoint finite union of graph diagonals; and spaces-cohomology.tex proposition-vanishing (072B) and its alternating-sequence proof. All new nodes introduce their own objects and hypotheses, contain statements only, and have empty proof/proof_deps with null proof_origin. No source forbidden by the route lock is used.

Step 1 uses the exact existing affine-atlas and geometric-fibre-bound statements. The former assumes only quasi-compactness; the latter needs quasi-separated X and quasi-compact source U, both present. Enlarge the chosen bound to d ≥ 1 so the later maximum is indexed by a finite nonempty set. No bound depends on M.

Step 2 uses the actual distinct-tuple geometry statement, with its index shifted: its p factors become this proof's p+1 factors. It explicitly gives quasi-compactness, separatedness, clopen equality loci, and geometric distinct-tuple interpretation. For two factors the equality locus is the relative diagonal, so the atlas is separated as required by 0728. If p ≥ d, a hypothetical point would yield a geometric point and too many distinct members of one fibre. No representability theorem is taken from the proof of the cited node.

Step 3 uses the new 0728 statement for the existence of Q_p, free permutation action, surjective etale quotient and map to X; the new 02Z4 statement for absolute separatedness. The quotient is of a separated scheme, which is exactly 02Z4's hypothesis; I do not assume that the quotient is a scheme or that every orbit has an affine neighbourhood. The atlas-topology definition gives continuity of the scheme-source quotient map. A finite subcover upstairs covers downstairs by surjectivity, proving quasi-compactness. Separatedness gives a quasi-compact diagonal: after scheme tests a closed immersion is affine, with inverse images of affines closed affine subschemes; a finite affine cover then gives quasi-compactness. Thus the existing fibre-bound lemma applies to each newly chosen affine atlas, not to an arbitrary non-quasi-separated space. I opened all six cited statements; the source gives their conclusions, rather than merely defining their names.

Step 4 uses the new spectral-sequence statement for L_p's local triviality and exact E1 coefficient; the quasi-coherent definition for local presentations. On a trivializing cover tensoring with L_p is tensoring with the integral unit, and restriction just restricts the same presentation. Thus the actual O_Qp-module N_p is quasi-coherent. Its underlying abelian sheaf is exactly the coefficient in E1; no module/abelian-derived comparison is invoked. The new separated-space cohomology-bound statement then supplies vanishing for q ≥ d_p with every hypothesis checked in Step 3. The empty quotient has only zero abelian sheaves by the empty covering axiom, giving all degrees in columns p ≥ d.

Step 5 uses only the spectral-sequence statement's finite abutment filtration and the vanishings already proved. I checked the boundary n = C: for every p < d one has n-p ≥ d_p, not just a strict inequality. Each zero entry remains zero under subsequent homology pages. Descending through the finite filtration from its zero endpoint proves the actual abutment zero. This avoids any claim that vanishing in one column suffices, and handles every positive integer degree requested.

I checked the small cases X empty, an affine scheme with its identity atlas (d = 1), sign-trivial p = 0, empty higher configurations, empty Q_p with a harmless bound d_p = 1, and a qcqs space of unbounded Krull dimension. The construction works in all cases. No finite generation of M, Noetherianity of S or X, global dimension bound, or separatedness of X was introduced. The quotient lemma also covers W empty and trivial G; it does not apply to nonfree actions. The spectral sequence covers ordinary integral coefficients, including characteristic two and noninvertible group orders. None of its comparisons is moved silently to invariants of cohomology.

The Mathlib queries were all executed through msearch.py. I read every returned result, including the second phrasings. The scheme-separatedness instances and affine-cover existence results have scheme objects; the ordinary alternating-coface complex only constructs a complex and does not supply this spectral sequence. Read Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:41-74, AlgebraicTopology/AlternatingFaceMapComplex.lean:340-355, and CategoryTheory/Sites/SheafCohomology/Basic.lean:66-86 to confirm these limitations. No result specializes in one line to a new node. Search records are copied from the log; no unavailable service was treated as a negative result.

All five proof steps are shorter than 1100 characters; none hides a long inline comparison. Every non-elementary input has a node citation and a verbatim statement quote in citations.json. No new node is a renamed clause of the item, and all dependencies are strictly below the assembly. The server review_split check passed; the required final delivery dry run is recorded below after completion.

## Unfinished work

No unfinished part of this one-level stage-1 split. The three new statement-only nodes remain for later workers. No Lean was written or compiled.

## Validation

Server review_split: PASS. First deliver.py --no-push: OK at 32419ad268f. Final rerun after adding the explicit closed-immersion-definition citation: OK at 07995dbe37e. All server preflight checks passed.
