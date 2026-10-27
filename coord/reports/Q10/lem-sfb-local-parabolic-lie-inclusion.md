# Stage-1 delivery: lem-sfb-local-parabolic-lie-inclusion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-parabolic-lie-inclusion.json: statement, split; unchanged statement, six proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-parabolic-cocharacter-description.json: new statement-only prerequisite; unsplit; no Mathlib match.
- citations.json: exact statement quotations for every step/use pair.
- searches.jsonl: search-command log, read before recording results.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and for parabolic subgroup, Borel subgroup and cocharacter; there is no declaration giving the item. Unrelated Borel–Moore and abstract Lie algebra occurrences are not attachments.

## WANTED

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Proposition 5.2.3, printed pp.152–153; Corollary 5.2.7(2), printed p.155; Theorem 4.1.7, pp.112–114; for the item and lem-sfb-local-parabolic-cocharacter-description. The primary author PDF was read online; it is absent from local literature. No download or literature edit was made. proof_origin.by is agent as required when the local document is missing.

## Corrections and scope

No statement dispute: the imported statement is true with the common maximal torus assumption. I retained every clause and the existing statement dependencies. The previously empty proof is now explicit. The proof only needs a cocharacter for P, not another for Q: its conjugation action preserves Q. The reduction argument eliminates negative integer weights by Nakayama, avoiding an implicit claim that arbitrary subspaces lift uniquely. It never infers subgroup containment solely from containment of underlying geometric points. The local-ring property makes every open neighbourhood of the closed point the whole spectrum: a basic neighbourhood D(f) has f outside the maximal ideal, hence f a unit. This is why Conrad's Zariski-local cocharacter description supplies a global cocharacter here.

Conrad's displayed nonnegative root signs can be rendered as > by PDF text extraction. The proof uses the correct nonnegative inequality, as Theorem 4.1.7 states. In particular lambda=0 gives P=G.

The chapter and unit records and the current latest direct-image proof were read. This is a supporting input below the inherited alteration prerequisite chain; no unit route is changed. blueprint_refs.py ancestor returns None; that inherited null and via list are retained, with the new node's via starting with the item. Searches of the full blueprint for parabolic, cocharacter, root space, local parabolic and limit subgroup found no equivalent blueprint item.

## Mathlib searches

All new recorded queries were actually run through the required msearch.py command, and searches.jsonl was read. LeanFinder was tried with the Lie-inclusion statement, with the root-generation formulation, and with two different cocharacter-description phrasings. Loogle patterns were "Parabolic", "Lie" and "cocharacter". LeanSearch used both a nonnegative-weight formulation and the local-base cocharacter formulation. The AlgebraicGeometry greps were parabolic|Parabolic|Borel and cocharacter|Parabolic|parabolic. The semantic hits are abstract root pairings/Lie algebras, Iwasawa structures and parabolic matrices; none states the relative scheme theorem. Zero grep and Loogle hits agree. No unavailable service is recorded as a negative answer. Previous item searches are retained.

## Not duplicates

lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-local-parabolic-lie-inclusion: the new node describes one parabolic using an actual cocharacter; it asserts no comparison, Lie-detection implication, equality criterion or Borel weight criterion. Steps 2–6 carry those arguments.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-split-parabolic-root-sign-cone: the existing theorem is over a field and gives the root-sign cone; the new theorem lifts the dynamic description over a possibly nonreduced Noetherian local base.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-parabolic-prescribed-split-cocharacter: the existing theorem is over a field, whereas the new statement is relative over a local ring. The new input is precisely the extension over the base.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-relative-dynamic-subgroups: the existing theorem constructs P_a for an already supplied action and describes its tangent module; it does not say that a supplied parabolic equals P_lambda for some cocharacter of its specified maximal torus.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-reductive-cocharacter-parabolic-geometry: the existing statement starts with a cocharacter over a field and constructs its parabolic; the new statement starts with a relative parabolic and supplies a cocharacter.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-regular-cocharacter-borel-description: the existing theorem concerns Borels over algebraically closed fields, not relative parabolics over rings.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-local-borel-quotient-geometry: the existing statement supplies the radical and quotient of a relative Borel, not the cocharacter description, and covers only Borels.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-split-positive-root-borel: the existing statement constructs a Borel from a pinned realization; it does not describe a supplied arbitrary parabolic by a cocharacter.
lem-sfb-local-parabolic-cocharacter-description vs lem-sfb-relative-root-product-open-cell: the existing statement constructs root-product Borels and an open cell; it does not classify a supplied parabolic.

## Review by Q10

I read Conrad Proposition 5.2.3 and its full proof, pp.152–153, for the new node and Corollary 5.2.7(2) and its proof, p.155, for the item. The new statement is a supporting existence theorem about one parabolic; it leaves no proof in its statement and does not repeat the item. Its object definitions are either inline (relative group diagrams, torus, reductivity, parabolicity, solvability and limit condition) or cite the existing scheme-property definitions. It needs no smoothness of an intersection inferred without proof.

For step 1, I read finite-type-algebra-noetherian and checked the base is Noetherian and the coordinate algebra finite type; a quotient ideal is finite, so P and Q satisfy finite presentation. I read the new statement and checked it applies to the actual P with the specified T, not to a newly chosen conjugate. The torus normalizes Q because it is contained in Q.

For step 2, I read the statement of relative-tangent-weight-base-change: it applies to any smooth affine finite-type group over a nonzero Noetherian ring and gives finite projectivity and arbitrary base change for the full coaction weights. It is applied separately to G,P,Q. Coarsening characters by the integer pairing is explicit. The dynamic-subgroups statement gives the nonnegative tangent summands for P. Closed immersions are injective on dual-number points, so the inclusions and reduced inclusions really are injective tangent maps; no injectivity after tensoring an arbitrary module map is assumed.

For step 3, I read Nakayama-local-generators: the empty family detects zero for each finite negative weight module over this local ring. Its statement expressly includes generation in the residue tensor product. Negative summands vanish because their images lie in disjoint summands of the ambient closed-fibre tangent space. This is a routine consequence of the two preceding steps and the cited Nakayama statement, marked elementary.

For step 4, I read relative-dynamic-subgroups: its hypotheses require smooth affine finitely presented groups, which step 1 supplies, and its conclusions give smoothness, closedness, geometric connectedness and tangent/base-change formulas for R. I read smooth-subgroup-tangent-generation: its singleton case works over every algebraically closed field with connected smooth target Q_F and gives equality even as a closed subgroup scheme. I read flat-geometric-fibre-open-criterion: its isomorphism clause requires flat locally finitely presented source, locally finite-type target and a locally finitely presented map. Smoothness gives the first conditions and the finite-type Noetherian coordinate calculation gives the last. Thus the fibrewise equality gives an isomorphism over A, including nilpotents. Step 5 writes the actual orbit extension and its composite on every test algebra, then applies the same proved implication in the other direction for equality.

For step 6, I read affine-group-lie-tangent-calculus (natural field extension isomorphism), relative-tangent-weight-base-change (character-weight scalar extension), regular-cocharacter-borel-description (the Borel tangent decomposition over an algebraically closed field), and reductive-rank-one-reflections (zero summand Lie(T) and dimension one for each root space, in every characteristic). They say exactly the claims used, rather than merely defining the notions. Passing to an algebraic closure satisfies their hypotheses because the given T is geometrically maximal and the fibres are reductive/Borel. The descent back to k is written by a basis argument. In particular this does not use differentials of characters, which can collapse distinct roots in small characteristic, or rational-point weights over a finite field.

I checked B–E of delivery-errors, including self-contained new statements, correct sources, recorded searches, no per-clause relabelling, no unproved claim hidden by 'transport', and no C4 citation to a proof instead of a statement. Every cited node's full statement is copied verbatim in citations.json. There is only one new node; all other substantial inputs are existing nodes. No step exceeds 2000 characters. Small cases: A a field, A with nilpotents, G a torus (empty roots), P=G (lambda=0), Q=G (negative weights must vanish), P=Q, and GL_2 opposite Borels. In the last case the root sets differ, so the asserted equality criterion has no false positive. In characteristic 2 the full characters remain distinct, and the argument never uses their derivatives. No SGA source is cited.

The general Noetherian-algebra lemma is a tool from another unit; no same-unit node supplies it. It is used only as the black-box algebraic finite-presentation check, so any required tool_uses recording is left to the maintainer. The Nakayama node is a Mathlib leaf. All other proof inputs are in the item's unit.

## Unfinished work

No unfinished argument in the item. The one new prerequisite is deliberately statement-only, to be split by its future worker. Required dry run and delivery results are recorded below when available.
