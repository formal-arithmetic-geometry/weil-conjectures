# Stage 1 report

Files written:

- `lem-weil-pbc-finite-pushforward-generic-constructible.json`: split statement; Mathlib searches found no exact theorem.
- `lem-weil-pbc-generic-finite-algebra-splitting.json`: unsplit auxiliary statement; Mathlib searches found no exact theorem.
- `citations.json`: verbatim citations for every non-elementary proof use.

Attachments: none.

WANTED: none.

The source item had no declaration in `WeilConjectures/` tagged with the blueprint id and no sorry-free declaration with the exact statement. The imported proof had a long algebraic calculation hidden in elementary paragraphs. I isolated that calculation as `lem-weil-pbc-generic-finite-algebra-splitting`; the remaining arguments cite existing DAG nodes. The finite-etale pushforward node is used by specializing its finite-module statement to a common exponent of the finite stalks.

## Review by J1

I read the item source and the neighbouring Noetherian constructibility node in the blueprint, and checked the corresponding declarations and docstrings in `WeilConjectures/ConstructibleSheaf/FinitePushforward.lean`; that file contains only later approximation lemmas, not this generic constructibility statement. Step 1 uses the exact integrality conclusion of `pqf-lem-finite-integral-lft`. Step 2 uses the universal-homeomorphism etale-site equivalence and the finite-components conclusion, with the finite-algebra generic-fibre assertion written out. Step 3 uses the existing irreducible-lisse-strata statement to obtain open lisse neighbourhoods. Step 4 uses the new auxiliary node, whose statement explicitly supplies the finite etale cover, product decomposition, and universal-homeomorphism factors; the nilpotent reduction is covered by the universal-homeomorphism node. Step 5 uses the exact finite-etale pushforward statement and the finite-exchange isomorphism; the common-exponent specialization was checked on finite abelian stalks. Step 6 is the elementary descent of a trivializing cover along an etale surjective cover.

I checked hypotheses: the base is an integral Noetherian affine scheme, finite maps are closed, all shrinkings are by nonzero principal opens, and the cover used at the end is finite etale and surjective. Small cases checked were `Z=∅` (zero pushforward on the complement), `Z=S` (the identity finite map), and a finite disjoint union of copies of `S` (pushforward is a finite product of lisse sheaves). The Mathlib searches for the item and auxiliary algebra node were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

## Second reading by J1

- Item statement: checked against the imported blueprint statement and the finite-pushforward construction; hypotheses (integral Noetherian affine base, finite map, constructible abelian sheaf) and dense-open lisse conclusion agree.
- Step 1: checked against `pqf-lem-finite-integral-lft`; integrality plus lying-over gives the closedness used for shrinkings, with no extra hypothesis.
- Step 2: checked against universal-homeomorphism invariance and finite-components statements; reduction and the generic-fibre/component argument are valid, including the empty generic-fibre case.
- Step 3: checked against `lem-weil-pbc-irreducible-lisse-strata`; finite components permit the stated open intersection and the finite-map closedness gives the dense shrink.
- Step 4: checked against the auxiliary algebra node and universal-homeomorphism invariance; the nilpotent thickening is handled by the cited topos equivalence.
- Step 5: checked each cited statement; corrected the original misuse of the finite-etale pushforward lemma, since the factors are universal homeomorphisms. The direct-image equivalence and finite product argument now use the universal-homeomorphism theorem, and finite exchange gives the pullback identification.
- Step 6: checked etale-surjective descent of a trivializing cover; the argument is elementary from the definition of lisse sheaf and the cover hypotheses.
- Auxiliary node `lem-weil-pbc-generic-finite-algebra-splitting`: checked the domain, finite-algebra, and universal-homeomorphism notions against its cited definition nodes and the finite-algebra calculation. Tested `B=A`, `B=A^r`, and a purely inseparable field extension. Repaired the statement so all localization is absorbed into the single nonzero base element `c`; an arbitrary further localization of `A'` would not preserve finite etaleness.

Changes made: removed the invalid finite-etale pushforward citation and dependency from Step 5, updated `citations.json`, corrected the auxiliary statement's localization and TeX, and updated the split report's tool-use record.
