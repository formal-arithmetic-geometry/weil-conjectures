# Stage 1 report: def-galois-object

Files written:

- `dag/nodes/sec-smooth-purity/def-galois-object.json` — existing definition item, split with no new nodes; Mathlib searches found only abstract PreGaloisCategory analogues, not an exact match.
- `citations.json` — empty because the definition has no proof steps.

Attachments: none. The source declaration `AlgebraicGeometry.Scheme.FiniteEtale.isGalois_iff` is a theorem about the existing abstract `IsGalois` predicate and does not state this whole scheme-specific definition, so it is not an attachment.

WANTED: none.

The imported node agrees with the blueprint sentence: a connected base scheme with a geometric point, a finite étale cover regarded as an object of `FÉt(Y)`, connectedness of `P`, and simple transitivity of `Aut_Y(P)` on the geometric fibre. Its two statement dependencies are the existing definitions of `FÉt(Y)`/geometric fibres and the fibre functor. No proof or subordinate lemma is appropriate for a definition node. The source file `WeilConjectures/AlgebraicGeometry/FundamentalGroup/Basic.lean`, lines 214–223, was read; its `isGalois_iff` theorem gives an equivalence for the Mathlib `PreGaloisCategory.IsGalois` notion and therefore does not supply an exact declaration of this item. The source's `EtaleTorsor.lean` `Scheme.GaloisCover` structure instead takes a separately specified finite group action and allows disconnected total space, so it also differs from the item.

## Review by NV

I checked the item's statement against `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-galois-object.md` (node order 1901), clause by clause. I opened both cited dependency statements: `def-galois-categories` supplies the category of finite étale `Y`-schemes and the notation for geometric fibres, while `def-galois-fibre-functor` supplies the fibre-functor context and its automorphism group. Since this node is a definition, it has no proof steps and hence no step citations or hypotheses hidden in a proof. I searched the whole DAG and blueprint for the definition and found only this item and the pointer `rem-ptr-galois-object-2`, which does not restate it. I read the relevant source declarations and checked the edge distinction between the project's `Aut_Y(P)` action on a connected cover and Mathlib's abstract `IsGalois`/group-action structures. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; the latter was unavailable and is recorded as such in the node. No statement or dependency was changed.

What could not be finished: nothing.

## Second reading by NV

- Item statement: checked clause by clause against the blueprint node (order 1901) and Stacks `pione.tex`, Section `section-finite-etale-under-galois` (the definition immediately before the equivalent conditions); the hypotheses that `Y` is connected, that a geometric point is fixed, that `P → Y` is finite étale, that `P` is connected, and that `Aut_Y(P)` acts simply transitively on the geometric fibre all agree.
- New nodes: none; there are no subordinate node statements to check (the item is itself a definition).
- Definition dependencies: opened `def-galois-categories` and `def-galois-fibre-functor`; they supply the finite-étale category, geometric-fibre notation, and automorphism/fibre-functor context used by the statement.
- Existing declarations: read `AlgebraicGeometry.Scheme.FiniteEtale.isGalois_iff` in `FundamentalGroup/Basic.lean` (lines 219–223); it characterizes the abstract `IsGalois` predicate and does not define this scheme-specific term, so no attachment or duplicate is appropriate. The `Scheme.GaloisCover` structure in `Morphisms/EtaleTorsor.lean` requires a separately supplied group action and is a different notion.
- Edge cases: a connected base with a one-point fibre gives the trivial cover (the trivial automorphism group acts simply transitively); a disconnected `P` fails the definition even if an automorphism action is transitive; the empty scheme is excluded by the connected-base/geometric-point hypotheses; no cardinality or nonzero-fibre hypothesis is silently added.
- Searches: checked the whole DAG and blueprint for duplicate definitions and ran the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch queries; only abstract `PreGaloisCategory` analogues were found.
- Changes: none; the statement, dependencies, and empty citation list already satisfy the definition-node form, and the dry run passed preflight.
