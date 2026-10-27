# Stage 1 delivery: lem-sfb-kflat-derived-adjunction-transport-shifts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kflat-derived-adjunction-transport-shifts.json: statement, split in four steps; no full Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-abstract-derived-unit-factorization.json: statement, Mathlib leaf CategoryTheory.Adjunction.derivedη_fac_app, Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:103-109 (unit definition :96-99; its use in derived :144-151).
- citations.json: every node used by every numbered step, with a complete verbatim statement quote.

One new node, one Mathlib leaf. Only the sandbox was written. No Lean was written and nothing was compiled.

## Attachments

None for this item. Searched the blueprint tag and the derived adjunction/transport notions in lean/WeilConjectures, then read SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean and CategoryTheory/DerivedCategory/Adjunction.lean. The project has the specified adjunction and comparison constructions, but these declarations do not state the comparison of both units/counits together with fixed shift compatibility. The canonical exact-left shift theorem already has its own node, lem-sp-canonical-right-derived-adjunction-shift, and is reused.

## WANTED

None. The blueprint, Stacks derived.tex, Mathlib sources and project Lean sources used here are available locally.

## What was wrong or incomplete

The item had a statement and searches but no proof. Its mathematical statement is retained verbatim. In particular, merely constructing an adjoint shift on G would not prove its last clause: G already has the fixed K-injective shift. The split uses the existing theorem specifically asserting that fixed normalization, and writes the transfer equations. Stacks 0DVC states the canonical adjunction, not this entire normalization comparison; the assembly calculation is therefore marked agent-written.

The existing generic lem-sc-derived-adjunction-from-underived is not used: its statement gives the counit factorization, not the unit equation needed for the cancellable exact comparison. The new leaf isolates the actual Mathlib unit equation with its universal-pair hypothesis. It does not move a clause of this item's module/shift comparison into a new node.

## Unfinished work

None in this stage 1 split. The delivery remains subject to the maintainer's independent review. No stage 2 or stage 3 work was attempted.

## Not duplicates

lem-sfb-abstract-derived-unit-factorization vs lem-sc-derived-adjunction-from-underived: the latter asserts an abstract derived adjunction and its counit factorization; the new leaf states the unit factorization, with only the left-derived universal property of L followed by R required. The old statement does not give this equation.

lem-sfb-abstract-derived-unit-factorization vs lem-pc-derived-adjunction-normalization-unique: the latter says two already normalized adjunctions are equal; the new leaf supplies the actual factorization of the constructed unit, without assuming two adjunctions or a Hom normalization equation.

lem-sfb-abstract-derived-unit-factorization vs lem-sfb-resolving-derived-adjunction-normalization: the latter assumes abelian categories, a resolving class and K-injective resolutions and gives an existence/Hom transpose theorem; the new leaf is an abstract category-theoretic unit API valid without those hypotheses. It is already in Mathlib.

lem-sfb-abstract-derived-unit-factorization vs lem-sp-canonical-right-derived-adjunction-shift: the latter proves fixed shift compatibility for an exact-left adjunction. The new leaf contains no shift structures and only computes a derived unit through its comparison.

## Review by Q111

I read the chapter and the unit sk-thm-sfb-proper-base-change before the item, and its nearest blueprint ancestor det-thm-sfb-proper-base-change-rational, proof paragraph (3). This paragraph needs the canonical exchange to be a transformation of exact functors; the present comparison supplies its adjunction normalization, without altering any coefficient category or changing that proof route. I read Stacks derived.tex, lemma-pre-derived-adjoint-functors-general (0FND) and lemma-pre-derived-adjoint-functors (0DVC), including their Hom colimit construction. They justify the canonical derived adjunction, but omit this particular comparison, so I did not attribute the detailed calculation to Stacks. I read Mathlib Derived/Adjunction.lean:96-109 and :144-151 for the one new leaf, including the exact hypothesis on the left-derived pair after postcomposition. The leaf is statement-only, introduces every category/functor/transformation, and matches derivedη_fac_app after reversing Lean composition notation. Its universal-pair hypothesis is written out, rather than hidden behind a reference to a tag.

For step 1, I opened the statements of lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-exact-functor-derived-factorization and lem-weil-pbc-localization-universal-property. They respectively give the termwise unit and adjunction, the exact localization isomorphism, and full faithfulness of descent on natural transformations. The new leaf gives precisely G(alpha) followed after the derived unit equals the localized ordinary unit followed by beta. The extra hypothesis of that leaf is checked in the step: alphaA is invertible and alphaP is alphaA composed with c, hence invertible; postcomposition by any G preserves these inverses, so natural transformations descend uniquely along Q. Thus it is legitimate for both actual specified unit constructions. This avoids needing an unproved preservation assertion about u_* on K-injectives. I also read the definitions of the two actual adjunctions in the Lean files: both use Adjunction.derived with those comparisons.

For step 2, the only cited statement is localization-universal-property, clause (3), equality of transformations detected after precomposition. Its hypotheses apply to Q_Y, the ordinary unbounded localization; they impose no boundedness. The remaining work is the explicit substitution alphaP=alphaA cQ and cancellation of G(alphaA), an isomorphism. This gives the formula on all objects, without equating adjunctions merely because their functors are isomorphic.

For step 3, the proof uses only the two specified adjunctions' defining Hom bijections and triangle identities. I checked the type d_N:PGN to N and its transpose GN to GN. Substituting the unit identity makes that transpose the identity. Injectivity of the Hom bijection gives the actual counit identity. This short calculation is elementary and is written out rather than hidden behind 'transport'.

For step 4, I opened the statement and source of lem-sp-canonical-right-derived-adjunction-shift, including lean/Sheaf/CategoryTheory/CanonicalRightDerivedAdjunctionShift.lean and the exact-left adjunction definition. Its hypotheses are abelian categories with unbounded derived categories, K-injective resolutions on the target, and an additive exact left adjoint. Here these are precisely the ambient module categories and specified exact u^* and K-injective model in the item. Its conclusion explicitly retains the canonical K-injective shift. The proof writes both shift squares for every integer n, using naturality of the fixed shift sG and of c and cancelling an invertible G(c)[n]. Thus there is no appeal to the weaker theorem that chooses a new adjoint shift. The off-unit citations are declared in split_report.tool_uses as generic tools; they do not replace the unit's route.

I tested the formulas on u=identity and c=identity, where they reduce to equality of the two unit/counit presentations; on n=0 and negative shifts, where the same typed algebra applies; and on the zero module category, where the unique arrows satisfy all formulas. The need to hold beta fixed was checked using the scalar-twisted identity adjunction on modules over a field: arbitrary adjunctions on identical functors can have inverse scalar twists in their units/counits, so functor isomorphism alone is insufficient. Step 1's identical normalized right side excludes that twist. No hypothesis was added and no conclusion weakened.

For duplicate checks I searched the whole DAG by tags 0DVC and 0FND, derived adjunction and unit/factorization terms, and searched the whole blueprint with tools/blueprint_refs.py for derived adjunction, derived adjunction unit, derived unit factorization and canonical right derived. I read the closest generic statements listed above before introducing the leaf. Mathlib searches were run only with the required msearch.py command, read as returned, and are recorded with exact query texts in the nodes and searches.jsonl. The first and second semantic phrasings both find the generic formulas, not the full module comparison; the formula-specific searches find the exact new leaf. No unavailable service is represented as a negative result.

I checked B--E of delivery-errors.md against both node files and the sources: the new node has no proof sketch or dependencies of a hidden proof; every proof citation is an actual statement quote in citations.json; no new node repeats a clause of the item; there are no SGA references. Every proof step is shorter than 2000 characters. No statement dispute or source correction is necessary. The only corrections during this review were choosing the unit formula rather than the existing counit-only citation, and making the universal-pair hypothesis and both transported shift calculations explicit.

## Validation

The first server preflight required the Mathlib line as a dedicated mathlib_match.line field; added line 103, already read and documented in the source/how fields. Re-running the required dry run.
