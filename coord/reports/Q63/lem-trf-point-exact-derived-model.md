# Q63 stage-1 delivery: lem-trf-point-exact-derived-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-exact-derived-model.json`: existing statement node, split into nine steps; no exact Mathlib match for the full statement.
- `citations.json`: sixteen step/node entries, each quoting a verbatim substring of the current cited statement.
- `report.md`: this report. `searches.jsonl` is the unchanged search-command log; the local write script is only a sandbox helper.

## Attachments

None. Searches for the blueprint id and the exact-point terminology throughout `lean/WeilConjectures/` found no declaration stating this item. The inspected generic exact-derived comparisons in `CategoryTheory/DerivedCategory/MapDerivedCategoryMate.lean` and the Frobenius comparison constructions in `SixFunctors/ProEtale/GeometricFrobenius.lean` supply parts of its mathematical infrastructure, but do not state the whole pro-etale module-sheaf point result with its arbitrary natural transformations and the specified K-flat-normalized comparison. They are not attachment claims.

## WANTED

None. The source texts needed for this split are present. No SGA source is used.

## What changed and what was wrong

The existing node had a statement and searches but no proof. Its statement is retained verbatim: no dispute, extra hypothesis, weakened conclusion or replacement coefficient category. In particular, the ambient category consists of ordinary sheaves of modules over the finite constant ring on the small pro-etale site, not condensed-coefficient module objects or completed integral objects.

The split adds the proof dependencies actually used and the statement dependency for the ordinary canonical module-pullback compositor. It retains the existing blueprint ancestor and precise origin place, searches the whole blueprint for a duplicate, and fills `split_report.blueprint` and the declarations of off-unit generic tools. The chapter and unit records are unchanged. The unit has no numbered proof steps to re-realize, and this auxiliary item is not its defining statement.

The exact-derived normalization is not assumed from a generic existence isomorphism. Step 4 first proves the claimed formula on a flat-term K-flat complex using the specified derived compositor's statement. Step 5 writes two naturality equations and cancels the image of a quasi-isomorphism to prove the formula for an arbitrary complex. The ordinary compositor uses the literal constant-section coefficient maps, verified separately in Step 3. Descent in Step 8 uses the fully faithful universal property for arbitrary natural transformations, so it does not require alpha to be invertible.

## What remains unfinished

No part of this item's one-level split remains unfinished. Its existing dependencies retain their current states. No new nodes are proposed, and no Lean was written or compiled. The maintainer's independent mathematical review is still required after delivery.

## New nodes

None: zero new nodes and zero new Mathlib leaves. The generic localization and exact-derived lemmas already have nodes, including Mathlib leaves, and the cancellation and chain-map checks are elementary proof steps rather than new nodes. No part of the item was moved into a renamed clause node.

## Not duplicates

No new nodes, hence no new/existing-node pairs to distinguish. DAG and blueprint searches found the exact module-pullback, exact point sections, constant-ring composition, K-flat-resolution and localization lemmas already in the project, and the split cites them directly. `blueprint_refs.py search 'exact-derived-model'` and `search 'exact point'` each found zero blueprint nodes stating the item; its blueprint ancestor is `lem-trf-frobenius-operator-compact-description`.

## Searches

I ran the required search command with LeanFinder (two phrasings), Loogle, grep and LeanSearch. Every service returned normally. The first long LeanFinder query gave irrelevant cotangent-cohomology hits; the second, broader exact-functor query gave `mapDerivedCategory`, `mapDerivedCategoryFactors` and related Ext maps. Loogle located `Localization.liftNatTrans`, its component formula and composition laws; grep located the same declarations in `Mathlib/CategoryTheory/Localization/Predicate.lean` at lines 278, 286, 326, 332 and 339. LeanSearch returned derived natural-transformation composition and exact-functor/Ext constructions. I read Predicate.lean and the exact-derived factorization in `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`, lines 35–55. These support existing nodes, not a one-line Mathlib specialization of the entire item. The item's previous search records are preserved, and the five newly executed queries are appended verbatim with their actual hits. No unexecuted or unavailable search is recorded as a negative result.

## Review by Q63

I read the source and proof of Stacks 0D6D (`sites-cohomology.tex`, `lemma-derived-pullback-composition`), its computation by a flat-term K-flat complex, and the two input constructions 06YS (`lemma-K-flat-resolution`) and 06YY (`lemma-derived-base-change`). I also read 015F in `derived.tex`, 03D8 in `sites-modules.tex`, 03CB and 0H7J in `sites.tex`, and 04VG in `categories.tex`. I compared 04VG's actual functor statement with Mathlib Predicate.lean, which explicitly supplies the stronger natural-transformation clause that Stacks does not state there. The proof is marked agent-written because the arbitrary-representative and natural-transformation refinements are assembled here, not claimed to be a verbatim Stacks theorem.

The blueprint route was checked against the current main-20261015 proof of `lem-trf-frobenius-operator-compact-description`, especially the paragraph beginning “That action transports the pair”. This split supplies the point-model comparison needed in that transport, through its recorded ancestor chain, without replacing the unit's compact-support route. For the point fiber I read the older blueprint's `def-weil-finite-coefficient-point.md` together with the current repaired definition node, whose finite-level functor is explicitly termwise final-object sections. There is no claim that every pro-etale sheaf on the point is constant.

For Step 1 I read both cited statements. `prop-weil-pbc-proetale-constant-exact` asserts exactness of the actual module pullback with canonical constant coefficients for finite rings and arbitrary scheme morphisms. Our ring is the finite commutative quotient in the hypotheses, and each h-power is a scheme morphism. `lem-weil-point-proetale-sections-exact` asserts exact evaluation on modules over any ring sheaf at Spec of an algebraically closed field. Our k is algebraically closed. Restriction to the constant A-scalars is exact on underlying groups, and that short argument is written explicitly.

For Step 2 I checked that `lem-weil-pbc-exact-functor-derived-factorization` includes quasi-isomorphism preservation and a natural factorization for every complex, not just bounded ones. `lem-weil-pbc-exact-functor-derived-functor` asserts that this exact factorization is a total left as well as right derived functor with its canonical comparison. The finite-level clause of `def-weil-derived-pullback-tensor-hom` specifies precisely that ordinary, uncompleted pullback computed by K-flat resolutions. Thus the factors used later have the specified comparison normalization, and no flatness of K is introduced.

For Step 3 the statement of `lem-trf-constant-coefficient-composition` gives exactly the coefficient-map equality used. `lem-pur-proetale-module-pullback-composition` states the canonical left-adjoint compositor using those actual constant-section maps; its direction is opposite to T_m, so I explicitly take its inverse. The cited derived-composition statement requires the composite coefficient identification, and the first equality supplies it. This avoids confusing two arbitrarily chosen isomorphisms of constant rings.

For Step 4 `lem-pc-kflat-resolution` supplies a map P to K with P K-flat and every term flat on any ringed site; the small ringed pro-etale site satisfies that hypothesis. `lem-weil-pbc-proetale-derived-pullback-composition` states both its normalization on such P and that the intermediate pullback is K-flat with flat terms. I checked the order h then h^m gives Q_1 Q_m, and inverting c gives the requested t_m. Step 5 uses only the naturality from Steps 2 and 4 and the ordinary naturality of T_m: it writes both squares and cancels the same invertible a. This is a few-line argument, not an unrecorded independent comparison lemma.

For Step 6 the Frobenius definition makes gamma an automorphism; the inverse h-power is therefore explicit. `lem-weil-isomorphism-derived-pullback` gives both the termwise inverse-image identification and bounded-constructible preservation for this coefficient ring. Its ell-invertibility hypothesis follows from ell different from p, and its finite-level clause applies at every n at least one. The point definition's first clause is exactly V as termwise sections, and `lem-weil-point-sections-finiteness` (1) supplies its bounded finite-cohomology codomain. Neither a finite-field-only pullback lemma nor an integral completion theorem is substituted here.

Step 7 is elementary: I wrote naturality for each differential and each degree of a chain map, proving that alpha's components give chain maps and a natural transformation on complexes. Step 8 cites the full statement of `lem-weil-pbc-localization-universal-property`, whose part (2) gives unique descent with the explicit conjugation by the two factorization isomorphisms. Its hypotheses are exactly quasi-isomorphism inversion, established in Step 2. Step 9 writes the inverse-quasi-isomorphism naturality calculation, applies elementary functoriality to chain-map equalities and compositions, and uses part (3) of that same statement for equality of natural transformations. The full-subcategory restriction is justified by Step 6.

I checked delivery-errors B through E individually against the files. B: there are no new statement-only nodes to audit, the only edited node retains its statement, all source places name actual labels/tags, and the search records correspond to executed commands. C: every cited node's statement was opened; the sixteen verbatim citation entries were tested against those statements. No definition is used as a substitute for a missing theorem: exactness, bounded-constructible preservation, K-flat existence, normalized composition and localization descent all have theorem citations. The remaining algebra and chain-map naturality are written as elementary steps. Off-unit generic uses are declared without altering the unit route. D: the proof carries the argument in nine steps, creates no restatement node, and contains no circular resolution comparison. E: the unbounded, non-flat and nonconstructible representative cases are allowed; the fixed coefficient maps and order of composition are retained. In small cases, the zero complex and alpha=0 give zero component maps, alpha an identity (where its source and target agree) gives the identity after conjugation, a one-term complex recovers the ordinary comparison, and the m=1 case reads H_1 H_1 to H_2. A non-K-flat representative is handled by the same cancellation square, not by an invalid flatness assumption. The argument also works for a ring with nilpotents (n greater than one), because only exact pullback with an isomorphic coefficient sheaf is used.

No proof step exceeds 2000 characters (the longest is 971). The independent server `review_split` check passed with zero new nodes; its only route notes were declared generic tool uses and the pre-existing absence of a unit realization record. Before writing this report I corrected one proof-step source path that pointed to a nonexistent new-snapshot copy of the point definition; it now cites the existing older source actually read, with the current DAG definition used for the refined statement. No mathematical statement needed correction.
