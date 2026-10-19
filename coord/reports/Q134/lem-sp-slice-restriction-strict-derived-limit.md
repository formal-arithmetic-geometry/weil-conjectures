# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-slice-restriction-strict-derived-limit.json`: statement, split; no exact Mathlib match. The statement, statement dependencies, source and inherited blueprint ancestry are preserved. Added six proof steps, their exact dependency union, proof origin and split report, and actual Q134 search results.
- `citations.json`: one verbatim statement excerpt for every step/node pair.
- No new nodes, no Mathlib leaves, and no unit files changed.

## Attachments

None for the item. I searched the read-only `WeilConjectures/` tree by its blueprint tag and by restriction, slice, inverse-limit, homotopy-limit and K-injective terminology. The triangulated `IsHomotopyLimit.map` theorem transports Milnor cones; it does not state this canonical natural comparison on the derived category of strict towers. The existing generic K-injective preservation and localized exact adjunction are reused through their DAG nodes, not claimed as attachments of this item. No own Lean declaration or open sorry declaration was recorded on the item.

## WANTED

None. All sources used are present locally.

## Faults and changes

The item was a statement-only extraction from Step 3 of `lem-sp-completed-pullback-adjunction`. There was no previous sandbox split or report to recover. Its mathematical statement is correct; no statement correction or disputed statement is needed. The source place's 03DJ supplies exactness, while the adjunction itself is 03DI. The proof now names both labels explicitly rather than relying on that shorthand.

The important distinction is between K-injectivity in the tower category and K-injectivity of the evaluated terms. Merely restricting every evaluated term would not justify applying total strict inverse limit. Step 2 instead applies the exact-left-adjoint criterion to the lifted tower adjunction. Ordinary restriction of module sheaves here is restriction to an arbitrary site object, not just a scheme open immersion. No enough-points, repleteness, exact-products, boundedness, flatness of a ring change, or constructibility hypothesis is used.

The item's inherited source and the entire chapter/unit records were read. The current main-20261015 `fix-lem-exchanges.proof.md` Steps 2 and 3 concern naturality and normalized adjunction mates; this foundational slice argument supplies the completed adjunction used there. The current main unit is physically under `sec-six-functors-basics`, while the inherited DAG unit/chapter metadata retains `sec-smooth-purity`; I have not edited this maintainer-owned binding. This delivery does not change the unit's route or statement.

## Unfinished work

None within this one-level split. Existing dependency nodes retain their current statuses.

## Mathlib and duplicate searches

I read the inherited search records, then ran and read the five Q134 command searches in `searches.jsonl`: two different LeanFinder formulations, Loogle for `CochainComplex.IsKInjective`, the restriction/derived-limit grep, and LeanSearch. All services returned results; none was unavailable. The nearest hits were ordinary scheme restriction composition, `SheafOfModules.hasLimit`/`hasLimitsOfShape`, the K-injective definition, and `Functor.mapDerivedCategoryFactors[h]`. I read the relevant Mathlib sheaf-module limits and exact-derived-functor source. These do not prove the full item in one line: the exact slice adjunction on tower categories and its K-injective application are still needed. The more abstract Guitart-exactness hits assume a derivability structure not supplied by the item's hypotheses.

I searched the whole DAG by `03DJ`, `08BJ`, `0941`, restriction/limit/K-injective terminology, and used `blueprint_refs.py ancestor` and searches for `restriction`, `derived limit`, `K-injective`, and combined strict-tower terms. This found the existing exact slice adjunction, right-adjoint K-injective preservation, tower abelian-category leaf, K-injective Hom leaf, and strict-limit model now cited. `lem-pur-kinjective-restrict-localized` only asserts restriction of an ordinary K-injective complex, not preservation of K-injective tower complexes plus the canonical limit comparison. `lem-weil-ringed-tower-pushforward-limit-comparison` concerns ringed-topos direct image, whose direction and functors differ from slice inverse image here. No duplicate node is introduced.

## Not duplicates

No new nodes. The proof uses existing statements and writes the elementary lifts and compatible-tuple computations as steps.

## Review by Q134

I read Stacks `sites-modules.tex` Definition 04IX (`definition-localize-ringed-site`), Lemmas 03DI (`lemma-extension-by-zero`) and 03DJ (`lemma-extension-by-zero-exact`); `sites-cohomology.tex` Section 0940 and Lemma 0941 (`lemma-derived-limit-is-ok`) with its K-injective tower proof; and `derived.tex` Lemmas 08BJ (`lemma-adjoint-preserve-K-injectives`) and 070I (`lemma-K-injective`). The item assumes a site small in the chosen module universe, a commutative ring sheaf and an arbitrary site object U. Its slice is small in that same universe. These are sufficient for both strict-tower models. The scalar clause is a specialization with the original restricted ring, not another coefficient category. There are no new node statements to check against a source.

For Step 1 I opened `lem-pur-site-restriction-module-adjunction-exact`: its statement gives exactly the additive module adjunction and exactness needed, for arbitrary ringed sites. I also opened `lem-weil-tower-category-levelwise-abelian`; its statement gives abelianness and pointwise exactness. The lift of the Hom bijection is written out through its naturality equation, rather than treated as an extra theorem. Kernels and images commute with an exact functor, so the cohomology and quasi-isomorphism assertion follows directly from the definition in `def-weil-abstract-derived-category`. This is the elementary content of this step.

For Step 2 I opened `lem-weil-pbc-right-adjoint-preserves-kinjective`. Its statement is for any pair of abelian categories and additive adjoint functors with exact left adjoint. Step 1 verifies every one of these hypotheses for the tower categories. Thus its conclusion is K-injectivity of the entire restricted tower complex, exactly what the step takes from it. I did not cite the ordinary slice K-injectivity node for this stronger application.

For Step 3 I opened `def-weil-sheaf-of-modules-category` and `def-pur-localized-ringed-site`. The latter explicitly gives restriction as F(V) at V/U, and the former gives compatible sectionwise module actions and module-linear morphisms. Coordinatewise gluing proves that compatible tuples form a sheaf and establishes the limit property. Consequently the comparison and its inverse are both identity maps on tuples. This short proof supplies the limit identification itself; a definition node is not being cited as a theorem that restrictions preserve limits.

For Step 4 I opened `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, including its exact statement and proof. Its statement says total derived inverse limit is computed by a K-injective tower resolution and termwise inverse limit. I apply only that statement, once on C and once on C/U, not its inline tower-site construction. Step 1 makes the restricted resolution a quasi-isomorphism and Step 2 makes its target K-injective. There is no product-exactness assumption hidden in this computation. The ordinary comparison of Step 3 is now an isomorphism between these two actual computing complexes.

For Step 5 I opened `lem-weil-pbc-kinjective-hom-derived`. Its statement provides the bijection between homotopy-category maps into K-injectives and derived-category maps, in any abelian category, and the homotopy-equivalence comparison of K-injective representatives. Tower categories are abelian by the cited leaf in Step 1. Naturality of the comparison follows from the explicit tuple formula and its invariance under chain homotopies, whose additive homotopy equation is preserved termwise. This verifies that the constructed map is the prescribed derived comparison rather than an arbitrary isomorphism between homotopy limits.

For Step 6 the tower-category leaf ensures q_n is a quasi-isomorphism. I explicitly use the projection from lim I and invert q_n, and the equation for tuple projections checks the required square. `def-pur-localized-ringed-site` gives the restricted module action, so the actual chain transition a becomes a|_U. All scalar values, including zero, units and nilpotents, are allowed. A quasi-isomorphism of representatives yields a levelwise quasi-isomorphism of the multiplication towers, justifying the phrase “tower of H”.

I checked B–E against these node files and source passages. B: no new nodes or unsupported definitions, meaningful source labels, unchanged self-contained statement. C: every non-elementary input is a cited statement; every citation has a literal excerpt in `citations.json`; no proof-only facts are borrowed. D: the item carries the argument and has no new restatement node. E: the categories, functor directions, exact-left-adjoint hypotheses, smallness and projections have been checked explicitly. Small cases were the zero complex, zero coefficient ring, terminal U (identity comparison), a point site (ordinary module towers), arbitrary non-epimorphic transitions, and scalar a=0, a=1 and nilpotent a. None requires additional hypotheses. Each proof step has fewer than 1,000 characters, so no long step hides a sublemma. I corrected the potential termwise-versus-tower K-injective gap by lifting the exact adjunction before using 08BJ.

The off-unit strict-tower model is declared in `split_report.tool_uses`: it is a generic foundational computation that this unit does not replace. The other off-unit cited tools are definitions, Mathlib leaves or Lean-closed statements. No SGA source, Lean writing, compiler, Lake, live-project edit, or local preflight execution was used.

## Validation repair

The first dry run rejected only two short citation excerpts (Steps 3 and 6). I expanded each to the complete statement clause giving both sectionwise restriction and its module structure. The proof and its dependencies did not change.
