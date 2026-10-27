# Q07 — lem-trf-stalk-compositor-tower-realization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-stalk-compositor-tower-realization.json`: statement, split, no Mathlib match; ten proof steps, with all non-elementary inputs supplied by existing nodes.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` was produced by the prescribed search command.

No new nodes; no new Mathlib leaves. The statement and its statement dependencies are unchanged. All inherited fields, including the original searches and blueprint ancestry, are retained.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the exact id, stalk/compositor and tower/realization combinations, and read `SixFunctors/Etale/Derived/NormalizedTowerRealization.lean`. Its `NormalizedTower.exists_iso_of_isHomotopyLimit` realizes an isomorphism of normalized étale towers; it does not assert the pro-etale stalk formula, the specified integral counit normalization, or the reparametrization square. It is not an attachment for this item. No project declaration found states every clause.

## WANTED

None. The germ-colimit source is available. The extension from this finite formula to the normalized integral simultaneous quotient diagrams is an agent argument and is marked accordingly.

## Issues and corrections

The item arrived unsplit, without a proof. Its statement is correct with its stated comparison normalizations. There is no statement dispute and no change to any unit or chapter. The finite stalk lemma is explicitly for bounded complexes, so Step 1 uses the existing functorial bounded zigzags before applying it; the proof does not treat the generally unbounded K-flat representative as bounded. Step 5 distinguishes the section-tower comparison obtained through the entire-tower counit from an arbitrary family of finite reduction isomorphisms. The map of both cone coordinates, quotient compatibility, and the actual reparametrization germ are written out instead of being hidden in a transport assertion.

## Mathlib and blueprint searches

Read all five fresh logged search results, including two semantic phrasings. Loogle `"stalkPullback"` gave the ordinary topological stalk maps and their germ equations. The grep returned `TopCat.Presheaf.stalkPullbackIso` at `Mathlib/Topology/Sheaves/Stalks.lean:335` and `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` at `Mathlib/CategoryTheory/Sites/Point/Comap.lean:69`; read both source declarations and their context. They do not identify this completed integral compositor on whole quotient diagrams. LeanSearch returned ordinary stalk-unit/counit equations and chosen-pullback comparison equations; the two LeanFinder searches returned scheme pullback coordinate formulas, finite-set Galois fiber functors, and unrelated profinite/condensed identifications. None is an exact match or one-line specialization. All services answered; no unavailable query is represented as a negative result.

Whole-DAG searches for the tag `0F4F`, stalk/composition and strict-tower/cone vocabulary located the three existing named comparison nodes and the generic localization and resolution-invariance lemmas. Blueprint searches `stalk compositor`, `tower realization`, `pullback stalk`, and `0F4F` found no equivalent blueprint node. The ancestor command gives `thm-trf-l-function-euler-product`; its current main-20261015 proof, Step 1, Local powers, input (b), is exactly the natural/compositional stalk-identification input realized here. Read the chapter and `sk-thm-trace-transport` unit records; this subordinate node is not the unit key statement and changes no realization fields.

## Not duplicates

No new nodes are proposed. The existing finite comparison is reused for the germ law; the existing bounded realization is reused for truncation and section coordinates; the existing integral comparison is reused for the counit and iterated realization. The item additionally relates these particular comparisons and checks its strict reparametrization square, which none of those individually states.

## Review by Q07

I read Stacks `sites.tex`, Tag 0F4F (`lemma-point-functor`), including its combined-colimit proof and the representative functor `(V,y,U,phi) -> (U,v(phi)(y))`, and Tag 05V1 (`lemma-point-morphism-sites`) immediately following it. This justifies the finite germ normalization used by the existing stalk-coherence node. I read the current blueprint Euler-product proof, Step 1, Local powers, input (b); it calls for natural stalk identifications compatible with composition and does not supply this strict integral calculation. Therefore the new proof origin is agent, not a claimed verbatim Stacks theorem. There are no new nodes requiring independent source verification.

For Step 1 I read the statement of `lem-trf-bounded-quotient-stalk-realization`: it supplies one cohomological interval, both strict zigzag arrows, preservation by every finite pullback, and naturality of the e comparisons. The item has exactly its constructible-complete coefficient datum and flat-term K-flat representative. Thus it is legitimate to apply the bounded finite lemma, even when the terms of P are unbounded or reductions have infinite Tor-amplitude.

For Step 2 I read `lem-trf-proetale-pullback-stalk-coherence`, which gives the representative germ, its inverse and coefficient naturality. I checked the quotient transition by replacing x with rho_n x and checked the differential by replacing x with dx; the point and projection are unchanged. The coefficient module pullback compositors here are the canonical ones in that statement, so their representatives preserve coefficient reductions. The fixed coefficient ring at level n is the finite ring A_n; transitions between levels are checked directly, not inferred merely from naturality for fixed coefficients.

For Step 3 the finite node gives the composition equation. Substituting h=v and point id_s is well typed. The bounded-realization statement supplies exactly the two e maps and the sections/identity-stalk normalization. I checked domains: Gamma(chi_fin) runs from sections of (fv)^*P_n to sections of v^*f^*P_n, so the inverse is e_fv^{-1} c e_v, in the direction required by the item. Cancelling isomorphisms gives this formula without reversing a factor.

Step 4 is elementary: I substituted the stated differential into the diagonal product map and used only the strict transition square. The minus sign on the shifted coordinate agrees on both sides. Composition is coordinatewise and has no cross term. This is not a separate non-elementary lemma or a new DAG node.

For Step 5 I read the entire statement of `lem-trf-integral-pullback-comparison-realization`, especially its definition chi = eta^{-1} Rlim(chi_fin), its K-injective whole-tower counit, and its explicit independence/naturality clauses. The equal-extension specialization E=E is permitted. Taking its maps h=v,k=f produces exactly the nested tower in our item. The bounded-realization statement provides the sectionwise comparisons on both products. I checked the displayed cancellation equation and its inverse direction; this uses the entire counit-normalized tower map before applying the cone, with no inference from agreement of separate reductions.

For Step 6 the finite node asserts exactly c_fh = c_f c_h chi_fin. I additionally expanded a double pullback germ: both routes retain x and compose its pointed lift through the W and V projections in that order. Replacing x by its quotient reduction verifies strictness. For Step 7 the integral comparison statement explicitly asserts compatibility with further operations, associativity, and arbitrary finite iterations as simultaneous quotient-diagram equations. It therefore identifies the last factor after w with J_w(chi_hf), under the same nested counit identifications. The construction does not silently swap a completed pullback and a raw inverse image.

For Step 8 the finite node's identity clause and the integral node's unital clause supply the exact unit identifications. The definition `def-weil-finite-coefficient-point` supplies Fib_s = sections. This proves the unit at s, with its required identification, rather than asserting a literal equality of differently constructed models.

For Step 9 I read `def-weil-proetale-geometric-stalk` and used its explicit generating relation on representatives. A pointed relation remains a relation after precomposition by delta. This also proves inverse, additivity and compatibility with coefficients and the differential, directly. The finite comparison's formula makes both square routes the very same pointed germ [V,pr_V theta u' delta,x]. Applying Step 4 and the e/eta identifications from the bounded and integral comparison nodes gives the whole realized square. No separate derived evaluations are declared faithful.

For Step 10 I read `lem-pur-integral-operations-well-defined`: it states that the cone functors invert quasi-isomorphisms between flat-term K-flat representatives and that their descents and natural comparisons are resolution independent. I read `lem-weil-pbc-localization-universal-property`, including the full natural-transformation descent, preservation of identities/composition and equality-detection clauses. Together with the bounded and integral comparisons' stated naturality these give naturality for arbitrary derived morphisms: invert a quasi-isomorphism's naturality square and compose. This is the sole generic localization tool use; the trace unit supplies no replacement for it. The well-definedness lemma is the other generic tool, recorded in split_report.tool_uses. No dependency is taken from a cited node's proof alone.

I tested the first coefficient level, a zero complex, f or h the identity, v=id_s, alpha=1, a complex whose bounded reduction cohomology is in one degree, and an unbounded flat-term K-flat representative with the same bounded reduction cohomology. Formulas specialize correctly; at zero complexes the maps are unique and at identities the explicit unit identifications apply. Empty schemes cannot carry the given geometric point and introduce no additional case. The automorphism is used only by precomposition, with no assumption it fixes F_q or commutes with another automorphism. No new statement requires a separate small-case test.

Against delivery-errors B--E: all statements and inherited metadata are retained, every step citation has a verbatim statement quotation, all non-elementary operations are covered by the named existing nodes, and there is no new duplicate, clause relabelling, missing coefficient hypothesis or silent change of site/category. Every step is below 2000 characters (maximum 1133), so there is no long step hiding a further lemma. The proof follows the unit's stalk-identification input and uses no SGA source. The required server checks and push are the remaining delivery actions.

## Unfinished work

No mathematical part remains open in this split. The independent maintainer review remains external to this delivery.
