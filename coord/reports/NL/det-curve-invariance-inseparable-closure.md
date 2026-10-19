# Worker report

## Files written

- `dag/nodes/sec-curve-estimates/det-curve-invariance-inseparable-closure.json`: split item; no new nodes; Mathlib searches recorded, with no exact Mathlib match for the full item.
- `citations.json`: seven verbatim citations covering the two proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, curve-invariance terms, universal-homeomorphism terms, and the relevant declaration names; no sorry-free project declaration states the item. The existing universal-homeomorphism declarations used below are attached to their existing DAG nodes.

## WANTED:

None.

## What was wrong in the imported node

The imported first paragraph asserted that the algebraic closure map is a universal homeomorphism by an inline tensor argument but cited only base-change stability and étale invariance. I replaced that unsupported jump with the existing pure-inseparability, Spec integral/radicial/surjective, and universal-homeomorphism criterion nodes. The imported `def-weil-pbc-curve-setting` statement dependency was unused because the item allows an arbitrary k-scheme and arbitrary abelian étale sheaf; it was removed, and the base-change and scheme-over-base definitions needed for `C_bar k` were added. The square paragraph now cites the existing composition law for étale cohomology pullback instead of treating functoriality as an uncited elementary fact.

## Source error

None in the mathematical statement. The characteristic-zero case is explicitly handled: a separably closed characteristic-zero field is already algebraically closed.

## Review by NL

I read the item source `literature/blueprint/main-20261015/blueprint/sec-curve-estimates/sk-cor-curve-invariance/det-curve-invariance-inseparable-closure.md` and its proof, together with the unit route in `dag/units/sk-cor-curve-invariance.json`. For Step 1 I checked `lem-pc-kbar-pure-insep`: in characteristic p it states that the algebraic closure of a separably closed field is purely inseparable; in characteristic zero the direct separable-closedness argument gives equality of the field and its algebraic closure. I checked `lem-pc-spec-pure-insep-integral-radicial-surjective`, whose hypotheses are exactly a purely inseparable field extension and whose conclusion supplies integrality, universal injectivity, and surjectivity of the Spec map. I checked `lem-pc-integral-radicial-surjective-universal-homeomorphism`, which converts those three properties into the required universal-homeomorphism statement. I checked `def-pc-base-change` to identify the projection `C_bar k -> C` with the base change of the Spec map, and `lem-weil-pbc-universal-homeomorphism-base-change` for stability under this base change. Finally, I checked `thm-weil-pbc-universal-homeomorphism-invariance`: its statement explicitly gives the étale-topos equivalence and compatibility with cohomology, so it yields the displayed isomorphisms for every abelian sheaf and every degree.

For Step 2 I checked `lem-weil-pbc-cohomology-pullback-functorial`, clause 4, which states that pullback along a composite is the composite of the pullbacks after the canonical inverse-image composition isomorphism. The compatible inclusions `bar k subset bar k'` over `k subset k'` make the two scheme composites from `C_bar k'` to `C` equal, so this clause gives equality of the two cohomology paths. I verified every hypothesis used by each cited statement and regenerated `citations.json`; all seven quotes are verbatim substrings of the cited node statements. I also ran the required Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch, including second phrasings for cohomology functoriality); they returned only unrelated field or scheme declarations and no exact full-item theorem. The server `check_dag` check passed before this report was written.

## What could not be finished

Nothing. No Lean source, compiler, Lake, or build tool was run.
