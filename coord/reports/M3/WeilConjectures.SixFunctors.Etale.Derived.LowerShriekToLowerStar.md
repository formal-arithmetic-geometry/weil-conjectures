## What changed

Closed the sole hole in
`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar` without changing
any statement, definition, visibility, universe or existing public import. Added the proof-only
import `WeilConjectures.SixFunctors.Etale.LowerShriek.Proper`.

The proof applies the existing sheaf-level clopen comparison theorem using the closed range
of the closed immersion. Deriving this natural isomorphism and identifying the right derived
functor of the exact extension-by-zero functor with its levelwise functor gives
`e : D(j_!) ≅ Rj_*`. The existing invertible unit of `D(j_!) ⊣ D(j^*)` makes `D(j_!)` fully
faithful, so `Rj_*` is fully faithful as well. Mathlib's
`CategoryTheory.Adjunction.isIso_unit_app_of_iso` then makes the unit of `D(j^*) ⊣ Rj_*`
invertible at every `D(j_!) K`, using `e.app K`. Thus the first whiskered factor in the
comparison is invertible. The associator and the final whiskering of the inverse of the
extension-by-zero unit are already invertible; instance synthesis closes the result.

This is the original sheaf-comparison argument with categorical essential-image reasoning
for the compatibility step. It requires no comparison equality and no new intermediate theorem.
The argument applies equally to an empty source, an identity immersion and disconnected
schemes: it imposes no condition beyond the original open and closed immersion hypotheses.

Local single-file compilation passed in about 3 seconds. All three added candidate imports
were checked for cycles before use. Mathlib searches were run through msearch.py with
LeanFinder, Loogle and grep; they confirmed `Adjunction.isIso_unit_app_of_iso`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar`.
No `sorry` remains in the item. No holes, declarations or modules were added.

## No longer needed

No original imports or attached DAG dependencies were pruned. The attempted proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion` were removed before
completion: full faithfulness transfers directly from the already available derived
extension-by-zero adjunction. These were search candidates, not dependencies of the original
module, so no newly unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The item has no `(blueprint: ...)` annotation and no matching DAG node: searches for its
module, file and declaration names in `dag/nodes/` found none. Consequently there is no
existing node or unit attachment to update. The delivery only fills the original proof by
its existing sketch, using proved library and Mathlib declarations, and leaves the existing
API and compactification route unchanged. No mathematical defect was found.

The first dry run required a change record because the interface checker compares entire
instance bodies. The record `coord/changes/clopen-derived-shriek-star-instance-proof.md`
contains the old and new proof and the complete downstream inventory; no consumer adaptation
is needed. The second-reading section is deliberately left to the independent second reader,
as the worker brief requires (deliver3.py allows this sole remaining check during dry runs).

## Second reading by M3

1. **Comparison with the repository.** I diffed the delivered module against the repository
   version. The existing declaration signatures, definitions, visibility and universes are
   unchanged byte for byte. The only edits are the proof of
   `isIso_derivedOpenImmersionLowerShriekToLowerStar` and one proof-only import. Verdict: pass.

2. **Compilation and trust.** The sandbox module compiles with `lcompile.py` and contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern` or `implemented_by`. A scratch `#print axioms`
   for the closed instance reports only `propext`, `Classical.choice` and `Quot.sound`. Verdict:
   pass.

3. **Statements and split-offs.** No statement was split off and no new node or theorem was
   added. The existing clopen comparison theorem is applied at exactly its stated strength;
   the derived isomorphism is obtained by the canonical right-derived comparison and the
   existing adjunction full-faithfulness theorem. Searches found no duplicate intermediate
   declaration. Verdict: pass.

4. **Pruning and route.** The proof uses the existing sheaf-level clopen comparison, the
   exact-functor derived comparison, and the adjunction unit criterion. The added
   `LowerShriek.Proper` import is required (removing it produces unknown-identifier errors);
   no unused original imports or DAG dependencies were introduced or removed. The module has
   no matching DAG node or unit attachment, so there is no route metadata to update. Verdict:
   pass.

5. **DAG agreement and delivery metadata.** The proof body agrees with the report and the
   audit entry for the existing instance; it closes the sole hole and adds none. The required
   proof-change record is present, lists downstream users, and requires no adaptations. Verdict:
   pass.

I changed only this report section during second reading; no Lean source, declaration, node or
change record required repair.
