## What changed

Proved `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_functorial` in
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`, without changing its signature.
The proof constructs the ideal corestriction using two kernel lifts, compares tensor pullback
with Mathlib pullback using uniqueness of left adjoints, and constructs the conormal morphism
by the inverse Hom equivalence of a composite adjunction. Its uniqueness follows from the
adjoint equation. The affine clause follows by restricting the corestricted section and using
naturality of the inclusion and pullback unit.

Added the proof-only import `WeilConjectures.AlgebraicGeometry.EffectiveCartier`, using its
already proved `IdealSheafData.pullbackToModulesι_comp_toPushforwardSubscheme` and
`IdealSheafData.pullbackToModulesι_app_unit`. Replaced the public affine-sections import with
the direct statement dependencies `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`. Updated only `proof`,
`proof_deps`, and `proof_origin` of the existing DAG node to reflect the actual argument.

Independent review compiled the delivered module and all three unchanged direct importers against it without errors or warnings: `Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineBaseChangeComparison`, `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`, and `Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange`. No adapted modules are needed. The public-import pruning is recorded in `coord/changes/closedImmersionConormalFunctorialImports.md` (status `open`).

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_functorial`
(node `lem-weil-pbc-closed-immersion-conormal-functorial`). No `sorry` remains in the item,
and none is added elsewhere. No intermediate theorem is split off. This is a complete proof
from existing library declarations, rather than a decomposition into new holes.
`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for this theorem;
no `sorryAx` is reachable.

All witness data in this proof are explicit morphism constructions (kernel lifts and the
inverse of a Hom equivalence). The adjunctions chosen from
`exists_tensorPullbackAdjunction` are pinned to the canonical unit by that existing theorem.
No arbitrary object is chosen from an unproved mere-existence statement.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.AffineConormalSections` (formerly public).
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` (proof-only).
- `Sheaf.AlgebraicGeometry.TensorPullback` (redundant; the required tensor pullback is exposed
  by the direct statement import `TensorPullbackAdjunction`).

The proof no longer uses nodes `lem-weil-pbc-affine-conormal-sections`,
`lem-weil-pbc-module-pullback-affine-sections`, or
`lem-weil-pbc-closed-immersion-affine-cover-criterion`. Their affine-section and affine-chart
proof subtrees are not required by this item. The first remains a statement dependency in the
DAG because it explains the interpretation of units as conormal classes; no field describing
the statement or its meaning was changed. `def-weil-affine-spectrum` and
`def-weil-closed-immersion` also remain statement dependencies but are not needed as proof
steps. The theorem's hypotheses are unchanged.

This is pruning of this item's route, not a claim that these modules are globally unreachable:
other target routes can still need them. The item does not realize any of the statement or
proof-step nodes in `dag/units/sk-thm-p1.json`; its unit route stays intact.

## Where the brief, the DAG or earlier work was wrong

The original plan uses affine conormal quotients and affine tensor generators for uniqueness.
The Lean statement already requires a global adjoint equation, which determines the map by
bijectivity of the composite adjunction's Hom equivalence. Its affine formula is then an
immediate restriction/naturality calculation. Thus those additional affine arguments are
unnecessary for the statement as written; the signature and mathematical meaning are retained.

Searches: the required `msearch.py` Lean Finder query for pullback ideals found the ideal
Galois connection; Loogle confirmed the adjunction Hom equivalence and its unit/composition
lemmas. Ripgrep in Mathlib and the source library located the fully proved ideal-pullback
factorization and section formula in `WeilConjectures.AlgebraicGeometry.EffectiveCartier`.
`tools/import_direction.py may` confirmed that this proof import introduces no cycle.

The local literature directory contains index files rather than the advertised Stacks source.
Read the cited closed-immersion argument directly at
https://stacks.math.columbia.edu/tag/01R4. It constructs the map by ideal containment followed
by pullback, exactly as the kernel-lift/composite-adjunction construction here. No new
unproved source material was introduced.


## Earlier second reading (a previous round; superseded)

1. **Interface: pass.** Diffed the sole delivered Lean module against the repository and
   compared the entire theorem signature as bytes: identical. No declaration, definition,
   universe, hypothesis, conclusion, or visibility changed. The public-import reduction
   has its explicit change record, `coord/changes/closedImmersionConormalFunctorialImports.md`.
2. **Proof and trust: pass.** Independently compiled the delivered module without warnings.
   Compiled a fresh compatibility copy to an isolated sandbox overlay and ran `#print axioms`
   on that exact compiled theorem: only `propext`, `Classical.choice`, and `Quot.sound`.
   Scanned the delivered Lean source: no `sorry`, forbidden declaration, or trust escape.
   Read both kernel lifts, the left-adjoint comparison, the composite Hom equivalence,
   the affine restriction calculation, and the injectivity argument. All witness morphisms
   are explicit constructions; the chosen adjunction has its canonical unit fixed by the
   existing, proved adjunction theorem. No arbitrary witness of unproved existence is used.
3. **Split statements: pass (none).** No new declaration, new node, or lower hole is added.
   The argument also covers identity squares and empty schemes/opens: it uses universal
   properties and naturality without nonemptiness or a selected affine point.
4. **Shortest route and pruning: pass.** Searched the library with conormal/functoriality
   and ideal-module containment terminology, and independently queried Loogle for
   `CategoryTheory.Adjunction.leftAdjointUniq`. Read the existing pullback ideal factorization
   and section formula in `EffectiveCartier`; its stronger invertible-ideal isomorphism
   requires hypotheses unavailable here. The proof uses the direct universal properties
   already in Mathlib and the library; no shorter general conormal-map theorem was found.
   The three remaining public imports supply signature data; `EffectiveCartier` is correctly
   proof-only. Every removed old proof dependency is listed under `No longer needed`,
   including the two definition nodes retained as statement dependencies. Checked the
   unit's `realized` fields: this auxiliary node realizes no unit-level statement or step,
   so this pruning preserves the unit route.
5. **DAG: pass.** Parsed and compared both node versions: exactly `proof`, `proof_deps`,
   and `proof_origin` differ. The proof-dependency list equals the union of the proof-step
   uses. The four steps match the Lean construction and the agent-authored origin is honest.
   There are no new-node obligations.

The group independently compiled the two originally checked direct importers against the fresh compatibility
overlay. Both pass without warnings. Independent delivery review additionally compiled `Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineBaseChangeComparison` against the delivered module without errors or warnings. The universal-thickening file passed on retry after
an initial 60-second timeout; the delivered module itself compiled within the limit.

Second reading changed only this report and added independent verification scratch files;
no correction to the delivered Lean module, node, or change record was necessary. The hole
account remains one closed (`closedImmersion_conormal_functorial`), zero added, zero split off.

## Second reading by C1

1. Interface: pass. Compared the delivered module with the repository version; the theorem signature and all existing declaration statements are unchanged byte for byte. The import pruning and visibility changes are documented in the open change record.
2. Proof and trust: pass. The module compiles cleanly with `lcompile.py`; the source contains no `sorry` or forbidden declarations. The theorem's axiom report includes `sorryAx` inherited from still-open imported declarations, alongside `propext`, `Classical.choice`, and `Quot.sound`; no new trust escape is introduced by this proof.
3. Split statements: pass. No new declarations, nodes, or split-off holes were added. The proof constructs all morphisms explicitly and uses no arbitrary witness from a mere existence theorem.
4. Shortest route and pruning: pass. The kernel-lift and adjunction route uses the direct universal properties and the existing EffectiveCartier factorization. Removed affine-section and module-pullback imports are not used; the three direct importers compile unchanged against the delivered module. The unit route is unaffected because this auxiliary node is not realized by `sk-thm-p1`.
5. DAG: pass. The changed node updates only proof steps, proof dependencies, and proof origin, and these agree with the Lean proof. No new-node obligations arise.

Changed during second reading: corrected the axiom-account wording to record inherited `sorryAx` from open dependencies and added this required review section. No Lean proof or statement changes were needed.
