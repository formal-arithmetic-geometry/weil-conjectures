## What changed

Restore `lean/Sheaf/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/ExchangeMono.lean`
byte for byte from the quarantine path recorded in `coord/rework.tsv` (cluster restoration
reverted at 5f7b33eac). The live source was absent; this delivery restores its actual proved
implementation, rather than withdrawing the node or replacing its content with an empty module.
All original public imports, declarations, signatures, private support abbreviations, and proof
bodies are preserved. The existing node `stage3-sfb-open-base-change-component-mono`, its Lean
attachment, and all four proof dependencies remain accurate and unchanged.

The proof first detects the support of ordinary module pullback of extension by zero using the
abelian-sheaf base-change isomorphism and the forgetful comparison. It transports invertibility
of the counit through scalar equivalences, exact derivation, and the fully faithful bounded
constructible inclusion. Finally the prescribed unit-square-counit composite consists of
isomorphisms and is therefore monic. This follows the node's existing five-step proof and the
unit's exchange construction without any new intermediate statement.

The restored module compiled cleanly through `lcompile.py` in 16.7 seconds. The three direct
consumers in the live and quarantined trees were checked: lower-shriek `MorphismDefs`,
`ExchangeSection`, and `CompactificationRefinementLocalizing`. All receive precisely their
archived interface, including the support helpers accessed through `import all`; none needs
adaptation. The delivery tool performs its independent compilation and axiom probe.

Change record: `coord/changes/J2-restore-open-shriek-exchange-mono.md`.

## Proved and sorry left

This is restoration of an already proved, zero-hole module: 0 holes closed, 0 holes added,
0 split off, and 0 remaining. The public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono`
is proved in the restored implementation. All five private counit helpers and all seven private
shared support abbreviations retain their complete proofs. There is no `sorry` in the file.
No claim of a new mathematical proof-hole closure is made.

## No longer needed

None. No import, declaration, node, module, or planned dependency is pruned. In particular the
quarantined parent modules still require this node. The `CondensedOpenClosedRecollement`
import-all supplies the open-unit proof and the forgetful/support context; ordinary sheaf
base change, full faithfulness, and complement vanishing imports retain their uses.

Fresh searches: LeanFinder for derived open-immersion extension-by-zero base change found
only ringed-space open-immersion results, not a replacement. Loogle found
`CategoryTheory.Adjunction.isIso_counit_app_of_iso`, already used in the archived proof.
Mathlib grep found that same fully faithful adjunction lemma; local source search located
the abelian base-change implementation already used here. No shorter replacement is needed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof-hole item, but the actual rework row assigns restoration
of a quarantined, already sorry-free module. Its absence from the live library was caused by
a reverted cluster restoration, not by withdrawal of the mathematics. Restoring the complete
archived source repairs this missing-module defect. No statement, definition, target meaning,
DAG proof route, or blueprint unit is changed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
