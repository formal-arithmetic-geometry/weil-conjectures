## What changed

Replaced the hole in `SheafOfModules.arithmeticSystemRightAdjoint` with an assembly
of two strictly smaller steps from the existing six-step plan. The original
statement, binder names, universes, and component normalization records are unchanged.

The assembly constructs `r(n)=e(n+1)-1` as an order embedding, proves the required
floor inequality from natural-number division, obtains the ordinary exact floor
extension, and constructs all four derived fields directly. Preservation of
quasi-isomorphisms follows from exactness; the derived-unit and derived-counit
formulas follow from the specified localization and cancellation of the exact
functor factorization isomorphisms. It constructs the selected coefficient map β
from α and proves its naturality and component formula, then applies the separate
common-coefficient comparison to the already specified ordinary extension.

Extracted the three original records verbatim into
`Sheaf.CategoryTheory.ArithmeticSystemRightAdjointData`, publicly reexported by
the item. Added `ArithmeticSystemOrdinaryFloorData` containing precisely the eleven
ordinary fields of `ArithmeticSystemFloorData`, without its four derived fields.
This is necessary to state the two independent proof steps without an import cycle.
See `coord/changes/arithmetic-system-right-adjoint-data.md`; the downstream checks
find zero external consumers of the original module or these record names.

Validation: all four modules compiled through `lcompile.py`; the final item compile
completed in 7.6 seconds without errors or warnings. The definition module compiled
in about 26 seconds, and each split statement module in under 7 seconds. Static
checks confirmed the unchanged original theorem signature and unchanged relocated
record declarations, matching node signatures, named theorem-only holes, 100-column
Lean lines, stated dependencies and absence of dependency cycles.

## Proved and sorry left

This is a decomposition, not a complete proof or net hole reduction.

- Closed the original hole `SheafOfModules.arithmeticSystemRightAdjoint`
  (`lem-sp-arithmetic-system-right-adjoint`) by a real assembly proof.
- Added one hole `SheafOfModules.arithmeticSystemFloorExtension`
  (`lem-sp-arithmetic-system-floor-extension`), the ordinary additive exact floor
  construction and normalized Hom bijection. It asserts no derived-limit comparison
  or derived-unit/counit localization formula.
- Added one hole `SheafOfModules.arithmeticSystemFloorLimitComparison`
  (`lem-sp-arithmetic-system-floor-limit`), the common-coefficient comparison for a
  GIVEN ordinary floor extension. It neither constructs R nor asserts its existence.
- No other holes occur in this delivery. In particular, the data module and item
  contain zero holes, and no definition obtains data by choosing an unproved witness.

The arithmetic embedding, division inequality, quasi-isomorphism fields, two
localization normalization formulas, and selected coefficient natural transformation
are proved directly in the item. Each remaining hole has a source, a complete
natural-language proof and its own module and node. The empty prefix when e=1,
zero target prefix when e>1, and arbitrary coefficient/derived universes are
explicitly covered in the statements and proof descriptions.

## No longer needed

Removed these direct imports from the item:

- `Sheaf.CategoryTheory.SystemLevelLeftExtension`: the construction uses the strict
  category and componentwise exactness definitions/API, publicly supplied by
  `SystemLevelLeftExtensionBasic`, rather than the full derived LEFT-extension theory.
- `Sheaf.CategoryTheory.ExactDerivedAdjunction`: still publicly supplied by the data
  module and used by the proof; it is not a mathematical dependency pruned away.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  removed as a public import; its K-injective model is a planned tool for the
  limit-comparison obligation.
  The limit pair RF,η is already given by the item's hypotheses.
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`: removed as a public
  import; its definitions are publicly supplied by the data module, and its comparison
  theorem remains a planned dependency of the split limit-comparison node.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: removed; scalar exactness
  remains a planned dependency of the two split statements. Their still-unproved
  modules import only their statement dependencies.

The parent node now uses the two split statements and the actual exact-localization
and data dependencies. Its former direct uses of
`lem-pur-system-level-left-extension`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-sp-strict-tower-arithmetic-restriction` and
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` are no longer direct uses.
Scalar exactness and arithmetic restriction remain DAG dependencies of the split steps;
the full derived left-extension theorem is unnecessary for this proof route.
No module is withdrawn and no global unreachability is asserted.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically usable; no statement is disputed.
Its existing declarations do not themselves construct the ordinary varying-ring
right adjoint or the compatible scalar-forgetting tower functors. The existing
constant-coefficient arithmetic-restriction theorem is stated with the coefficient
universe containing the site universes, whereas this item's coefficient universe
is independent under EssentialSmall. The remaining comparison step records the
required transport through a coefficient-universe small-site model; it does not
silently impose a larger-universe hypothesis on the item.

The unit route is unchanged. The original three records were kept verbatim;
their relocation avoids a circular import when expressing the ordinary and limit
steps separately. There was no interrupted delivery or compilation to repeat at
resumption: the sandbox contained only dispatcher metadata.

## New nodes

`def-sp-arithmetic-system-adjunction-data` owns the three unchanged records and
the new ordinary-field subrecord. Its module contains concrete structures only,
with no existence claim and no hole.

`lem-sp-arithmetic-system-floor-extension` records steps 1–4 of the original plan:
the ordinary additive exact construction, its Hom bijection and selected unit and
counit formulas, for the already given arithmetic embedding and floor inequality.

`lem-sp-arithmetic-system-floor-limit` records step 6: exact scalar forgetting and
the normalized common-coefficient comparison, conditional on a specified ordinary
floor extension and on the specified total derived limit pair. Step 5 is proved
in the original item, not split into another hole.

Change record: `coord/changes/arithmetic-system-right-adjoint-data.md`.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
