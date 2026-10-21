## What changed

Proved all five original theorem holes in `Sheaf.CategoryTheory.RingLocalizationSheafification`.
The sectionwise fraction theorem uses Mathlib localization induction, its power-torsion
relation, addition/multiplication formulas, and localization maps. Sheafification is
constructed on a small model, and tensor stability uses the existing enriched-end theorem.
Private proved helpers translate section-ring morphisms into internal commutative monoid
morphisms and back. Mathlib `Adjunction.mapCommMon` supplies the ring sheafification
universal property. The original canonical object and unit definitions and every public
signature are preserved. The comparison isomorphism follows by both uniqueness properties.

Updated the item's DAG proof and proof dependencies to reflect this argument.
The module-interface change is recorded in
`coord/changes/F2-ring-localization-proof-interface.md`.
Removed unused public imports `Sheaf.CategoryTheory.SheafTensor` and
`Sheaf.CategoryTheory.SiteCoveringAxioms`; added the proof-only import
`Sheaf.CategoryTheory.PresheafTensorInternalHom`.

Validation: compiled the complete item through the required `lcompile.py` workflow;
delivery also runs the server compilation, axiom audit, and preflight checks.
No other Lean module was edited. No scratch Lean files or new modules were created.

## Proved and sorry left

Closed five original holes, all attached to `lem-sfb-ring-localization-sheafification`:

- `CategoryTheory.sfbLocalizationPresheaf_spec`.
- `CategoryTheory.sfbLocalization_hasSheafify`.
- `CategoryTheory.sfbLocalization_monoidalLocalEquivalences`.
- `CategoryTheory.sfbLocalizationUnderlyingUnit_isMonHom`.
- `CategoryTheory.sfbRingLocalizationSheafification`.

Zero holes remain in the item; zero holes added; zero split-off statements.
The argument applies to zero rings and to zero, nilpotent, or zero-divisor sections:
it uses localization's power-torsion equality and never cancels a power of the section.
No points or enough-points assumption is introduced.

## No longer needed

Removed imports: `Sheaf.CategoryTheory.SheafTensor` and
`Sheaf.CategoryTheory.SiteCoveringAxioms`.

The proof dependency `sk-def-sfb-sheaf-tensor` is replaced by the direct enriched-end
input `det-def-sfb-sheaf-tensor-presheaf` / `Sheaf.CategoryTheory.PresheafTensorInternalHom`
and Mathlib `GrothendieckTopology.W.monoidal`. The former remains a statement dependency
because it specifies the tensor in the node's mathematical statement; its unit route is
unchanged. Neither `SheafTensorStructure`, `SheafificationTensorLocalIso`, nor
`SheafTensor` is needed as a proof import for this item.

`det-def-sfb-ring-object-sheaf` / `Sheaf.CategoryTheory.RingObjectSheaf` is not needed:
Mathlib's lifted monoidal adjunction and the explicit conversions implement the internal
ring argument directly. No declaration or module is withdrawn. Ordinary localization,
section-ring reconstruction, and sheafification dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The original plan used the general ring-sheaf reconstruction theorem, but Mathlib already
provides `Adjunction.mapCommMon`. Applying this adjunction directly avoids that dependency
and preserves the exact original canonical construction. The enriched-end input likewise
makes the general sheaf tensor properties theorem unnecessary here.

The unit `sk-prop-sfb-cartesian-coefficients` realizes only its own statement and proof
steps; this localization node is not a unit realization. No unit statement or route changes.
No mathematical statement, definition, or target is changed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
