# AlgebraicGeometry.ringComplex_godement_functorial

## Reason

The complete proof needs category-theoretic notation, scalar-restriction notation,
noncomputable private constructions, and local elaboration controls. The static
delivery check flags the added `open`, `noncomputable section`, options and local
`attribute` commands as a possible interface change. This record documents them.
No existing declaration signature, public import or construction is changed.

The local irreducibility attributes prevent elaboration from unfolding the large
chosen Godement construction. All added helpers are private and completely proved.
The two new Mathlib imports and the `import all` of the existing model-map module
are proof imports. No target definition or statement changes meaning.

## Old

```lean
theorem ringComplex_godement_functorial :
    ∃ m : RingComplexMaps (fun A I ↦ ringComplexGodement A I.val),
      RingComplexFunctorial (fun A I ↦ ringComplexGodement A I.val)
        (fun A I ↦ ringComplexGodementAugmentation A I.val) m := by sorry
```

The original commands were `set_option autoImplicit false`, `universe u`,
`open CategoryTheory`, and `namespace AlgebraicGeometry`.

## New

The signature is verbatim unchanged:

```lean
theorem ringComplex_godement_functorial :
    ∃ m : RingComplexMaps (fun A I ↦ ringComplexGodement A I.val),
      RingComplexFunctorial (fun A I ↦ ringComplexGodement A I.val)
        (fun A I ↦ ringComplexGodementAugmentation A I.val) m := by
```

Its body now constructs the semilinear mapping-fibre maps and proves their
differential, augmentation, identity and composition equations. Added commands:

```lean
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] ringComplexGodementModel ringComplexGodementUnit
  ringComplexGodementResolution resmap
```

These commands support elaboration of this proof and its private helpers. The
irreducibility attributes are explicitly local. No persistent public attribute,
notation or instance is added.

## Users

`python3 tools/downstream.py Sheaf.Paper.RingComplexGodementFunctorial --uses
ringComplex_godement_functorial` reports zero downstream modules and only the
declaration's own module as a textual user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingComplexGodementFunctorial | D5 | Existing hole closed; signature unchanged. |

No consumer needs adaptation. No other module is edited.

## Status

landed 20261020T131946-L-1395212 2026-10-20 (merge of deliver/D5/Sheaf.Paper.RingComplexGodementFunctorial)
