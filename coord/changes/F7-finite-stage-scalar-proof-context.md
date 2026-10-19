# AlgebraicGeometry.Scheme.pbcScalarSystem_units

## Reason

Complete the eight remaining scalar-extension proofs using private localization,
exact-derived coherence, and adjunction mate helpers. Record the additional private
proof context, since the mechanical scanner may classify its namespace, universe,
section, attribute, and open commands as an interface change.

The four erased integralOperations instance attributes keep universe inference on
the existing canonical coefficient instances. Erasure changes only this file's
elaboration context. The high-priority torsion-free instance is explicitly local
and restricted to the concrete coefficient-field portion of the namespace.
Backward transparency options are declaration-scoped. All new helpers are private
and fully proved. No existing signature, definition body, public import, notation,
or exported instance registration changes; no target statement changes.

## Old

```lean
theorem pbcScalarSystem_units (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ ∧
      HEq (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
        (Functor.leftUnitor (pbcScalarExtension l Ω T hdim hl h)) ∧
      HEq (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
        (Functor.rightUnitor (pbcScalarExtension l Ω T hdim hl h)) := by
  sorry
```

## New

```lean
theorem pbcScalarSystem_units (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ ∧
      HEq (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
        (Functor.leftUnitor (pbcScalarExtension l Ω T hdim hl h)) ∧
      HEq (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
        (Functor.rightUnitor (pbcScalarExtension l Ω T hdim hl h)) := by
  refine ⟨by simp [pbcScalarExtension], ?_, ?_⟩
  · exact left_unit_from_diagonal
      (pbcScalarExtension l Ω T hdim hl (le_refl E))
      (pbcScalarExtension l Ω T hdim hl h)
      (pbcScalarAssociator l Ω T hdim hl (le_refl E) (le_refl E))
      (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
      (by simp [pbcScalarExtension]) (pbc_scalar_diagonal l Ω T hdim hl E)
      (pbcScalarAssociator_cocycle l Ω T hdim hl (le_refl E) (le_refl E) h)
  · exact right_unit_from_diagonal
      (pbcScalarExtension l Ω T hdim hl h)
      (pbcScalarExtension l Ω T hdim hl (le_refl F))
      (pbcScalarAssociator l Ω T hdim hl (le_refl F) (le_refl F))
      (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
      (by simp [pbcScalarExtension]) (pbc_scalar_diagonal l Ω T hdim hl F)
      (pbcScalarAssociator_cocycle l Ω T hdim hl h (le_refl F) (le_refl F))
```

The identical theorem signature is proved from the diagonal unit equation and
pentagon, using the private `left_unit_from_diagonal` and
`right_unit_from_diagonal` cancellation lemmas. Its complete proof is in the
item module. The other seven completed theorem signatures are also identical.
The six added imports are proof-only. No public construction is replaced or
made irreducible, and no new public declaration is introduced.

## Users

`tools/downstream.py Sheaf.Paper.FiniteStagePairCategory --uses` on the eight
completed theorem names reports 1040 transitive importers. For every queried
name the only textual consumer is the item itself. Existing public definitions
retain their bodies, and their unique defining existence statements retain their
signatures. Thus every importer sees the same interface and requires no adaptation.
No module held by another group is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteStagePairCategory | F7 | Eight proofs and private helpers; existing interface unchanged. |

## Status

landed 20261019T192727-L-1860404 2026-10-19 (merge of deliver/F7/Sheaf.Paper.FiniteStagePairCategory)
