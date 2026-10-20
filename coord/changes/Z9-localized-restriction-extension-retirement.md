# CategoryTheory.localized_restriction_extension_exists

## Reason

Complete the retirement item in coord/retire-items.tsv. The Sheaf module duplicates
its proved WeilConjectures twin except for the public propositional wrapper
CategoryTheory.extensionSheafAdjunction_nonempty. That wrapper has one consumer.
The source module already constructs the same adjunction as a proved private
definition. A proof-only import all lets the consumer reuse this construction
directly. No source-library file, target statement, or surviving signature changes.
No new module, theorem, definition, or proof obligation is introduced.

## Old

In Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists:

```lean
theorem localized_restriction_extension_exists
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms) :
    ∃ (G : SheafOfModules.{max u v} (R.over U) ⥤ SheafOfModules.{max u v} R),
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      Nonempty (G ⊣ SheafOfModules.overFunctor.{max u v} R U)

theorem extensionSheafAdjunction_nonempty
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    Nonempty ((SheafOfModules.extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)) ⊣
        SheafOfModules.overFunctor.{max u v} R U)
```

## New

The item module is withdrawn using deleted.txt. The first theorem, with exactly
the same signature, is provided by
WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists.
The redundant Nonempty wrapper and duplicate private helpers are removed.

ProjectionCompactification replaces its private proof import by the source twin.
RingedSliceExtensionPreservesExact replaces its private proof import by
`import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists`
and replaces
`let adj := (CategoryTheory.extensionSheafAdjunction_nonempty R U).some`
by
`let adj := CategoryTheory.extensionSheafAdjunction R U`.
This is the same concrete sheafified direct-sum adjunction, now obtained from its
proved construction without choosing through the redundant propositional wrapper.
The import is private; the source definition remains private in its own module.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists | Z9 | Withdraw duplicate module; reattach its node to the source theorem. |
| Sheaf.CategoryTheory.RingedSliceExtensionPreservesExact | unclaimed | Replace proof import and adjunction expression; signature and remaining proof unchanged. |
| Sheaf.Paper.ProjectionCompactification | unclaimed | Replace one private proof import; declarations unchanged. |

These are all current direct consumers and all textual declaration users reported
by tools/downstream.py --uses for the two public theorem names. Its 56 transitive
downstream modules need no other adaptations. The inventory's third consumer,
Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction, has already been retired;
its source twin already imports the source twin of this item.
Both adapted consumers were unclaimed when inspected. After changing only the
exactness consumer's import, compilation fails at line 91 with
`Unknown identifier CategoryTheory.extensionSheafAdjunction_nonempty`.
The single proof-expression replacement repairs it. Both adapted files compile
alone in the delivered overlay (5.4 s and 5.0 s respectively).
No definitions or meanings of downstream statements change; no target meaning
review is reopened. The DAG retains the direct-sum adjunction and exactness route.

## Status

landed 20261020T144313-L-2264786 2026-10-20 (merge of deliver/Z9/Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists)
