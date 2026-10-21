# CategoryTheory.SubterminalImageCalculus.restrictionComp

## Reason

The original compositor appends the inverse complex-composition isomorphism of an identity
functor isomorphism. Its domain and codomain already agree definitionally. Matching this
redundant term against the ordinary overlap calculation and the normalization signature
causes large definitional-equality searches and 60-second compilation failures. Retain the
termwise image of `overFunctorMap.symm` alone. Componentwise the removed isomorphism is the
identity; the old and new morphisms are equal by complex extensionality and composition with
identity. No functor, ring action, map, or normalization equation changes mathematically.

## Old

```lean
def restrictionComp {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u r})
    {X Y : C} (f : X ⟶ Y) :=
  NatIso.mapHomologicalComplex
    (SheafOfModules.overFunctorMap.{max u r} (ring R) f).symm (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (SheafOfModules.overFunctor.{max u r} (ring R) Y ⋙
          SheafOfModules.overMap.{max u r} (ring R) f)) (.up ℤ)).symm
```

## New

```lean
def restrictionComp {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u r})
    {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overFunctor.{max u r} (ring R) X).mapHomologicalComplex (.up ℤ) ≅
      (SheafOfModules.overFunctor.{max u r} (ring R) Y).mapHomologicalComplex (.up ℤ) ⋙
        (SheafOfModules.overMap.{max u r} (ring R) f).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex
    (SheafOfModules.overFunctorMap.{max u r} (ring R) f).symm (.up ℤ)
```

The explicit type (added by the reviewer) keeps the published signature of `restrictionComp`
unchanged: without it the inferred codomain would be `(F ⋙ G).mapHomologicalComplex` instead
of `F.mapHomologicalComplex ⋙ G.mapHomologicalComplex`. Only the body changes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SubterminalDerivedImageCalculus --uses
CategoryTheory.SubterminalImageCalculus.restrictionComp` reports one downstream module,
`Sheaf.Paper.TransverseTameOpenShriekExchange`, and the item itself as the only textual
user of `restrictionComp` (three occurrences). The downstream importer has no reference to
this namespace and needs no consumer adaptation. The target declarations do not mention this definition; its semantic equality is
recorded above for the independent reader.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SubterminalDerivedImageCalculus | U7 | Equivalent compositor; theorem has the same elaborated type, with explicit universe annotations; private component lemma becomes reflexivity. |

The current importer is unclaimed in the current claim records:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed | Proof import only; no reference to the changed definition or namespace; no adaptation. |

## Delivery path

This record is delivered as `coord/changes/U7-subterminal-restriction-compositor.md`.
Return C-190f6 (head `190f6fbecdc`) reports that the landing used the bare basename in
`--apply-fixes`, which did not identify a file of the delivery. Any reviewer fix must
use the full repository path above, including `coord/changes/`. This record is present
in the sandbox at that path and is included by `deliver3.py`; it remains open until
the maintainer verifies the global build.

## Status

landed 20261021T173346-L-3591234 2026-10-21 (merge of deliver/U7/Sheaf.CategoryTheory.SubterminalDerivedImageCalculus)
