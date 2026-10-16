# isFlat_algebraicInverseImageOfUniverses: proof scope commands

## Reason

The proof needs private finite-product, equalizer, relation-sheaf and witness-sheaf helpers.
Preflight conservatively treats added universe, open, section, and option commands as a
change visible to importers. This record documents the syntactic scope change. The existing
public theorem signature and public imports are unchanged; there is no semantic interface
change and no forced adaptation.

## Old

The original scope commands, verbatim:

```lean
universe uC vC uD vD r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules
```

The existing public signature, unchanged in the delivery:

```lean
theorem isFlat_algebraicInverseImageOfUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    [HasWeakSheafify K AddCommGrpCat.{max r m}]
    {R : Sheaf J CommRingCat.{r}} {RI : Sheaf K CommRingCat.{r}}
    (uInv : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m)))
    (uPush : Sheaf K (Type (max r m)) ⥤ Sheaf J (Type (max r m)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImageOfUniverses uInv R RI)
    (F : ringedSiteModules.{max r m, r, vC, uC}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hF : IsFlatOnSite F) : IsFlatOnSite (I.modules.obj F)
```

## New

The replacement scope commands before the private helpers, verbatim:

```lean
universe uC vC uD vD r m w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency false


section Sections

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
```

The `Sections`, `Operations`, and `ImageOperations` helper sections close before the
existing public theorem; the noncomputable section closes after it. The added universe `w`
is used only by private helpers and does not enter the public theorem's universe parameters.
The assigned module's helpers are private and proved. The transparency option affects proof elaboration only.
The public theorem has exactly the Old signature above.

The redundant direct proof import of `TensorProductOfUniverses` is removed because
`FlatOnSite` publicly imports it. New proof dependencies are plain imports. The new local-families and iff-criterion modules each expose one proved theorem. The
forward local-relations module also exposes the proved shared theorem
`TensorProduct.exists_relations_with_coefficients`; the iff module imports and reuses it.
Its duplicate private copy in the iff module is removed. All other construction and
algebra helpers remain private.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback` | unclaimed (no claim in the shared snapshot) | Same public theorem, universes, assumptions, conclusion, and public imports. |

This is the only direct importer in the repository. Transitive importers receive the same
public interface and target meanings. Only the assigned module and new modules are delivered.
No target statement or definition used by a target changes, so no target review reopens.

## Status

landed 20261016T020325-L-854160 2026-10-16 (merge of deliver/D4/Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses)
