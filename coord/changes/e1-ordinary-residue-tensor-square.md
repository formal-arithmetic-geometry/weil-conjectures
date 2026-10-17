# residueOrdinaryRestrictedRegularPullIso

## Reason

The ordinary balanced-tensor square must refer to the existing, named coefficient
isomorphism without importing the derived counit theorem it helps prove. Move its
unchanged construction to `Sheaf.Paper.IntegralResidueOrdinaryTensorSquare` and publicly
reexport it through a direct public import by the original module. Homotopy normalization
also imports the ordinary square publicly because its statement uses the isomorphism.
The original counit theorem keeps its exact signature, including its local coefficient
and counit constructions. No target statement or mathematical definition changes.

## Old

In `Sheaf.Paper.IntegralResidueScalarCounitModel`:

```lean
@[irreducible] noncomputable def residueOrdinaryRestrictedRegularPullIso
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*⟦Λ⟧.obj
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) ≅
      (Mod.comap (coefficientMap φ X)).obj (Mod.regular (condensedRingObj A X)) := by
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  letI := residueOrdinaryUpperStarMonoidal A f
  exact (comapUpperStarIso φ f).symm.app (Mod.regular (condensedRingObj A Y)) ≪≫
    SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
```

## New

In `Sheaf.Paper.IntegralResidueOrdinaryTensorSquare`, publicly reexported by the old module:

```lean
@[irreducible] noncomputable def residueOrdinaryRestrictedRegularPullIso
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*⟦Λ⟧.obj
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) ≅
      (Mod.comap (coefficientMap φ X)).obj (Mod.regular (condensedRingObj A X)) := by
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  letI := residueOrdinaryUpperStarMonoidal A f
  exact (comapUpperStarIso φ f).symm.app (Mod.regular (condensedRingObj A Y)) ≪≫
    SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
```

## Users

`tools/downstream.py Sheaf.Paper.IntegralResidueScalarCounitModel --uses
residueOrdinaryRestrictedRegularPullIso` reports 24 downstream modules and two actual users
(second reading, current shared source).
The declaration name, visibility, universe, type and constructed term are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueScalarCounitModel | E1 | Same signature; imports the moved definition publicly and proves the counit theorem. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | claimed elsewhere; unmodified | Its original source continues to see the same definition through the existing public import. |

The new ordinary square uses the moved definition; the homotopy normalization uses that
square. No existing consumer needs an adaptation. Their statements retain the same meaning.
Consumer compilation is recorded in report.md.

Return H10 additionally restores the private mate, unit and factor calculations in
the counit module and removes its dependency on the flat-model module. This is a
proof-only repair: all copied helpers stay private and the existing public
signatures, visibility and coefficient construction remain unchanged. No existing
consumer source is adapted by the repair.

## Status

landed 20261017T063346-L-528999 2026-10-17 (merge of deliver/E1/Sheaf.Paper.IntegralResidueScalarCounitModel)
