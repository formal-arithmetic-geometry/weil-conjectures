# constructible_internalHom_continuity (private proof context)

## Reason

Stage-3 preflight requires a record for new universe/attribute/instance commands.
The native/ringed comparison and the closed-support calculation contain large
coefficient functor types. Proved categorical helpers and local transparency
settings keep these constructions abstract. A private instance fixes the same
small Grothendieck-derived localization used by the existing comparison API.
It has a complete body and introduces no new assumption or public declaration.

The private continuity property is a proposition structure with named fields,
which avoids repeated unfolding of the large conjunction when the kernel checks
its consumers. No old statement, definition, visibility, public import or target
meaning changes. The unit-route CartesianCoefficients import is retained.

## Old

The module had only `universe u`, no local irreducibility registrations, and no
private derived-category instance or native continuity property. Its public
theorem was the unchanged assigned signature, with proof `by sorry`.

## New

The proof-only context is:

```lean
universe a b d v w

attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.homComplexFunctor CategoryTheory.derivedInternalHomOfUniverses
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  HasDerivedCategory.ofIsGrothendieckAbelian
```

The additional private, constructed instance is:

```lean
private noncomputable instance ringedModulesDerived
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1}
      (CategoryTheory.RingedHomUniverses.Modules.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ModuleObjectRingedComparison.ring Λ.X X)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _
```

The instance body is the existing Grothendieck-derived construction. The
transparency attributes are local and no importer inherits them. The only other
options adjust elaboration/typeclass budgets and turn off the private-module
style linter (the module has its public theorem; profiling showed about 30 seconds
spent scanning imported private declarations). No kernel checking is disabled.
Every new helper is private and proved, and no private declaration occurs in the
public theorem signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstructibleInternalHomContinuity | F7 | The existing theorem is proved with the identical signature and public imports. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Existing import retained; statement and public interface identical; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Existing import retained; statement and public interface identical; no adaptation. |

`tools/downstream.py Sheaf.Paper.ConstructibleInternalHomContinuity --uses
AlgebraicGeometry.ProEtale.constructible_internalHom_continuity` reports these two
importers and only the item itself as a textual declaration-name occurrence.
Their source import headers were read. No consumer requires a source adaptation:
all additional instances/helpers are private and all attribute commands are local.
No source-library file is changed.

## Status

landed 20261021T193234-L-1017514 2026-10-21 (merge of deliver/F7/Sheaf.Paper.ConstructibleInternalHomContinuity)
