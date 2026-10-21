# AlgebraicGeometry.exists_openSingle_coefficient_transport

## Reason

Restore the quarantined item and repair its compatibility and compile performance against
the current adopted source library. The archive imports a retired Sheaf module and
redeclares `derivedPullback` locally irreducible. The compiler confirms the latter fails:
`failed to set [local irreducible], derivedPullback is currently [irreducible]`.

After repairing these, the full archive exceeds the normal 60-second limit. Profiling
its normalization calculations identifies repeated checking of the selected counit's
nested existence predicate. Reuse the existing `SingleComplexBaseChange.counit`
definition for exactly that counit. Fix tensor additivity once in the explicit
sheaf-module categories rather than passing a generic additivity family through the
private helpers. Keep local comparison data shared with scoped `cleanup.letToHave false`.
The public imports, theorem signature, mathematical argument, and coefficient construction
are preserved. No source-library definition or target meaning changes.

## Old

The archive uses these proof imports and local commands:

```lean
import Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts

attribute [local irreducible] derivedPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullback

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules
```

The private calculations use `pinnedPullbackCounit`, an abbreviation for the nested
selected counit, and take a generic section variable
`[add : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), (Scheme.Modules.tensorPullback f).Additive]`.
The public theorem already omits that section variable.

## New

```lean
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit

attribute [local irreducible]
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullback

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
```

The private calculations use the existing `SingleComplexBaseChange.counit` definition.
Their one fixed local additive structure is:

```lean
private instance tensorAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (show SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) from
        Scheme.Modules.tensorPullback f).Additive :=
  Scheme.Modules.canonicalTensorPullbackAdditive f
```

The open counit factorization names the `leftDerivedUnique` comparison and applies its
counit factorization before normalizing the underived comparison. A proved private
lemma supplies this inverse uniqueness factorization in general categories. The named
counit remains locally irreducible in the later private calculations. Further proved
private lemmas lift single-complex naturality in general abelian categories and paste
the final coefficient diagram, avoiding large concrete congruence proofs. The private helpers no longer take a generic
additivity family; the two corresponding local instance introductions disappear.
Scoped `cleanup.letToHave false` retains local term sharing. Kernel checking, axiom
checking, and the normal file limit remain enabled. No proof is split into another file.

The public theorem signature is unchanged, including the universe, its derived-category
instance, all scheme/module binders, and the complete coefficient compatibility equation.
The restored module has zero holes. The complete candidate with the required axiom
probe compiles in 47.3 seconds under the unchanged 60-second limit, reporting
`SHEAF-PROBED 4` with no direct holes or disallowed axioms. The only warning belongs to
the appended tool probe.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport
--allow-missing --uses exists_openSingle_coefficient_transport` lists zero live importers.
The quarantine and DAG searches identify the following archived direct consumer; its
restoration remains needed. The identical interface requires no adaptation.
No source-library module is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport | F1 | Restore the original theorem and repair private proof calculations. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux | unclaimed | Archived direct consumer; identical theorem signature and coefficient equation. |

## Status

landed 20261021T005733-L-1886698 2026-10-21 (merge of deliver/F1/Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport)
