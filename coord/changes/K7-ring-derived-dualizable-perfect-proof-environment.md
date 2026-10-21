# DerivedCategory.dualizable_iff_isPerfectRingComplex proof environment

## Reason

Preflight conservatively flags the added universe, open and option commands as
changes visible to importers. This record documents the proof environment.
All new helper declarations are private and completely proved. The theorem's
signature, attributes and two public imports are unchanged. No definition body,
instance, exported notation, or target statement changes.

## Old

The original environment was:

```lean
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace DerivedCategory
```

The original theorem signature was:

```lean
theorem dualizable_iff_isPerfectRingComplex {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (Q : DerivedCategory (ModuleCat.{u} A)) :
    (∃ (D : DerivedCategory (ModuleCat.{u} A))
      (ev : D ⊗ Q ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
      (coev : 𝟙_ (DerivedCategory (ModuleCat.{u} A)) ⟶ Q ⊗ D),
      (λ_ Q).inv ≫ coev ▷ Q ≫ (α_ Q D Q).hom ≫ Q ◁ ev ≫ (ρ_ Q).hom = 𝟙 Q ∧
      (ρ_ D).inv ≫ D ◁ coev ≫ (α_ D Q D).inv ≫ ev ▷ D ≫ (λ_ D).hom = 𝟙 D) ↔
      IsPerfectRingComplex Q
```

Its body was `by sorry`.

## New

The environment is:

```lean
universe u w v t
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace DerivedCategory
```

These commands provide names and elaboration controls within this file only.
The extra universes are used by generic private helpers; the public theorem still
has exactly its original universe parameters. No heartbeat, wall-clock or kernel
checking limit is changed, and all profiling options were removed.

The new theorem has the identical signature:

```lean
theorem dualizable_iff_isPerfectRingComplex {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (Q : DerivedCategory (ModuleCat.{u} A)) :
    (∃ (D : DerivedCategory (ModuleCat.{u} A))
      (ev : D ⊗ Q ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
      (coev : 𝟙_ (DerivedCategory (ModuleCat.{u} A)) ⟶ Q ⊗ D),
      (λ_ Q).inv ≫ coev ▷ Q ≫ (α_ Q D Q).hom ≫ Q ◁ ev ≫ (ρ_ Q).hom = 𝟙 Q ∧
      (ρ_ D).inv ≫ D ◁ coev ≫ (α_ D Q D).inv ≫ ev ▷ D ≫ (λ_ D).hom = 𝟙 D) ↔
      IsPerfectRingComplex Q
```

Its complete proof uses the existing K-flat signed-duality API in one direction
and compact generation plus perfect thick closure in the other. New imports
are private proof imports. The existing public imports are verbatim unchanged.

## Users

`tools/downstream.py --uses DerivedCategory.dualizable_iff_isPerfectRingComplex`
reports five downstream modules and one downstream textual user. The latter,
`ContractibleLisseEvaluation.perfect_iff_dualizable`, rewrites with exactly the
unchanged equivalence. It does not refer to any new private helper. All downstream
public statements and definitions retain the same meaning; no source adaptation
is necessary. This is a source/interface check, not a downstream global build.
No target definition changes, so target-statement review is not reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect | K7 | Proof completed; public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Transitive importer; public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Transitive importer; public API unchanged. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Transitive importer; public API unchanged. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Sole direct user; exact theorem signature preserved. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Transitive importer; public API unchanged. |

## Status

landed 20261021T134501-L-1205097 2026-10-21 (merge of deliver/K7/Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect)
