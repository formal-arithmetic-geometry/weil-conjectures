# AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIso

## Reason

The 2026-10-20 sync restored the upstream definitions of all five canonical derived
comparison isomorphisms. The extracted Sheaf module still defined those same fully
qualified constants. Restoring the assigned quarantined module therefore failed at
its imports: the environment already contained
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'` from the upstream
smooth base-change module. Every one of the five declaration texts, from
`noncomputable def` through its body, is byte-identical in the two source modules.
Retain the upstream definitions and turn the Sheaf file into a compatibility re-export.
This is a duplicate-definition repair, with no change to any defining term or type.
No source-library file is changed.

The assigned extracted module also ends with an orphaned `variable (p) in` before
`end AlgebraicGeometry`. Once the import clash was repaired the compiler rejected
that scope. Remove only the dangling command. Keep the private transport lemma,
its complete proof, and all original public imports. The module now contains only
that private helper; disable `linter.privateModule` for this compatibility file.
Rewrap the extraction comment to respect the 100-character line limit.

The definition node `def-weil-pbc-fixed-derived-comparisons` now points to the
upstream module and the same five declaration names. Its mathematical statement,
statement dependencies, proof dependencies, and the unit route are unchanged.
No node is attached to the assigned extracted module in the current DAG.

## Old

The comparison module, verbatim:

```lean
/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-! # Canonical comparison isomorphisms for derived base change

These are the unchanged constructions extracted from the smooth base-change module. -/

@[expose] public section

universe u' u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry
open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (f) in
/-- Blueprint `prop-weil-pbc-comparison-direct-image`: for `f` quasi-compact and
quasi-separated, the canonical isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` on bounded below derived
categories, the base change morphism of right derived functors induced by the underived
comparison `ν_Y^* f_* ⟶ f_* ν_X^*`
(`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`). -/
noncomputable def rightDerivedLowerStarComparisonPlusIso [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ D+(ν^*(Y)[A]) ≅ D+(ν^*(X)[A]) ⋙ R+(ProEtale.lowerStar A f) :=
  have := isIso_lowerStarComparisonUpperStarBaseChange f A
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f A)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f A))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective A f I)
  asIso (Functor.rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange f A))

variable (f) in
/-- The isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` of
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso`, with the pro-étale direct
image the unbounded right derived functor, as functors `D⁺(X_ét) ⥤ D(Y_proét)`. -/
noncomputable def rightDerivedLowerStarComparisonIso' [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[A]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[A]) ⋙ R(ProEtale.lowerStar A f) :=
  Functor.isoWhiskerLeft R+(Etale.lowerStar A f)
      (ν^*(Y)[A]).mapDerivedCategoryPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarComparisonPlusIso f A) DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft D+(ν^*(X)[A])
      (ProEtale.lowerStar A f).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight (ν^*(X)[A]).mapDerivedCategoryPlusCompatibility
      R(ProEtale.lowerStar A f)

end Comparison

variable (Λ : Type (u + 1)) [CommRing Λ]

variable (g) in
/-- (blueprint: def-weil-pbc-fixed-derived-comparisons)
Blueprint `lem-weil-pbc-comparison-pullback`: the canonical isomorphism
`ν_{Y'}^* g^* ≅ Lg^* ν_Y^*`, as functors `D⁺(Y_ét) ⥤ D(Y'_proét)`. It is induced by the
underived isomorphism `AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`, the
derived pullback of the exact functor `g^*` being computed degreewise. -/
noncomputable def leftDerivedUpperStarComparisonIso :
    D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g) ⋙ DerivedCategory.Plus.ι ⋙
        D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g) :=
  Functor.isoWhiskerRight
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
      D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]))
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm

variable (f g) in
/-- The comparison `ν_{Y'}^* g^* Rf_* ≅ Lg^* Rf_* ν_X^*` of the sources of the étale and the
pro-étale exchange maps, as functors `D⁺(X_ét) ⥤ D(Y'_proét)`. -/
noncomputable def baseChangeSourceComparisonIso [QuasiCompact f] [QuasiSeparated f] :
    (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g)) ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g) :=
  Functor.isoWhiskerLeft R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
      (leftDerivedUpperStarComparisonIso g Λ) ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ))
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)

variable (g' f') in
/-- The comparison `ν_{Y'}^* Rf'_* g'^* ≅ Rf'_* Lg'^* ν_X^*` of the targets of the étale and the
pro-étale exchange maps, as functors `D⁺(X_ét) ⥤ D(Y'_proét)`. -/
noncomputable def baseChangeTargetComparisonIso [QuasiCompact f'] [QuasiSeparated f'] :
    (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g') ⋙ R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f')) ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g') ⋙
          R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f') :=
  Functor.isoWhiskerLeft D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g')
      (rightDerivedLowerStarComparisonIso' f' (ModuleCat.{u + 1} Λ)) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComparisonIso g' Λ)
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f')

end ProEtale

end AlgebraicGeometry
```

The assigned module's final commands, verbatim:

```lean
variable (p) in
end AlgebraicGeometry
```

## New

The comparison module:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-! # Canonical comparison isomorphisms for derived base change

The five canonical comparison constructions are now supplied by the upstream module.
This compatibility module re-exports those same constructions instead of defining them twice.
Source: the upstream smooth base-change module.
(blueprint: def-weil-pbc-fixed-derived-comparisons)
-/
```

The assigned module retains all declarations and public imports. Its final command is:

```lean
end AlgebraicGeometry
```

Immediately after `open scoped CategoryTheory.Functor` it now contains:

```lean
-- The sync left this compatibility module with a proved private helper only.
set_option linter.privateModule false
```

## Users

`tools/downstream.py` lists the nine live consumers below. Text search of both live
and quarantined sources adds `ProperDirectImageFiniteness` and the assigned archive.
The comparison module itself was unclaimed in the local claim snapshot. Since each
of the five upstream declarations is textually identical, every use keeps the same
meaning; no target definition changes and no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactSupportProperFactor | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.AlgebraicGeometry.TorsionStalkProEtaleResolutionMap | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.Paper.ProperDirectImageFiniteness | unclaimed in local claim snapshot | Same five names, types and defining terms; no consumer edits. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | P4 (assigned) | Same five names, types and defining terms; no consumer edits. |

All nine live consumers compiled unchanged against the repaired comparison module
via `lcompile.py --all`; each took less than ten seconds. The additional archived
direct consumer `Sheaf.Paper.ProperDirectImageFiniteness` compiled unchanged in
12.3 seconds. Both delivered files compile without errors or warnings. Consumer
copies were removed after checking and are not delivered.

## Status

landed 20261020T161736-L-3530137 2026-10-20 (merge of deliver/P4/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange)
