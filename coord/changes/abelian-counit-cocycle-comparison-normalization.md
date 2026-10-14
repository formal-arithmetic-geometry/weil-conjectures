# abelianInjectiveResolutionIso

## Reason

The counit leaf needs the already-proved source evaluation theorem, but its old module imported the leaf. Move the constructors and the evaluation theorem below the leaf to remove that import cycle. The old evaluation module becomes a public re-export, preserving its declaration name and signature.

The original injective comparison went through the general acyclic-resolution constructor. Unfolding that constructor in the cocycle proof repeatedly exposed large derived-comparison terms and exceeded the 60-second compile limit. Use the ordinary injective comparison in this constructor and expose the proved equality `abelianInjectiveResolutionIso_eq_acyclic` with the original construction. All existing signatures remain identical. No target statement changes, and equality of the actual isomorphisms preserves the meaning of every downstream use.

## Old

The constructors were in `Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation`:

```lean
abbrev abelianPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

def abelianAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    invImage f ⊣ abelianPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base

def abelianExtSectionsIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      ((abelianSections X).rightDerived p).obj
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) :=
  (Abelian.Ext.precompAddEquiv (terminalSourceIso X)
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p

def abelianInjectiveResolutionIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
  abelianExtSectionsIso X F p ≪≫
    (abelianSections X).rightDerivedObjIsoOfResolution R.ι
      (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n)) p
```

The existing public theorem `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_resolution_comparison_evaluation` lived in `Sheaf.AlgebraicGeometry.AbelianResolutionComparisonEvaluation`, which publicly imported the leaf.

## New

The same names and signatures are in `Sheaf.AlgebraicGeometry.AbelianCounitCocycleDefinitions`, publicly imported by the leaf:

```lean
abbrev abelianPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

def abelianAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    invImage f ⊣ abelianPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base

def abelianExtSectionsIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      ((abelianSections X).rightDerived p).obj
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) :=
  (Abelian.Ext.precompAddEquiv (terminalSourceIso X)
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p

def abelianInjectiveResolutionIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
  abelianExtSectionsIso X F p ≪≫ R.isoRightDerivedObj (abelianSections X) p
```

`abelianInjectiveResolutionIso_eq_acyclic` proves equality with the old constructor by `CategoryTheory.acyclic_comparison_of_injective`. The source evaluation theorem has the exact old signature and visibility; its only mathematical proof change is replacing expansion of the old injective constructor with that equality. Its old module is a public re-export of the new lower module. The item uses the existing theorem directly; it does not duplicate it or add an unresolved replacement.

The computational normalization changes no mathematical object: the equality theorem is fully proved with the permitted axioms. Downstream target meanings are therefore identical, while the changed definition remains available for the required statement review.

## Users

`tools/downstream.py --uses` identified the direct declaration users. The two section-homotopy wrappers are included because they publicly consume the direct user. Holder names are from the local claim snapshot; only the unclaimed evaluation module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation | H3 | Unchanged public leaf signature; original counit constructors are publicly re-exported. Complete proof added. |
| Sheaf.AlgebraicGeometry.AbelianResolutionComparisonEvaluation | unclaimed | Its existing proved declaration moves to AbelianCounitCocycleDefinitions with identical signature and visibility; this module publicly re-exports it. |
| Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation | unclaimed | No source adaptation needed: original declaration names, signatures and constructor meanings are preserved by public re-exports and the proved constructor equality. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCoreParts | unclaimed | No source adaptation needed: original declaration names, signatures and constructor meanings are preserved by public re-exports and the proved constructor equality. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCore | unclaimed | No source adaptation needed: original declaration names, signatures and constructor meanings are preserved by public re-exports and the proved constructor equality. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopies | unclaimed | No source adaptation needed: original declaration names, signatures and constructor meanings are preserved by public re-exports and the proved constructor equality. |

No other group’s module is adapted. `Challenge.lean` and the blueprint unit records are unchanged. The old evaluation node’s `lean` attachment follows the moved declaration.

## Status

landed 20261014T223541-L-4125412 2026-10-14 (merge of deliver/H3/Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation)
