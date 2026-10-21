# AlgebraicGeometry.ProEtale.constructibleComparisonRingMap, constructibleComparisonPullback, constructibleComparisonComplexPullback

## Reason

Move the three canonical constructions into `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`,
publicly imported by the original module. Lower proof modules need the constructions without
importing the theorem they prove. All qualified names, universes, binders and definition bodies
are preserved verbatim. No mathematical definition or target meaning changes. No source-library
module is edited. The moved declarations retain a Lean attachment in the new data node.
The original theorem statement is unchanged.

## Old

In `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`:

```lean
def constructibleComparisonRingMap (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    siteModuleRings (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⟶
    ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
      RingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj
        (siteModuleRings (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  (sheafCompose (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).map
    (((sheafificationAdjunction (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      CommRingCat.{max v (u + 1)}).homEquiv
        ((Functor.const (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ).obj
          (CommRingCat.of A))
        ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          CommRingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) |>.obj
            (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X)
              A))).symm
        (Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
          (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
            ((Functor.const _).obj (CommRingCat.of A)))))

abbrev constructibleComparisonPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  SheafOfModules.pullback.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X) (constructibleComparisonRingMap X A)

def constructibleComparisonComplexPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  @Functor.mapHomologicalComplex ℤ _ _ _ _ _ _ (constructibleComparisonPullback X A)
    (@Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
      (SheafOfModules.pullbackPushforwardAdjunction
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap X A)).isLeftAdjoint) (.up ℤ)
```

## New

Exactly the same declarations and bodies, now in
`Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`:

```lean
def constructibleComparisonRingMap (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    siteModuleRings (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⟶
    ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
      RingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj
        (siteModuleRings (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  (sheafCompose (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).map
    (((sheafificationAdjunction (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      CommRingCat.{max v (u + 1)}).homEquiv
        ((Functor.const (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ).obj
          (CommRingCat.of A))
        ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          CommRingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) |>.obj
            (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X)
              A))).symm
        (Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
          (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
            ((Functor.const _).obj (CommRingCat.of A)))))

abbrev constructibleComparisonPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  SheafOfModules.pullback.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X) (constructibleComparisonRingMap X A)

def constructibleComparisonComplexPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  @Functor.mapHomologicalComplex ℤ _ _ _ _ _ _ (constructibleComparisonPullback X A)
    (@Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
      (SheafOfModules.pullbackPushforwardAdjunction
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap X A)).isLeftAdjoint) (.up ℤ)
```

The original module has `public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`.
This preserves access through every original import path.

## Users

The three original `tools/downstream.py --uses` searches and the refreshed combined search found these users.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact | unclaimed at inspection | Same names and bodies through the original public import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonFlatPullback | unclaimed at inspection | Same names and bodies through the original public import; no adaptation. |

| Sheaf.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection | unclaimed at inspection | New downstream user found by preflight; compiles unchanged in 16.8 s. Same names and bodies; no adaptation. |

| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | unclaimed at inspection | Refreshed downstream user; compiles unchanged in 7.9 s with the same canonical constructions and theorem statement. No adaptation. |

The first two unchanged consumer sources compile against the sandbox module (14.2 s for
ModuleExact, 10.6 s for FlatPullback), without adaptation.
New proof modules import the data directly. The moved definitions are not changed semantically,
so no target statement or definition review is reopened for a different mathematical meaning;
the independent reader can compare the three bodies verbatim.

## Status

landed 20261021T012347-L-2179661 2026-10-21 (merge of deliver/B2/Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison)
