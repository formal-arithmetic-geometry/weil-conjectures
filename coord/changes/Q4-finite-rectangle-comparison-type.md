# fourCornerPullback and the four-corner comparison interfaces

## Reason

The inferred types retain expanded derived-category and functor-composition metadata.
Checking the concrete mate equations then unfolds large localization choices. Give
all four existing functor aliases explicit raw DerivedCategory types, matching
adicDatumReduction exactly, and expose the
two existing geometric adjunctions with those types, and type the existing reduction
comparison using adicDatumReduction. Local instance preferences select the shared
adicDatumModulesAbelian data and proEtaleRingModules_hasDerivedCategory. These are
existing constructions; no new choice, mathematical assumption, or hole is added.
The data bodies of the four functors and the selected unique comparison are unchanged.
The four aliases become ordinary definitions, so they need not eagerly unfold.
The two new adjunction definitions have the existing geometric adjunction as value.
Using fourCornerDerived in these four interfaces while reduction used raw
DerivedCategory produced different hidden parameters in Functor.obj applications.
The same reduced object then required unfolding the whole chosen functor to compare.
All interfaces now use the same raw category spelling, removing that reduction.
No global instance or attribute is changed. Signatures remain definitionally equal;
target statements retain their meaning, subject to the independent definition review.

## Old

```lean
abbrev fourCornerPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :=
  proEtaleRingDerivedPullback f (adicDatumRing V d)
    (adicDatumRing U d) (fourCornerCoefficientIso f d)
```

```lean
abbrev fourCornerPushforward {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :=
  proEtaleRingDerivedDirectImage f (adicDatumRing V d)
    (adicDatumRing U d) (fourCornerCoefficientIso f d)
```

```lean
abbrev fourCornerFinitePullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  proEtaleRingDerivedPullback f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
```

```lean
abbrev fourCornerFinitePushforward {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  proEtaleRingDerivedDirectImage f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
```

```lean
def fourCornerReductionPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  (fourCornerReductionPullback_exists f d n).exists.choose
```

## New

```lean
def fourCornerPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :
    DerivedCategory (proEtaleRingModules V (adicDatumRing V d)) ⥤ DerivedCategory
      (proEtaleRingModules U (adicDatumRing U d)) :=
  proEtaleRingDerivedPullback f (adicDatumRing V d)
    (adicDatumRing U d) (fourCornerCoefficientIso f d)
```

```lean
def fourCornerPushforward {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :
    DerivedCategory (proEtaleRingModules U (adicDatumRing U d)) ⥤ DerivedCategory
      (proEtaleRingModules V (adicDatumRing V d)) :=
  proEtaleRingDerivedDirectImage f (adicDatumRing V d)
    (adicDatumRing U d) (fourCornerCoefficientIso f d)
```

```lean
def fourCornerFinitePullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (proEtaleRingModules V ((adicLisseRingSystem V d.ideal).obj (op n))) ⥤
      DerivedCategory (proEtaleRingModules U ((adicLisseRingSystem U d.ideal).obj (op n))) :=
  proEtaleRingDerivedPullback f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
```

```lean
def fourCornerFinitePushforward {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (proEtaleRingModules U ((adicLisseRingSystem U d.ideal).obj (op n))) ⥤
      DerivedCategory (proEtaleRingModules V ((adicLisseRingSystem V d.ideal).obj (op n))) :=
  proEtaleRingDerivedDirectImage f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
```

```lean
def fourCornerDerivedAdjunction {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :
    fourCornerPullback f d ⊣ fourCornerPushforward f d :=
  proEtaleRingDerivedAdjunction f (adicDatumRing V d) (adicDatumRing U d)
    (fourCornerCoefficientIso f d)
```

```lean
def fourCornerFiniteDerivedAdjunction {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourCornerFinitePullback f d n ⊣ fourCornerFinitePushforward f d n :=
  proEtaleRingDerivedAdjunction f
    ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
```

```lean
def fourCornerReductionPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourCornerPullback f d ⋙ adicDatumReduction U d n ≅
      adicDatumReduction V d n ⋙ fourCornerFinitePullback f d n :=
  (fourCornerReductionPullback_exists f d n).exists.choose
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Explicit functor/comparison interfaces, unchanged data; two typed adjunction aliases. |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Uses the same functors and comparison; selects the same local category data. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | Uses the fixed interfaces for the mate calculation. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | new, Q4 | Uses the fixed interfaces in the pullback cube. |

The downstream.py --uses scan for fourCornerReductionPullback lists only the first
two existing modules. ProperBaseChangeFourArrows is the sole direct importer of
ProperBaseChangeFourCorners. No module held by another group is edited.

## Status

landed 20261020T233213-L-905022 2026-10-20 (merge of deliver/Q4/Sheaf.Paper.FiniteLevelRectangle)
