# Completed ordinary comparison declarations

## Reason
The completed coherence proof uses the ordinary coefficient identities from a proof-only
module. They were moved unchanged from the item module so the ordinary exchange coherence
split can be imported without an import cycle.

## Old

Declared in `Sheaf.Paper.CompletedExchangeCoherence`:

```lean
theorem AdicCoefficientDatum.integralRingIso_comp {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    d.integralRingIso (h ≫ g) = proEtaleRingCompositeCoefficients h g
      (d.completedRing W) (d.completedRing V) (d.completedRing U)
      (d.integralRingIso g) (d.integralRingIso h)

def AdicCoefficientDatum.pullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.pull (h ≫ g) ≅ d.pull g ⋙ d.pull h :=
  eqToIso (congrArg
    (proEtaleRingDerivedPullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    proEtaleCanonicalDerivedPullbackComparison h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

def AdicCoefficientDatum.pushComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.push h ⋙ d.push g ≅ d.push (h ≫ g) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction g (d.completedRing W) (d.completedRing V)
      (d.integralRingIso g)).comp
      (proEtaleRingDerivedAdjunction h (d.completedRing V) (d.completedRing U)
        (d.integralRingIso h)))
    (proEtaleRingDerivedAdjunction (h ≫ g) (d.completedRing W) (d.completedRing U)
      (d.integralRingIso (h ≫ g))) (d.pullComp h g)

theorem AdicCoefficientDatum.modulePushId_existsUnique (T : Scheme.{t}) :
    ∃! α : proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T) (d.completedRing T)
        (d.integralRingIso (𝟙 T)) ≅ 𝟭 _,
      ∀ (N : reductionModules T (d.completedRing T)) (U : T.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T)
          (d.completedRing T) (d.integralRingIso (𝟙 T))).obj N).val.obj (op U)),
        (α.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app U).op m

def AdicCoefficientDatum.modulePushId (T : Scheme.{t}) :=
  (d.modulePushId_existsUnique T).choose

def AdicCoefficientDatum.pullId (T : Scheme.{t}) : d.pull (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)) ≪≫
    Functor.mapDerivedCategoryIdIso _

def AdicCoefficientDatum.pushId (T : Scheme.{t}) : d.push (𝟙 T) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleRingDerivedAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))) (d.pullId T)).symm
```

## New

The same signatures and definition bodies, now in `Sheaf.Paper.CompletedOrdinaryComparisons`:

```lean
theorem AdicCoefficientDatum.integralRingIso_comp {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    d.integralRingIso (h ≫ g) = proEtaleRingCompositeCoefficients h g
      (d.completedRing W) (d.completedRing V) (d.completedRing U)
      (d.integralRingIso g) (d.integralRingIso h)

def AdicCoefficientDatum.pullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.pull (h ≫ g) ≅ d.pull g ⋙ d.pull h :=
  eqToIso (congrArg
    (proEtaleRingDerivedPullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    proEtaleCanonicalDerivedPullbackComparison h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

def AdicCoefficientDatum.pushComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.push h ⋙ d.push g ≅ d.push (h ≫ g) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction g (d.completedRing W) (d.completedRing V)
      (d.integralRingIso g)).comp
      (proEtaleRingDerivedAdjunction h (d.completedRing V) (d.completedRing U)
        (d.integralRingIso h)))
    (proEtaleRingDerivedAdjunction (h ≫ g) (d.completedRing W) (d.completedRing U)
      (d.integralRingIso (h ≫ g))) (d.pullComp h g)

theorem AdicCoefficientDatum.modulePushId_existsUnique (T : Scheme.{t}) :
    ∃! α : proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T) (d.completedRing T)
        (d.integralRingIso (𝟙 T)) ≅ 𝟭 _,
      ∀ (N : reductionModules T (d.completedRing T)) (U : T.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T)
          (d.completedRing T) (d.integralRingIso (𝟙 T))).obj N).val.obj (op U)),
        (α.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app U).op m

def AdicCoefficientDatum.modulePushId (T : Scheme.{t}) :=
  (d.modulePushId_existsUnique T).choose

def AdicCoefficientDatum.pullId (T : Scheme.{t}) : d.pull (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)) ≪≫
    Functor.mapDerivedCategoryIdIso _

def AdicCoefficientDatum.pushId (T : Scheme.{t}) : d.push (𝟙 T) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleRingDerivedAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))) (d.pullId T)).symm
```

The item publicly reexports this module, so every existing importing module sees the
same declaration names, visibility, signatures and bodies. Proofs of the two formerly
holed comparison theorems are filled. The targets keep their statements and meanings.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedExchangeCoherence | S9 | imports the relocated declarations |
| Sheaf.Paper.CompleteCompactSupportProetale | J3 | uses `pullComp`, `pushComp`, `pushId`; signatures unchanged |
| Sheaf.Paper.CondensedERealization | C4 | uses `pullId`; signature unchanged |
| Sheaf.Paper.ExchangeFunctoriality | D6 | uses `pushComp`; signature unchanged |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | uses `pullComp`; signature unchanged |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | D6 | uses `pullComp`; signature unchanged |

## Status
landed 20261021T165936-L-2309985 2026-10-21 (merge of deliver/S9/Sheaf.Paper.CompletedExchangeCoherence)
