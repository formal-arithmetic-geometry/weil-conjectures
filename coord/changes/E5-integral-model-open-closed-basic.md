# Integral-model open/closed constructions

## Reason

Move four definitions verbatim from `Sheaf.Paper.IntegralModelOpenClosedPieces` to
`Sheaf.Paper.IntegralModelOpenClosedBasic`, publicly imported by the original module.
The supporting geometric and scalar-change lemmas need these definitions; keeping
them beside their consumer theorem would create a proof-import cycle. No body,
namespace, signature, universe, attribute or mathematical meaning changes.
The original theorem signature is unchanged. No target meaning is changed.

## Old

In `Sheaf.Paper.IntegralModelOpenClosedPieces`:

```lean
def openSliceModules {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing U.left T) ⥤
      SheafOfModules.{u + 1} ((latticeModuleRing X T).over U) := by
  letI := Scheme.ProEt.sliceDense X U
  letI : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  exact SheafOfModules.pushforward (F := (Scheme.ProEt.sliceEquiv X U).functor)
    (J := (Scheme.ProEt.topology X).over U) (K := Scheme.ProEt.topology U.left)
    (S := (latticeModuleRing X T).over U) (R := latticeModuleRing U.left T)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩

/-- Direct image with the continuous coefficient action. First restrict scalars along
the canonical coefficient inverse-image map, then apply the published ringed direct
image. Its action is through the adjoint continuous-function pullback map.
Source: Stacks Project, Tags 09AA and 03D6; Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def continuousModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing X T) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing Y T) :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousCoefficientInverseImageMap f T)) ⋙
    Scheme.proEtaleRingedDirectImage f (latticeCoefficientSheaf Y T)

/-- Extension by zero with continuous coefficients: use the concrete slice-site
transport, followed by the published direct-sum presheaf extension and sheafification.
Source: Stacks Project, Tags 03DI and 09BN
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def continuousModuleExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :=
  openSliceModules U T ⋙ Scheme.proEtaleRingedExtensionByZero U (latticeCoefficientSheaf X T)

/-- Ordinary rationalization `E_X ⊗_{A_X} M`, as the published sheafified
sectionwise change of rings along the continuous integral inclusion.
Source: Bhatt--Scholze, Lemma 6.8.13; Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def integralModelRationalize (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (M : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E) M
```

## New

The same declarations, verbatim, in `Sheaf.Paper.IntegralModelOpenClosedBasic`:

```lean
def openSliceModules {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing U.left T) ⥤
      SheafOfModules.{u + 1} ((latticeModuleRing X T).over U) := by
  letI := Scheme.ProEt.sliceDense X U
  letI : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  exact SheafOfModules.pushforward (F := (Scheme.ProEt.sliceEquiv X U).functor)
    (J := (Scheme.ProEt.topology X).over U) (K := Scheme.ProEt.topology U.left)
    (S := (latticeModuleRing X T).over U) (R := latticeModuleRing U.left T)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩

/-- Direct image with the continuous coefficient action. First restrict scalars along
the canonical coefficient inverse-image map, then apply the published ringed direct
image. Its action is through the adjoint continuous-function pullback map.
Source: Stacks Project, Tags 09AA and 03D6; Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def continuousModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing X T) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing Y T) :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousCoefficientInverseImageMap f T)) ⋙
    Scheme.proEtaleRingedDirectImage f (latticeCoefficientSheaf Y T)

/-- Extension by zero with continuous coefficients: use the concrete slice-site
transport, followed by the published direct-sum presheaf extension and sheafification.
Source: Stacks Project, Tags 03DI and 09BN
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def continuousModuleExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :=
  openSliceModules U T ⋙ Scheme.proEtaleRingedExtensionByZero U (latticeCoefficientSheaf X T)

/-- Ordinary rationalization `E_X ⊗_{A_X} M`, as the published sheafified
sectionwise change of rings along the continuous integral inclusion.
Source: Bhatt--Scholze, Lemma 6.8.13; Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def integralModelRationalize (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (M : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E) M
```

The original module publicly imports the basic module, so all public names remain
available to every original consumer.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralModelOpenClosedPieces | E5 | Publicly imports the moved definitions; theorem signature unchanged. |
| Sheaf.Paper.RationalStratumIntegralModels | unclaimed | Its public import of the item still exposes all four unchanged definitions; no adaptation. |

The refreshed `tools/downstream.py --uses` scan and server preflight identify
`RationalStratumIntegralModels` as a consumer of the supported functors and
rationalization, in addition to the item itself. There is no current claim file
for that consumer. Its `piece`, `generator` and `tensorSection` definitions retain
the same bodies and types because the original module publicly reexports the
unchanged declarations. No existing consumer requires adaptation. The unfinished parent DAG route through
`lem-weil-pbc-lisse-e-constructible-integral-lattice` is retained.

## Status

landed 20261021T154019-L-2756307 2026-10-21 (merge of deliver/E5/Sheaf.Paper.IntegralModelOpenClosedPieces)
