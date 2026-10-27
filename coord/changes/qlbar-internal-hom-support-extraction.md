# AlgebraicGeometry.ProEtale.QlbarInternalHom: coefficient support extraction

## Reason

The complete proof profiles with repeated checking of the existing coefficient
constructions, strict formula and normalized evaluation roof. Local opacity of the
large derived tensor/Hom constructions and extraction of the proved generic colimit
assembly were tried first. The enlarged item still exceeds the 60-second per-file
limit. This is a file split after those definition-level improvements, as authorized
by the current remote-worker brief, step 3a. No limit or launcher tool is changed.

`Sheaf.Paper.QlbarInternalHomCoefficientData` contains the existing nine public
definitions and six already-proved auxiliary theorems. The original item publicly
imports this module, keeping all original names and signatures available. Its two
formerly holed comparison theorems remain in the item. Every moved public definition
is byte-identical to current source, including `HomTransportNormalized` and its
`@[no_expose]` attribute. The six auxiliary proofs are retained (the roof proof uses
explicit type annotations on its restriction equation). No mathematical hypothesis,
map, conclusion, visibility, target signature or source-library file changes.

## Old

The existing item directly defines these nine definitions, reproduced verbatim:

```lean
def evaluationComparison
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K L : DerivedCategory (Internal R X)) :
    (CondensedRing.internalScalarExtension a X).obj
        (((CondensedRing.derivedHom R X).obj (op K)).obj L) ⟶
      ((CondensedRing.derivedHom S X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))).obj
          ((CondensedRing.internalScalarExtension a X).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction S
    ((CondensedRing.internalScalarExtension a X).obj K)).homEquiv _ _
      (((CondensedRing.internalScalarTensorIso a X).inv.app K).app
          (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
        (CondensedRing.internalScalarExtension a X).map
          ((CondensedRing.derivedTensorHomAdjunction R K).counit.app L))

def scalarHomIso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Internal R X)) :
    ((CondensedRing.derivedHom S X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))) ⋙
        (Mod.comap (coefficientMap a X)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙
        (CondensedRing.derivedHom R X).obj (op K) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).comp
      (CondensedRing.derivedTensorHomAdjunction S
        ((CondensedRing.internalScalarExtension a X).obj K))).rightAdjointUniq
    (((CondensedRing.derivedTensorHomAdjunction R K).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).ofNatIsoLeft
      ((CondensedRing.internalScalarTensorIso a X).app K))

def Continuous (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X)) : Prop :=
  ∀ (P : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ),
    Nonempty (DerivedCategory.Q.obj P ≅
      (forward (Profinite.continuousMapRingObj E) X).obj K) →
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
      WeilConjectures.SfbHomFilteredColimit.Continuous.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring (Profinite.continuousMapRingObj E) X) (I := I) P

def fields (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

def coefficients (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ Modules (Profinite.continuousMapRingObj E) X :=
  coefficientComplexDiagram X ℓ
      ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
          (ComplexShape.up ℤ) 0).obj
        (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
      (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
      (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)) ⋙
    complexForward (Profinite.continuousMapRingObj E) X ⋙ HomologicalComplex.eval _ _ 0

def coefficientCocone (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Cocone (coefficients X ℓ E) :=
  (HomologicalComplex.eval _ _ 0).mapCocone
    ((complexForward (Profinite.continuousMapRingObj E) X).mapCocone
      (coefficientComplexCocone X ℓ
        ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
          (ComplexShape.up ℤ) 0).obj
          (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
        (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
        (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))))

def StrictColimitFormula
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I]
    (T : I ⥤ WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R)
    [HasColimit T] (c : Cocone T)
    (P L : CochainComplex
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R) ℤ) : Prop :=
  Nonempty (IsColimit c) ∧
  QuasiIso (colimMap (Functor.whiskerLeft T
    (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L))) ∧
  WeilConjectures.SfbHomFilteredColimit.Normalized.{u + 1, u, u} J R P L
    (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L) ∧
  QuasiIso (colimit.post
    (T ⋙ WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
      ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
  IsIso (colimit.post T
    (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
      ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L))) ∧
  (∀ i, QuasiIso
    ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
      (T.obj i))) ∧
  (∀ i, QuasiIso
    (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
      (T.obj i))) ∧
  QuasiIso
    ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app c.pt) ∧
  QuasiIso
    (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt) ∧
  (colimit.post T
      (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
        ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L)) ≫
        (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
          (colimit T) =
    colimMap (Functor.whiskerLeft T
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L)) ≫
        colimit.post T
          (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
            ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L) ⋙
              WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
  (∀ i,
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
          (c.ι.app i, 𝟙 L)) ≫
      WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt =
    WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
        (T.obj i) ≫
      (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
          (c.ι.app i, 𝟙 ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))))

def ColimitFormula (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (P L : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ) : Prop :=
  StrictColimitFormula (Scheme.ProEt.topology X)
    (ring (Profinite.continuousMapRingObj E) X) (coefficients X ℓ E)
      (coefficientCocone X ℓ E) P L

@[no_expose] def HomTransportNormalized
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (S : WeilConjectures.CoefficientClosedStructure (hom R X))
    (T : WeilConjectures.CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring R X) S)
    (t : TensorComparison R X S T)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
      ((forward R X).op.prod (forward R X)) ⋙ hom R X) : Prop :=
  -- Share the named evaluation map with `HomPresentation.evaluation`.
  ∀ K N : DerivedCategory (Internal R X),
    (forward R X).map (internalEvaluation R X K N) =
      t.iso.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj N, K) ≫
        S.tensor.map
          (X := ((forward R X).obj (((CondensedRing.derivedHom R X).obj (op K)).obj N),
            (forward R X).obj K))
          (Y := ((hom R X).obj (op ((forward R X).obj K), (forward R X).obj N),
            (forward R X).obj K))
          (θ.hom.app (op K, N), 𝟙 ((forward R X).obj K)) ≫
        S.evaluation ((forward R X).obj K) ((forward R X).obj N)
```

Its existing public imports are:

```lean
public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.DerivedInternalHomFilteredColimit
public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Final
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.QlbarTailModuleColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
```

## New

The nine definitions above occur verbatim, under the same namespace and universe
and section binders, in `Sheaf.Paper.QlbarInternalHomCoefficientData`. There is no
new definition body. The definitions' original attributes and visibility are retained.
The following public import is added to the original item, which retains every
existing public import listed above:

```lean
public import Sheaf.Paper.QlbarInternalHomCoefficientData
```

The moved proved auxiliaries retain their existing signatures:
`evaluationComparison_naturality`, `evaluationComparison_restriction`,
`fieldDiagram`, `coefficientModules`, `coefficientRingColimit`, and
`coefficient_comparison_roof`.
The coefficient-module-cocone node's Lean module/file attachment is updated to the
support module. The parent node records the re-export in its Lean note; its principal
comparison and colimit theorems remain attached to the original item. The parent
mathematical statement and all definition-node mathematical fields are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.QlbarInternalHomCoefficientComparison --uses
AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficients` lists the five downstream
modules below and finds actual uses only in the item and `QlbarBoundedTensorColimit`.
All moved declarations are publicly re-exported, with their original signatures and
bodies. Target meanings therefore remain identical. No consumer adaptation is needed.
There are no current claim rows for the five downstream modules in the shared snapshot.
The unchanged `FiniteModelTopologyComparisonMaps` and `FiniteModelTopologyDerivedHom`
compile against this packet (the latter in 34.8 seconds). The unchanged
`QlbarBoundedTensorColimit` finishes type-checking without errors but exceeds the
per-file limit (95 seconds). A separate control compile of that same unchanged
consumer against only the published baseline also exceeds the limit (88 seconds),
again without type errors. This is a pre-existing timing issue, not a forced
consumer adaptation; its source is not included in the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | P4 | Imports the data publicly and retains the two comparison proofs. |
| Sheaf.Paper.QlbarInternalHomCoefficientData | new in this packet, P4 | Contains unchanged existing data and auxiliary proofs. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Same public names, types, maps and instances. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | Same continuity predicate and comparison theorem. |
| Sheaf.Paper.GlobalInternalHomDetection | unclaimed | Same transitive definitions and statements. |
| Sheaf.Paper.QlbarBoundedTensorColimit | unclaimed | Same coefficient diagram, cocone, module identifications and finite-field tail. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Same transitive definitions and statements. |

The final item compile after redundant proof-import cleanup completes cleanly in
48.5 seconds. All three delivery modules contain zero `sorry`s and no profiling
options. The independent delivery preflight checks the complete packet.

## Status

landed 20261026T070455-L-3593981 2026-10-26 (merge of deliver/P4/Sheaf.Paper.QlbarInternalHomCoefficientComparison)
