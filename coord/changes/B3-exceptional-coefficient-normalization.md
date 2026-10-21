# AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalization

## Reason

The old raw-derived-tensor specialization causes the kernel to expand nested sheafification
and derived-monoidal proof arguments when comparing it to the site's `derivedTensor`.
The direct reflexive site transport exceeds 60 seconds. This is the same nested-proof
abstraction issue documented in WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs.
The repair places the unchanged equation behind a generic small-etale specialization,
whose argument type shares the site's derivedTensor constants. The full restored module
then compiles in 45.1 seconds with all three normalization holes closed.

The new wrapper body is exactly `TensorNormalizationAux F S r δ`. Both old and new
specializations require its equation on every cochain pair, without flatness restrictions.
The ModuleCat symmetric structure inherits its existing braiding. No mathematical datum,
hypothesis, normalization, or target statement changes. A target using this definition
indirectly should receive the normal definition review; no semantic weakening is intended.

## Old

```lean
abbrev TensorNormalization (T : Scheme.{u}) :=
  TensorNormalizationAux (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)
```

## New

```lean
def SiteTensorNormalizationAux
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T)) : Prop :=
  TensorNormalizationAux F S r δ

/-- Small-etale specialization of the shared all-complex tensor normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev TensorNormalization (T : Scheme.{u}) :=
  SiteTensorNormalizationAux (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) T
    (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)
```

## Users

`tools/downstream.py Sheaf.Paper.ExceptionalCoefficientComparison --allow-missing --uses
TensorNormalization tensorIso_existsUnique siteTensorIso_existsUnique tensorIso` reports
zero current importers. The module is restored from its rework quarantine, not withdrawn.
The quarantined sources were also searched explicitly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalCoefficientComparison | B3 | Same all-complex predicate, now through the generic wrapper; tensor uniqueness and site transport proved. Public tensorIso, unitIso and all main theorem statements retained. |
| Sheaf.Paper.EtaleCompactScalarCoherence | quarantined | Uses tensorIso_existsUnique.choose in the unit law. Its tensor/unit-law type was checked against the repaired interface in a separate compile probe. No adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | quarantined | Uses the unchanged generic TensorNormalizationAux, not the specialization. No adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | quarantined | Uses the unchanged generic TensorNormalizationAux; ordinary-etale branch uses tensorIso with its unchanged site type. No adaptation. |

## Status

landed 20261021T020055-L-2581770 2026-10-21 (merge of deliver/B3/Sheaf.Paper.ExceptionalCoefficientComparison)
