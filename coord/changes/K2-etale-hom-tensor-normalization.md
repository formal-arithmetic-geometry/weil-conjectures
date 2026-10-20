# AlgebraicGeometry.Etale.EtaleHomTensorModelNormalization

## Reason

Specialize the named generic cochain normalization predicate instead of expanding
its equation separately in the sheaf presentation. Repeated comparison of the
preadditive and zero-morphism instances inside the expanded equation exhausted
the kernel limit. The named predicate lets specialization retain the same equation
without rechecking that presentation conversion inside the whole uniqueness result.
The site bridge compiles in 7.2 seconds after this change.

The generic predicate has exactly the original flat-term K-flat hypotheses, ordinary
adjoint-mate oplax tensorator, and counit equation. Its explicit cochain tensor
bifunctor is definitionally the original `P ⊗ Q`. No mathematical condition changes.
Its module `Sheaf.CategoryTheory.DerivedTensorRightExact` is a public import because
the public definition now uses that predicate. The original module publicly
reexports `EtaleHomComparisonModels` as recorded in the interface relocation record.

## Old

```lean
def EtaleHomTensorModelNormalization
    (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D) [E.Additive] [E.IsLeftAdjoint]
    [E.OplaxMonoidal]
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
      F.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : ∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      ((derivedTensor D X).obj (F.obj K)).obj (F.obj L) ≅
        F.obj (((derivedTensor C X).obj K).obj L)) : Prop :=
  ∀ P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology C) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology C) (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) → (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
    F.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) ≫ r (P ⊗ Q) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app P).app Q) =
      (μ (_root_.DerivedCategory.Q.obj P) (_root_.DerivedCategory.Q.obj Q)).inv ≫
        (r P ⊗ₘ r Q) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((E.mapHomologicalComplex (.up ℤ)).obj P)
          ((E.mapHomologicalComplex (.up ℤ)).obj Q)
```

## New

```lean
def EtaleHomTensorModelNormalization
    (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D) [E.Additive] [E.IsLeftAdjoint]
    [E.OplaxMonoidal]
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
      F.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : ∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      ((derivedTensor D X).obj (F.obj K)).obj (F.obj L) ≅
        F.obj (((derivedTensor C X).obj K).obj L)) : Prop :=
  Functor.rightExactTensorModelNormalization E F r μ
```

Unfolding `CategoryTheory.Functor.rightExactTensorModelNormalization` gives the old
equation, with `((curriedTensor (CochainComplex _ ℤ)).obj P).obj Q` in place of the
definitionally identical `P ⊗ Q`. The universes, category assumptions, quantifiers,
K-flatness and flat-term hypotheses are unchanged. In particular, the chosen
ordinary tensorator and the chosen scalar-extension representative remain fixed.
The generic equation is verified by `rfl` in a temporary abstract-category check.
A direct expanded comparison after sheaf specialization reaches the same conversion
timeout that motivated this interface; the named specialization and all five direct
consumers compile.
This definition is used by the targets; its meaning is preserved and is submitted
for the required independent review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.EtaleHomThickLocus | K2 | Publicly reexports the definition and proves the original theorem using it. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | new K2 module | Owns the relocated predicate and its canonical comparison. |
| Sheaf.SixFunctors.EtaleHomTransposeExact | new K2 module | Uses the identical canonical tensor comparison. |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed in inspected claim records | Uses the public canonical comparison; no edit required. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed in inspected claim records; source authored by Q74 | Uses `etaleHomTensorComparison`; public reexport preserves it, no edit required. |

The shared-source search finds no external direct occurrence of this predicate;
its only direct source consumer is `IsEtaleHomTensorCanonical` in the original
item, now relocated with it. Other public consumers are covered by the interface
relocation record and its consumer checks. No upstream module or target is edited.

## Status

landed 20261020T230801-L-612184 2026-10-20 (merge of deliver/K2/Sheaf.SixFunctors.EtaleHomThickLocus)
