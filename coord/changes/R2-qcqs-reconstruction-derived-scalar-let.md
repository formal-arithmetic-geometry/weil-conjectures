# AlgebraicGeometry.ProEtale.LatticeTree.Reconstruction

## Reason

Elaborating total left derived scalar extension at a concrete pulled-back coefficient ring
repeatedly compares large monoidal and flat-resolution instances. The generic library uses
an abstract-ring `derivedScalar` abbreviation for this purpose. Introduce the same local
`let` inside this definition, elaborating its instances while the two rings are abstract.
Substitution and beta reduction give exactly the previous expression. No hypothesis,
conclusion, functor, ring object, scalar map, or coefficient-family index changes. This is a
representation repair for the 60-second compile bottleneck, not a statement weakening.

## Old

```lean
def Reconstruction
    (ℓ : ℕ) [Fact ℓ.Prime] (I : Type) (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (a : ∀ k : I, Profinite.padicIntegersRingObj.{u} ℓ (F k).1 ⟶ R)
    [∀ k : I, IsMonHom (a k)] : Prop :=
  ∀ (X : Scheme.{u}) (t : QcqsOpenClosedTree X),
    (∀ (W : Scheme.{u}) (_p : t.Path W) (k : I),
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a k) W))) →
    (∀ (W : Scheme.{u}) (p : t.Path W),
      PreservesModelsAndFlat R p ∧
      ∀ k : I, PreservesModelsAndFlat (Profinite.padicIntegersRingObj ℓ (F k).1) p ∧
        PreservesModelsAndFlat (Profinite.continuousMapRingObj (F k).1) p ∧
        ∀ B : Modules (Profinite.padicIntegersRingObj ℓ (F k).1) W,
          IsIso ((scalarComparison (a k) p).app B)) ∧
    ∀ (M : Modules R X) (d : LeafModels ℓ I F R a t M),
      (∀ w : Leaf t,
        constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ (F (d.fieldIndex w)).1) X
          (single _ X (branchModel d w)) ∧
        DerivedCategory.finiteTorAmplitude _ (single _ X (branchModel d w)) ∧
        DerivedCategory.torAmplitudeIn _ 0 0 (single _ X (branchModel d w)) ∧
        Nonempty
          ((Mod.extendScalars (coefficientMap (a (d.fieldIndex w)) X)).leftDerivedFunctor.obj
              (single _ X (branchModel d w)) ≅
            single R X ((w.2.1.extension R).obj
              ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))) ∧
      ∃ n : ℕ, ObjectProperty.extensionProductIter
        (fun K : DerivedCategory (Modules R X) ↦ ∃ w : Leaf t,
          Nonempty (K ≅ single R X ((w.2.1.extension R).obj
            ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))) n (single R X M)
```

## New

```lean
def Reconstruction
    (ℓ : ℕ) [Fact ℓ.Prime] (I : Type) (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (a : ∀ k : I, Profinite.padicIntegersRingObj.{u} ℓ (F k).1 ⟶ R)
    [∀ k : I, IsMonHom (a k)] : Prop :=
  let derivedScalar {Y : Scheme.{u}}
      {A B : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}}
      [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
      (φ : A ⟶ B) [IsMonHom φ] :
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) A) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) B) :=
    (Mod.extendScalars φ).leftDerivedFunctor
  ∀ (X : Scheme.{u}) (t : QcqsOpenClosedTree X),
    (∀ (W : Scheme.{u}) (_p : t.Path W) (k : I),
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a k) W))) →
    (∀ (W : Scheme.{u}) (p : t.Path W),
      PreservesModelsAndFlat R p ∧
      ∀ k : I, PreservesModelsAndFlat (Profinite.padicIntegersRingObj ℓ (F k).1) p ∧
        PreservesModelsAndFlat (Profinite.continuousMapRingObj (F k).1) p ∧
        ∀ B : Modules (Profinite.padicIntegersRingObj ℓ (F k).1) W,
          IsIso ((scalarComparison (a k) p).app B)) ∧
    ∀ (M : Modules R X) (d : LeafModels ℓ I F R a t M),
      (∀ w : Leaf t,
        constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ (F (d.fieldIndex w)).1) X
          (single _ X (branchModel d w)) ∧
        DerivedCategory.finiteTorAmplitude _ (single _ X (branchModel d w)) ∧
        DerivedCategory.torAmplitudeIn _ 0 0 (single _ X (branchModel d w)) ∧
        Nonempty
          ((derivedScalar (coefficientMap (a (d.fieldIndex w)) X)).obj
              (single _ X (branchModel d w)) ≅
            single R X ((w.2.1.extension R).obj
              ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))) ∧
      ∃ n : ℕ, ObjectProperty.extensionProductIter
        (fun K : DerivedCategory (Modules R X) ↦ ∃ w : Leaf t,
          Nonempty (K ≅ single R X ((w.2.1.extension R).obj
            ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))) n (single R X M)
```

## Users

The table is the complete declaration-use list from
`tools/downstream.py Sheaf.Paper.QcqsLatticeTreeReconstruction --uses Reconstruction`.
The local let substitutes to the old body, so these statements are definitionally unchanged.
The target signatures stay verbatim. The independent reader should confirm their unchanged
interpretation through this definition. No consumer adaptation is made. Lean compiled a copy of the original definition and proved
`Reconstruction ℓ I F R a = OriginalReconstruction ℓ I F R a` by `rfl` (21.3 seconds).

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicExceptionalCompositorCoefficientsData | unclaimed | Same definition after local-let reduction; no adaptation. |
| Sheaf.Paper.AdicRamifiedScalarCochainNormalization | unclaimed | Same definition after local-let reduction; no adaptation. |
| Sheaf.Paper.AdicRamifiedScalarRealizationData | unclaimed | Same definition after local-let reduction; no adaptation. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | R2 | Same definition after local-let reduction; no adaptation. |

## Status

landed 20261025T043304-L-1694089 2026-10-25 (merge of deliver/R2/Sheaf.Paper.QcqsLatticeTreeReconstruction)
