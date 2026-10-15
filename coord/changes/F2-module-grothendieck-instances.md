# CategoryTheory.Mod.monoidalClosed and CategoryTheory.Mod.hasFunctorialFlatResolution

## Reason

Replace the two original missing proofs with complete constructions. The interface scanner regards
changed instance bodies and the additional `open MonObj` command as interface changes, so this record
includes all downstream modules. Every existing signature, universe and public import is unchanged.
No target declaration or definition of a module object or relative tensor is changed.
The only new public theorem is `CategoryTheory.Mod.relativeTensor_isLeftAdjoint`.
The closed instance chooses a right adjoint of an actually proved left adjoint, uniquely determined
up to natural isomorphism; the flat-resolution instance builds its functor explicitly from the given
ambient resolution. No data comes from a missing proof. The original flat-resolution assumption is a
Prop-valued existence of supplied resolution data, not an unproved existence theorem.

## Old

```lean
open CategoryTheory MonoidalCategory Limits

noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  sorry

instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry
```

## New

```lean
open CategoryTheory MonoidalCategory Limits MonObj

noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) where
  closed M := by
    have := relativeTensor_isLeftAdjoint M
    exact ⟨_, Adjunction.ofIsLeftAdjoint _⟩

instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) := by
  classical
  obtain ⟨Λ⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution C)
  have : (free R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (freeForgetAdjunction R)
  refine ⟨{
    F := ObjectProperty.lift _
      (forget R ⋙ Λ.F ⋙ ObjectProperty.flat.ι ⋙ free R)
      (fun M ↦ flat_free (Λ.F.obj M.X).property)
    π := {
      app M := (free R).map (Λ.π.app M.X) ≫ (freeForgetAdjunction R).counit.app M
      naturality M N f := by
        change (free R).map (ObjectProperty.flat.ι.map (Λ.F.map f.hom)) ≫
          (free R).map (Λ.π.app N.X) ≫ (freeForgetAdjunction R).counit.app N =
          ((free R).map (Λ.π.app M.X) ≫ (freeForgetAdjunction R).counit.app M) ≫ f
        rw [← Functor.map_comp_assoc, Λ.π_naturality, Functor.map_comp,
          Category.assoc, Category.assoc]
        exact congrArg (fun k ↦ (free R).map (Λ.π.app M.X) ≫ k)
          ((freeForgetAdjunction R).counit.naturality f)
    }
    epi_π_app M := by
      change Epi ((free R).map (Λ.π.app M.X) ≫ (freeForgetAdjunction R).counit.app M)
      have : Epi (Λ.π.app M.X) := Λ.epi_π_app M.X
      have : Epi ((free R).map (Λ.π.app M.X)) := (free R).map_epi _
      have : Epi ((freeForgetAdjunction R).counit.app M) := by infer_instance
      infer_instance }⟩
```

The added proof import is private:
`WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular`.
The helper theorem and all explicitly constructed comparison isomorphisms are in the item module.
Existing module/declaration docstrings are preserved.

## Users

All 52 transitive downstream modules from `tools/downstream.py --names` are listed below;
`--uses monoidalClosed` and `--uses hasFunctorialFlatResolution` find no textual uses outside the
item itself. Consumers infer these instances implicitly. The mathematical properties and abstract
instance signatures are identical, and no target statement changes meaning. The new data instance
body should be included in the routine target-definition review, although its canonical right
adjoints differ only by natural isomorphism. No consumer requires a forced adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse` | B2 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover` | C3 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover` | B3 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` | C2 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` | C3 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover` | C4 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.AdicCompletionReduction` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CompletionMap` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedPointBasisEvaluation` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | C1 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQcqsPushforwardContinuity` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.GeometricFieldProEtaleEvaluation` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicKoszulCompletion` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.KoszulQuotientLimit` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Paper.ProfinitePointPullback` | B4 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.RingTheory.BoundedWContractibleExtension` | D3 | Existing signatures and public imports unchanged; no adaptation. |
| `Sheaf.Topology.BoundedExtremallyDisconnectedCover` | F4 | Existing signatures and public imports unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` | F2 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` | B4 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | A2 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | E4 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | A2 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | E4 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | F3 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | F3 | Existing signatures and public imports unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` | unclaimed | Existing signatures and public imports unchanged; no adaptation. |

## Status

landed 20261015T154210-L-164098 2026-10-15 (merge of deliver/F2/WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian)
