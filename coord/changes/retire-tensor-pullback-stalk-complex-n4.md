# CochainComplex.exists_tensorPullback_stalk_complex_iso

## Reason

The queue lists Sheaf.Algebra.Homology.TensorPullbackStalkComplex as a retirement item.
The adopted upstream twin already constructs the ring homomorphism and the complex
isomorphism separately. The Sheaf existential wrapper is redundant. Retire it and use
those upstream definitions at its only call site. No upstream file is changed.

## Old

```lean
theorem exists_tensorPullback_stalk_complex_iso
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
    (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf)
    (K : CochainComplex (RingedSpace.Modules Y) ℤ)
    (P : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : ∀ i : ℤ, P.X i ≅
      SheafOfModules.changeOfRings.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i)))
    (he : ∀ i j : ℤ, P.d i j ≫ (e j).hom =
      (e i).hom ≫ SheafOfModules.changeOfRingsHom.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i))
        (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf (K.X i) (K.d i j)))
    (x : X) :
    ∃ ρ : Y.presheaf.stalk (f x) →+* X.presheaf.stalk x,
      Nonempty
        ((((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj
          (((RingedSpace.moduleStalkFunctor Y (f x)).mapHomologicalComplex (.up ℤ)).obj K)) ≅
        (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)).obj P))
```

The old caller imported `Sheaf.Algebra.Homology.TensorPullbackStalkComplex` and wrote:

```lean
  obtain ⟨ρ, ⟨e⟩⟩ := exists_tensorPullback_stalk_complex_iso RX RY f
    (tensorPullbackRingMap f OX OY φ) K (tensorPullbackComplex f OX OY φ K)
    (fun i ↦ Iso.refl _)
    (by
      intro i j
      exact (Category.comp_id _).trans (Category.id_comp _).symm) x
```

## New

Withdraw the Sheaf module and attach its existing node to the unchanged upstream
`CochainComplex.tensorPullbackStalkComplexIso`. Its fully parameterized type is:

```lean
def tensorPullbackStalkComplexIso
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
    (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf)
    (K : CochainComplex (RingedSpace.Modules Y) ℤ)
    (P : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : ∀ i : ℤ, P.X i ≅
      SheafOfModules.changeOfRings.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i)))
    (he : ∀ i j : ℤ, P.d i j ≫ (e j).hom =
      (e i).hom ≫ SheafOfModules.changeOfRingsHom.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i))
        (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf (K.X i) (K.d i j)))
    (x : X) :
    ((ModuleCat.extendScalars
        (RingedSpace.tensorPullbackStalkRingHom X Y f α x)).mapHomologicalComplex (.up ℤ)).obj
      (((RingedSpace.moduleStalkFunctor Y (f x)).mapHomologicalComplex (.up ℤ)).obj K) ≅
    ((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)).obj P
```

The caller imports the upstream module privately and uses:

```lean
  let ρ := AlgebraicGeometry.RingedSpace.tensorPullbackStalkRingHom RX RY f
    (tensorPullbackRingMap f OX OY φ) x
  let e := tensorPullbackStalkComplexIso RX RY f
    (tensorPullbackRingMap f OX OY φ) K (tensorPullbackComplex f OX OY φ K)
    (fun i ↦ Iso.refl _)
    (by
      intro i j
      exact (Category.comp_id _).trans (Category.id_comp _).symm) x
```

The original existential follows by pairing the upstream ring map and isomorphism;
the exact original signature was checked in a compiling scratch theorem. The ring
map is precisely the composition used by the old proof. The upstream isomorphism
assembles the same component isomorphisms and differential squares. Empty spaces,
zero rings and arbitrary unbounded complexes keep exactly the same hypotheses.
No target statement or definition used by a target changes.

## Users

`tools/downstream.py --uses CochainComplex.exists_tensorPullback_stalk_complex_iso`
finds only the withdrawn declaration and `Sheaf.Algebra.Homology.KFlatPullback`.
The former module is held by N4 and withdrawn. All transitive downstream modules
reported by the same command are listed below; claim holders were read on 2026-10-20.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatPullback | P5 | Forced proof-only adaptation: replace the import and obtain the ring map and isomorphism from the upstream definitions; every declaration signature stays identical. |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedHomPushforwardKFlatModel | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackComposition | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackRecordedComposition | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedRepresentativeData | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensor | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomCochainCounit | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomTransport | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTailAbstract | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageSchemeIso | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfExtPushforwardHomology | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionCore | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |
| Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization | unclaimed | No direct use of the withdrawn theorem; unchanged signatures and proofs; no adaptation. |

With the item replaced by an empty module, the original KFlatPullback fails at
line 214 with `Unknown identifier exists_tensorPullback_stalk_complex_iso`, followed
by the dependent `rcases` failure. The adapted file compiles. Only its private import
and the local bindings for `ρ` and `e` change. It is held by P5, so this is the forced
adaptation exception; the independent reader must verify these lines.

## Status

landed 20261020T135418-L-1820678 2026-10-20 (merge of deliver/N4/Sheaf.Algebra.Homology.TensorPullbackStalkComplex)
