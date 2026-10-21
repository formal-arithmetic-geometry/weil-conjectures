# AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison

## Reason

Restore the module assigned by coord/rework.tsv from its quarantine archive, preserving its
mathematical interface and the DAG attachment. The archive's theorem has zero holes, but its
historical dependencies have been adopted upstream. The unmodified archive was compiled against the current build and fails at line 142:
`Unknown identifier counit_isIso_kFlat`. Its imported historical counit module is now empty.
Redeclaring the theorem also conflicts with users that load the source counterpart. Both roots
already contain the same complete cancellation proof. Use the existing source implementation
as the only declaration provider and keep the historical path as a public re-export.

The archived private import Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit is now an empty
withdrawn module. The source implementation imports the actual source counit helper instead.
No adopted source file is changed. This is a zero-hole module-environment repair, not a new proof
or a withdrawal of the mathematical result. The quarantine archive is not edited or deleted.

## Old

Archived module: quarantine/Sheaf/AlgebraicGeometry/SingleComplexOpenTermwiseComparison.lean.
Its local public theorem has this signature, verbatim:

```lean
theorem exists_singleComplexOpen_termwise_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let a : DerivedCategory.Q.obj Q ≅
        (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K :=
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategoryFactors.symm.app P
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (_hP₀ : CochainComplex.IsAcyclicTensorKFlat (R := (f ⁻¹ᵁ V).toScheme.sheaf) Q),
    ∃ (hcP₀ : IsIso ((counit j).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))),
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    ∃ l : F₀.obj ((Arrow.mk (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q hcP₀ i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoPullback f f' g g' sq z.val P hcP i)).left),
      F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q hcP₀ i ≫
        H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          ν.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i)
```

The archive has four public imports: WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData,
Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality, Mathlib.CategoryTheory.Comma.Arrow,
and WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso. All four are retained.

## New

The module retains the four public imports above and adds:

```lean
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTermwiseComparison
```

The adopted source supplies the theorem with this signature, verbatim:

```lean
theorem exists_singleComplexOpen_termwise_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let a : DerivedCategory.Q.obj Q ≅
        (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K :=
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategoryFactors.symm.app P
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (_hP₀ : CochainComplex.IsKFlatTensor (R := (f ⁻¹ᵁ V).toScheme.sheaf) Q),
    ∃ (hcP₀ : IsIso ((counit j).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))),
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    ∃ l : F₀.obj ((Arrow.mk (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q hcP₀ i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoPullback f f' g g' sq z.val P hcP i)).left),
      F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q hcP₀ i ≫
        H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          ν.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i)
```

The only textual type difference is IsKFlatTensor versus IsAcyclicTensorKFlat, in the input
and restricted output K-flatness predicates. Both unfold to exactly the same acyclic tensor
formula. A signature probe applies the source theorem to the entire archived signature without
any rewrite or mathematical adapter (compiled in 6.2 seconds). The theorem
axiom check reports exactly propext, Classical.choice and Quot.sound. No definition used by a target changes.

The node keeps its Sheaf module/file attachment and historical statement. existing=true now
records that its declaration comes from the public import. Its proof plan and dependencies stay:
K-flat restriction, pinned counit invertibility, ordinary-comparison transport and cancellation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison | X8, assigned repair | Restored as a public re-export; no duplicate declaration. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | quarantined, no current claim | Historical importer and DAG parent; same full theorem type by definitional equality. Unmodified archive compiles in 42.9 seconds against this wrapper; no edit required. |

The source-only downstream tool reports zero live importers, since the module is quarantined.
A search of quarantine/Sheaf finds the parent above, whose proof uses the same theorem by name.
The DAG parent lem-pc-single-complex-open-normalized-transport remains attached to that parent
and still cites lem-pc-single-complex-open-termwise-comparison. No parent edge is pruned.

## Status

landed 20261021T171859-L-3173551 2026-10-21 (merge of deliver/X8/Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison)
