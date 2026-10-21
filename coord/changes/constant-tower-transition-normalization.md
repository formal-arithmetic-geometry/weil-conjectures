# Canonical derived comparison and single-object augmentation APIs

## Reason

`Sheaf.Paper.ConstantTowerTransition` repeatedly exceeded the 60-second file limit
while elaborating identities between concrete sheaf/derived functors. The costly
operation was normalizing the entire coefficient-restriction/direct-image square
and expanding canonical derived-unit and H0-iso constructions. Cache the ordinary
square with both composite functor types and expose proved equations. Mark the
existing large constructions `no_expose`; retain their bodies and signatures.

The augmentation in the item now uses the existing cached `singleRightDerivedH0Iso`.
Its published `_def` theorem identifies it with exactly the former composite;
the statement's meaning and the chosen canonical isomorphism are unchanged.
A target statement that uses the augmentation therefore has an implementation
change to review, with a proved equality to its old value.

## Old

`lean/Sheaf/Paper/ConstantTowerTransition.lean`:

```lean
noncomputable def constantTowerTransitionAugmentation
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) f).obj F ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj F)) :=
  ((lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedZeroIsoSelf.app F).symm
```

`lean/Sheaf/CategoryTheory/RightDerivedSingleH0.lean`:

```lean
def singleRightDerivedUnit (F : C ⥤ D) [F.Additive] :
    F ⋙ DerivedCategory.singleFunctor D 0 ⟶
      DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor where
  app M := DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)
  naturality M N f := by
    have hs := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality f
    have hu := F.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.singleFunctor C 0).map f)
    dsimp only [Functor.comp_map] at hu hs
    change DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (F.map f)) ≫
      _ ≫ _ = _
    erw [← DerivedCategory.Q.map_comp_assoc, hs, DerivedCategory.Q.map_comp,
      Category.assoc]
    simp only [Category.assoc]
    apply congrArg (fun g ↦ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫ g)
    exact hu
```

`lean/Sheaf/CategoryTheory/RightDerivedSingleH0.lean`:

```lean
@[irreducible] def singleRightDerivedH0Iso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [EnoughInjectives C] (M : C) :
    (DerivedCategory.homologyFunctor D 0).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≅ F.obj M :=
  F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫ F.rightDerivedZeroIsoSelf.app M

/-- The named identification is the usual composite of canonical H⁰ comparisons.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0).
Proof: unfold the explicit construction. -/
```

`lean/Sheaf/CategoryTheory/RightDerivedSingleH0.lean`:

```lean
@[irreducible] def mapSingleRightDerivedH0Iso
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [EnoughInjectives C]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : C) :
    (DerivedCategory.homologyFunctor E 0).obj
        (F.mapDerivedCategory.obj
          (R.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M))) ≅
      F.obj (R.obj M) :=
  (F.mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    F.mapIso (R.singleRightDerivedH0Iso M)
```

`lean/Sheaf/AlgebraicGeometry/ProEtaleFixedScalarRestrictionDirectImage.lean`:

```lean
noncomputable def fixedScalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ ⟶
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (fixedScalarRestrictionPullback φ f).hom
```

`lean/Sheaf/AlgebraicGeometry/ProEtaleFixedScalarRestrictionDirectImage.lean`:

```lean
noncomputable def fixedScalarRestrictionDirectImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) ≅
      R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  letI := fixedScalarRestrictionDirectImageMap_isIso φ f
  (asIso (fixedScalarRestrictionDirectImageMap φ f)).symm
```

## New

All original signatures and data are preserved, except the augmentation body is
replaced by its equal cached value:

```lean
  ((lowerStar (ModuleCat.{u + 1} A) f).singleRightDerivedH0Iso F).symm
```

`Functor.singleRightDerivedH0Iso_def` proves equality to the old composite.
`singleRightDerivedUnit`, `singleRightDerivedH0Iso`,
`mapSingleRightDerivedH0Iso`, `fixedScalarRestrictionDirectImageMap`, and
`fixedScalarRestrictionDirectImage` gain
`@[no_expose]`. Their former bodies are unchanged. The two H0 isos retain
`irreducible`.

Added, fully proved API in the same existing node/module:

- `exactSingleComparison` and `exactH0Comparison`: the canonical degree-zero
  exact-functor comparisons, cached with explicit functor types and `no_expose`.
  Their `_def` equations identify them with the original Mathlib/library
  constructions. The item first rewrites the two original comparison expressions
  using these equations; its public statement is unchanged. This avoids repeated
  kernel normalization of the concrete module structures in those composites.
  The new exact-postcomposition unit and inverse-H0 equations use these caches.

- `singleH0Comparison`: the canonical single/H0 natural isomorphism, cached
  with `no_expose`; `singleH0Comparison_def` proves equality to the Mathlib iso.
- `singleRightDerivedUnit_homology_zero`: the original single-unit normalization
  stated with this equal cached comparison. The exact-postcomposition cached
  normalization uses the same comparison.
- `mapSingleRightDerivedUnit`: the real composite of the inverse exact/single
  comparison with the exact derived functor applied to the single-object unit.
  Its `no_expose` attribute prevents repeated expansion of this composite on
  concrete module sheaves. The source and target are explicitly typed.
- `mapSingleRightDerivedUnit_def`: the defining composite equation.
- `mapSingleRightDerivedUnit_homology_zero`: the existing exact-postcomposition
  H0 normalization for this cached unit, proved from its defining equation.
- `singleRightDerivedUnit_app`: the localized inverse single comparison followed
  by the right-derived unit.
- `mapSingleRightDerivedH0Iso_inv`: the inverse identification is the exact functor applied to
  the inverse ordinary H0 iso followed by the exact homology comparison.
- `fixedScalarRestrictionDirectImageUnderived`: `Iso.refl`, typed as an iso between
  direct image then restriction and restriction then direct image. Its
  `no_expose` attribute prevents repeated whole-functor normalization.
- `fixedScalarRestrictionDirectImageUnderived_app_comp`: its inverse component
  postcomposed with any map leaves that actual section map unchanged.
- `fixedScalarRestrictionDirectImage_inv`: the inverse of the published forward
  comparison is exactly its named mate, proved by its defining construction.
- `fixedScalarRestrictionDirectImageMap_factors`: the existing private derived-mate
  unit equation specialized to the published coefficient comparison and cached
  ordinary square. This is proved from the existing private factorization, mate
  identification, and sectionwise mate identity.

`ConstantTowerTransition` publicly imports `RightDerivedSingleH0` because its
augmentation definition uses that module's canonical iso. It keeps its original
public imports. No source-library (`WeilConjectures`) declaration changes.

The original `RightDerivedSingleCounit` fails against the hidden unit at its
`change` on line 70 and its `dsimp` on line 183. The adaptation rewrites with
`singleRightDerivedUnit_app` immediately before that `change` and replaces the
`dsimp` with that rewrite. Only these two proof lines change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantTowerTransition | H3 | Item proof; equal cached augmentation body. |
| Sheaf.CategoryTheory.RightDerivedSingleH0 | unclaimed | Existing data unchanged; proved equations and canonical comparison caches added. |
| Sheaf.CategoryTheory.RightDerivedSingleCounit | unclaimed | Two forced proof rewrites; signatures unchanged. |
| Sheaf.CategoryTheory.SingleAdjunctionComparison | unclaimed | Uses the same units and H0 isos; statements unchanged. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | unclaimed | Uses the same H0 isos; statements unchanged. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | Transitive H0 API consumer; unchanged. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | Transitive H0 API consumer; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage | unclaimed | Comparison body unchanged; proved factorization API. |
| Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars | unclaimed | Same public coefficient iso; unchanged. |
| Sheaf.Paper.CompactSupportCoefficientChange | unclaimed | Same public coefficient iso; unchanged. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Same public coefficient iso; unchanged. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Same public coefficient iso; unchanged. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Same public coefficient iso; unchanged. |

The table includes the modules found by `tools/downstream.py --uses` for each
changed definition and all downstream modules of the two changed API modules.
No hypotheses, conclusions, universes or visibility are altered. Consumer
compilations are reported in the delivery report.

## Status

landed 20261021T012403-L-2184098 2026-10-21 (merge of deliver/H3/Sheaf.Paper.ConstantTowerTransition)
