# Internal Hom dual scalar-model assembly

## Reason

The item's remaining proof needs two comparisons between the existing canonical ordinary
scalar realization and the sectionwise/point-scalar interfaces of its declared dependencies.
The comparisons are strictly separate steps of the argument. New public theorems are placed
in new Sheaf modules; the existing item's public API stays identical.

## Old

There were no declarations in the two new modules. The existing main theorem's proof was
`:= by sorry`; all of its signature and public imports are preserved verbatim.

## New

The new theorems are below. They use section variables for the topological commutative ring
`A : Type u` and the additivity instances of every canonical `modelFunctor A T`.

```lean
theorem ordinaryScalarPerfect_local_dual (S : Scheme.{u}) (P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj (Profinite.continuousCoefficientRingObj A) S))) (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) (F G : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ) (hbounded : ∀ i : 𝒰.I₀, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero ((F i).X q)) (hprojective : ∀ (i : 𝒰.I₀) (q : ℤ), Module.Finite A ((F i).X q) ∧ Module.Projective A ((F i).X q)) (τ : ∀ (i : 𝒰.I₀) (q : ℤ), (G i).X q ≅ ModuleCat.of A (Module.Dual A ((F i).X (-q)))) (hτ : ∀ (i : 𝒰.I₀) (q r : ℤ), (G i).d q r ≫ (τ i r).hom = (τ i q).hom ≫ ModuleCat.ofHom (-q.negOnePow • ((F i).d (-r) (-q)).hom.dualMap)) (hmodel : ∀ i : 𝒰.I₀, Nonempty (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory).obj P ≅ DerivedCategory.Q.obj (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj (F i)))) : ∀ i : 𝒰.I₀, Nonempty (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory).obj (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj A) S).obj (op P)).obj (𝟙_ _)) ≅ DerivedCategory.Q.obj (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj (G i)))
```

```lean
theorem ordinaryScalarModel_bounded_descent (S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S] (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj (Profinite.continuousCoefficientRingObj A) S))) (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) (F : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ) (hexact : ∀ T : Scheme.{u}, PreservesFiniteLimits (FiniteConstantModel.modelFunctor A T) ∧ PreservesFiniteColimits (FiniteConstantModel.modelFunctor A T)) (hbounded : ∀ i : 𝒰.I₀, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero ((F i).X q)) (hmodel : ∀ i : 𝒰.I₀, Nonempty (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory).obj Q ≅ DerivedCategory.Q.obj (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj (F i)))) (hfp : ∀ (i : 𝒰.I₀) (q : ℤ), Module.FinitePresentation A ((F i).homology q)) : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) S Q
```

The existing main theorem now combines these two steps with proved finite-presentation,
bounds and homology calculations, after applying the existing coefficient exactness theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.InternalHomDualConstructibleModels | B9 | New private proof imports; existing signatures and public imports unchanged. |

The two new modules have no pre-existing users. Existing consumers of the item see exactly
the same declarations and public imports. No source-library file or target is changed, and
no consumer adaptation is necessary.

## Status

landed 20261025T205856-L-3384397 2026-10-25 (merge of deliver/B9/Sheaf.Paper.InternalHomDualConstructibleModels)
