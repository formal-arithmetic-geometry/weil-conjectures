# AlgebraicGeometry.exists_pinned_stalk_tensor

## Reason

Reviewer X-56534 requested the complex-level pinned stalk tensor interface. The first worker replaced the existing chain-square declaration, breaking its caller, and left the new interface unproved. This revision proves that interface and preserves every existing Lean signature. The chain-square proof is decomposed into construction of pinned coordinate isomorphisms and their remaining compatibility equation.

## Old

The existing signature of AlgebraicGeometry.exists_tensor_pullback_stalk_square is retained verbatim:

```lean
theorem exists_tensor_pullback_stalk_square [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g) (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ) (a : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q ⟶ N) (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj (pullbackTensorTotal X P Q) ≅ pullbackTensorTotal X' (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q)) (hχ : ∀ (p q n : ℤ) (h : p + q = n), (Scheme.Modules.tensorPullback g').map (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫ χ.hom.f n = ((Classical.choose (Scheme.Modules.module_pullback_tensor g')) (P.X p) (Q.X q)).hom ≫ HomologicalComplex.ιMapBifunctor (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor _) (.up ℤ) p q n h) (z : X') : letI := SingleComplexBaseChange.leftAlgebra f g' z letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z)) letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z)) let R := SingleComplexBaseChange.R f g' z let A := SingleComplexBaseChange.A g' z let B := SingleComplexBaseChange.B f' z let C := SingleComplexBaseChange.C z let F := (ModuleCat.extendScalars.{u, u, u} ((algebraMap (TensorProduct R A B) C).comp (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ) let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex (.up ℤ) let U := SingleComplexBaseChange.stalkComplex g' z P let V := SingleComplexBaseChange.stalkComplex g' z Q let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom ≫ S.map a ∃ (σ : U ⊗ V ≅ SingleComplexBaseChange.stalkComplex g' z (pullbackTensorTotal X P Q)) (ρ : F.obj U ⊗ S.obj N ≅ S.obj (pullbackTensorTotal X' (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) N)), F.map σ.hom ≫ (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z (pullbackTensorTotal X P Q)).hom ≫ S.map (χ.hom ≫ HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ)) = (Functor.Monoidal.μIso F U V).inv ≫ (F.obj U ◁ t) ≫ ρ.hom
```

## New

The existing signature above is unchanged. The new pinned comparison is:

```lean
theorem exists_pinned_stalk_tensor (Y : Scheme.{u}) (z : Y) : letI := SheafOfModules.monoidalCategory Y.sheaf let T := RingedSpace.moduleStalkFunctor Y.toRingedSpace z letI := ModuleCat.monoidalCategory (R := Y.presheaf.stalk z) let S := T.mapHomologicalComplex (.up ℤ) ∃ e : ∀ P Q : CochainComplex Y.Modules ℤ, S.obj (pullbackTensorTotal Y P Q) ≅ S.obj P ⊗ S.obj Q, ∀ P Q p q n (h : p + q = n), T.map (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫ (e P Q).hom.f n = (Classical.choose (SheafOfModules.stalkTensorIso Y.toRingedSpace z) (P.X p) (Q.X q)).hom ≫ HomologicalComplex.ιMapBifunctor (S.obj P) (S.obj Q) (curriedTensor _) (.up ℤ) p q n h
```

The added equality-only helper fixes sigma and rho to the constructed pinned comparisons; its exact signature is recorded in lem-pc-pinned-tensor-square-compatibility. This is not a new existential chain-square assumption. It leaves only the chain equation open, while the pinned comparison and the isomorphism constructors are proved.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates | unclaimed in this delivery | Its original chain-square declaration and signature remain available; no Lean adaptation. Its DAG proof now cites lem-pc-tensor-pullback-stalk-square-assembly. |
| Sheaf.AlgebraicGeometry.TensorPullbackStalkSquare | M1 | One proof-only import of the calculation module (which publicly imports the construction module); existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.PinnedTensorSquareCompatibility | M1 | New module uses the proved pinned comparison in its statement; only its equality is deferred. |

No definition used by a Challenge.lean target is changed. No existing public import is removed or privatized. The new module PinnedStalkTensor exposes precisely the imports needed by its signature; its three construction/proof imports remain plain.

## Status

landed 20261013T211109-L-393708 2026-10-13 (merge of deliver/M1/Sheaf.AlgebraicGeometry.TensorPullbackStalkSquare)
