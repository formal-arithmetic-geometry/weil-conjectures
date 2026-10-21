# AlgebraicGeometry.derivedPullback_tensor_successive_normalization

## Reason

Restore the assigned quarantined module as a compatibility import of the complete
adopted source proof. The archived file has zero holes, but its attempted restoration
exceeded the 60-second single-file limit. Its proof imports the now-withdrawn
Sheaf.Algebra.Homology.KFlatPullback and uses the old IsAcyclicTensorKFlat name.
The source already proves exactly the normalization identity with IsKFlatTensor.
The two K-flat definitions have verbatim identical bodies, so the predicate rename
does not change the mathematical hypotheses. Comparing the full parsed theorem
signatures gives equality after that rename, including every chosen comparison.

This repairs an unavailable public import path without duplicating the theorem or
removing its attachment. The DAG attachment now records the existing source theorem;
its statement dependencies, proof dependencies, and three-step proof plan remain.
The adopted source tree is untouched. No target statement or definition is changed.

## Old

The quarantined module declared this signature locally, followed by its complete
normalization-pasting proof:

```lean
theorem derivedPullback_tensor_successive_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hN : N.IsAcyclicTensorKFlat)
    (φ : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hφ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f ≫ g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal Z P N)
    let β := Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
    ((derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N))) ≫
      (((SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap X
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)) =
    (derivedPullback f).map ((derivedPullback g).map (pullbackTensorModelMap Z P N)) ≫
      (derivedPullback f).map ((SingleComplexBaseChange.counit g).app H) ≫
      (SingleComplexBaseChange.counit f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map (β.hom.app H) ≫ DerivedCategory.Q.map φ.hom
```

## New

The restored module publicly imports
WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization.
That import exposes the complete existing proof with this signature:

```lean
theorem derivedPullback_tensor_successive_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hN : N.IsKFlatTensor)
    (φ : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hφ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f ≫ g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal Z P N)
    let β := Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
    ((derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N))) ≫
      (((SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap X
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)) =
    (derivedPullback f).map ((derivedPullback g).map (pullbackTensorModelMap Z P N)) ≫
      (derivedPullback f).map ((SingleComplexBaseChange.counit g).app H) ≫
      (SingleComplexBaseChange.counit f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map (β.hom.app H) ≫ DerivedCategory.Q.map φ.hom
```

The only signature difference is the definitionally identical K-flat predicate name.
The private generic pasting helper is supplied by the adopted proof and is not
redeclared. The Sheaf compatibility path continues to supply the public theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization | K3 | Restored compatibility import; canonical proved theorem is publicly available. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat | unclaimed (quarantined) | Its recorded DAG dependency is preserved. The same public theorem name and identity are available from the restored import path; its own obsolete K-flat interface remains part of its separate quarantine repair. |

`tools/downstream.py` with `--allow-missing --uses` finds zero live importers and
zero live textual users. A separate search of quarantine/ finds the parent listed
above. Its node lem-sc-derived-pullback-composition-tensor-kflat still cites this
normalization node in its proof step and proof_deps; these dependencies are retained.
No withdrawal is inferred from the absence of live importers. The child ordinary
localized-composition node has this item in blueprint.from (provenance only), and
its current proved source module remains imported by the adopted normalization proof.

## Status

landed 20261021T225150-L-3784479 2026-10-21 (merge of deliver/K3/Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization)
