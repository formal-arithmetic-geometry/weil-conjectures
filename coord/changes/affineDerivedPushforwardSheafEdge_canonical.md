# affineDerivedPushforwardSheafEdge_canonical

## Reason

Review point E2/4: arbitrary epsilon=0 contradicts compatibility for the identity on
Spec(k), k nonzero, in degree zero on tilde(k[0]). Repair the component and parent
compatibility to use the canonical edge; pin the existence witness independently.

The canonical edge is the inverse of the unique natural reverse comparison on
K-injectives. Its components use a real kernel lift and homology cokernel descent,
transported through the canonical right-derived-unit isomorphism. The existence and
uniqueness theorem determines the whole object up to equality, including its inverse;
choosing this unique object is permitted by AGENTS.md §5. It contains no exact-family
compatibility equation. The two new proof holes concern unique affine descent and
resolution naturality, not arbitrary witness normalization. There is no hollow data.

Neither target statements nor definitions previously used by target statements
change. The parent compatible-edge existential statement keeps its existing type;
it remains open in its independently held module; the repaired interfaces now
supply a canonical witness and its compatibility for its eventual proof.
The statement review should record this corrected meaning of the affine comparison.

## Old

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent`

```lean
theorem affineDerivedPushforwardSheafEdge_component (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) (ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i) (F : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology] (_hF : ∀ M, (F.obj M).IsQuasicoherent) (C : CochainComplex (ModuleCat.{u} A) ℤ) (hC : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))) : (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map (((C.sc i).mapHomologyIso F).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫ ε.app ⟨_, hC⟩ = ((C.sc i).mapHomologyIso (F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app (((F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom) |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫ (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map (((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app ((HomotopyCategory.quotient _ (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj C)))
```

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility`

```lean
theorem affineDerivedPushforwardSheafEdge_compatibility (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) : (ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i) → (∀ (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (hK : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj K)) (T : (K.sc i).LeftHomologyData) (U : ((((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj K).sc i).LeftHomologyData) (k : (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj T.K ⟶ U.K), (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map T.i = k ≫ U.i → (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map (T.π ≫ T.homologyIso.inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app K).inv) ≫ ε.app ⟨_, hK⟩ = k ≫ U.π ≫ U.homologyIso.inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app (((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj K)).inv ≫ (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map (((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) → ∀ (F : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology] (_hF : ∀ M, (F.obj M).IsQuasicoherent) (C : CochainComplex (ModuleCat.{u} A) ℤ) (hC : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))), (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map (((C.sc i).mapHomologyIso F).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫ ε.app ⟨_, hC⟩ = ((C.sc i).mapHomologyIso (F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app (((F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom) |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫ (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map (((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app ((HomotopyCategory.quotient _ (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj C)))
```

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence`

```lean
theorem exists_affineDerivedPushforwardSheafEdge_existence (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) : Nonempty ((schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i)
```

## New

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent`

```lean
theorem affineDerivedPushforwardSheafEdge_component (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) (F : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology] (_hF : ∀ M, (F.obj M).IsQuasicoherent) (C : CochainComplex (ModuleCat.{u} A) ℤ) (hC : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))) : (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map (((C.sc i).mapHomologyIso F).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫ (affineDerivedPushforwardSheafEdge_canonical A B φ i).app ⟨_, hC⟩ = ((C.sc i).mapHomologyIso (F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app (((F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom) |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫ (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map (((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app ((HomotopyCategory.quotient _ (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj C)))
```

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility`

```lean
theorem affineDerivedPushforwardSheafEdge_compatibility (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) : ∀ (F : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms] [(F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology] (_hF : ∀ M, (F.obj M).IsQuasicoherent) (C : CochainComplex (ModuleCat.{u} A) ℤ) (hC : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))), (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map (((C.sc i).mapHomologyIso F).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫ (affineDerivedPushforwardSheafEdge_canonical A B φ i).app ⟨_, hC⟩ = ((C.sc i).mapHomologyIso (F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫ ((DerivedCategory.homologyFunctorFactors _ i).app (((F ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom) |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫ (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map (((RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app ((HomotopyCategory.quotient _ (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj C)))
```

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence`

```lean
theorem exists_affineDerivedPushforwardSheafEdge_existence (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) : ∃ ε : ((schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙ RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙ schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i), ε = affineDerivedPushforwardSheafEdge_canonical A B φ i
```

## Users

`tools/downstream.py --uses` finds no direct caller outside the three declaration
modules on the current base: the earlier parent compatibility was replaced with
conditional cycle normalization and the edge assembly was restored to `sorry`.
The repaired parent compatibility calls the repaired component in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent | G4 | Item: remove arbitrary epsilon, use canonical edge, prove the component by reverse-comparison cancellation. |
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility | G4 | Claimed interface repair: replace the conditional arbitrary-edge interface with unconditional compatibility of the constructed canonical edge. |
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence | G4 | Claimed interface repair: pin the witness to the independently constructed canonical edge. |
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge | N4 | No source change: its existing existential statement and open proof compile unchanged against the repaired dependencies. |

The latter module imports both changed parent interfaces but has no application
of either declaration in its current proof. The downstream modules
`AffinePushforwardCohomologyEdgeExists` and `AffinePushforwardCohomologyEdgeIdentity`
use only its unchanged compatible-edge existential signature. No forced
adaptation is necessary, and no module held by another group is changed.

The claims for both interface repairs were checked with the server's claim tool:
Compatibility and Existence are held by G4. Edge is held by N4. The canonical
construction and its supporting modules are new nodes of this item.

## Status

landed 20261014T041057-L-1059047 2026-10-14 (merge of deliver/G4/Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent)
