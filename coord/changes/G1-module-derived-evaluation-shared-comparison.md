# CategoryTheory.exact_comp_comparison and its formula and zero lemmas

## Reason

The return of head 793656a03 rejects the duplicated private exact-composite helpers
in ModuleDerivedEvaluationSlice. The original helpers already have the needed general
abelian-category signatures, but are private and cannot be imported. Expose the existing
construction and its two existing proved lemmas in place, without changing their types
or bodies, and have the slice proof import and use them. The defining module is unclaimed
(no claim file at the time of repair). Add docstrings for these newly public declarations.
Promote the existing Comp import to public because rightAcyclic occurs in their public
signatures and mapResolution occurs in the exposed construction.

## Old

```lean
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

private noncomputable def exact_comp_comparison
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I)) (q : ℕ) :
    (T ⋙ F).rightDerived q ≅ T ⋙ F.rightDerived q :=
  NatIso.ofComponents (fun M ↦
    (injectiveResolution M).isoRightDerivedObj (T ⋙ F) q ≪≫
      (F.rightDerivedObjIsoOfResolution (T.mapResolution (injectiveResolution M).ι)
        (fun n ↦ hT ((injectiveResolution M).cocomplex.X n)) q).symm) (by
    intro M N f
    let I := injectiveResolution M
    let K := injectiveResolution N
    let φ := InjectiveResolution.desc f K I
    let ι := T.mapResolution I.ι
    let κ := T.mapResolution K.ι
    let c := F.rightDerivedObjIsoOfResolution ι (fun n ↦ hT (I.cocomplex.X n)) q
    let d := F.rightDerivedObjIsoOfResolution κ (fun n ↦ hT (K.cocomplex.X n)) q
    have hw : ι ≫ (T.mapHomologicalComplex _).map φ =
        (CochainComplex.single₀ _).map (T.map f) ≫ κ := by
      dsimp only [ι, κ, Functor.mapResolution]
      rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
        Functor.map_comp, ← Category.assoc]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ k ≫ (T.mapHomologicalComplex _).map K.ι)
          ((HomologicalComplex.singleMapHomologicalComplex T
            (ComplexShape.up ℕ) 0).inv.naturality f).symm
    have hc := acyclicComparison_naturality F ι κ
      (fun n ↦ hT (I.cocomplex.X n)) (fun n ↦ hT (K.cocomplex.X n))
      (T.map f) ((T.mapHomologicalComplex _).map φ) hw q
    have hd := InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ
      (InjectiveResolution.desc_commutes_zero f K I) (T ⋙ F) q
    change ((T ⋙ F).rightDerived q).map f ≫
        ((K.isoRightDerivedObj (T ⋙ F) q).hom ≫ d.inv) =
      ((I.isoRightDerivedObj (T ⋙ F) q).hom ≫ c.inv) ≫ (F.rightDerived q).map (T.map f)
    rw [← Category.assoc, hd, Category.assoc]
    simp only [Category.assoc]
    convert congrArg (fun k ↦ (I.isoRightDerivedObj (T ⋙ F) q).hom ≫ k) hc using 1
    rfl)

private theorem exact_comp_comparison_formula
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I))
    (M : A) (I : InjectiveResolution M) (K : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ) :
    (exact_comp_comparison T F hT q).hom.app M ≫ (K.isoRightDerivedObj F q).hom =
      (I.isoRightDerivedObj (T ⋙ F) q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) q

private theorem exact_comp_comparison_zero
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I)) :
    (T ⋙ F).toRightDerivedZero ≫ (exact_comp_comparison T F hT 0).hom =
      Functor.whiskerLeft T F.toRightDerivedZero
```

## New

```lean
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

noncomputable def exact_comp_comparison
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I)) (q : ℕ) :
    (T ⋙ F).rightDerived q ≅ T ⋙ F.rightDerived q :=
  NatIso.ofComponents (fun M ↦
    (injectiveResolution M).isoRightDerivedObj (T ⋙ F) q ≪≫
      (F.rightDerivedObjIsoOfResolution (T.mapResolution (injectiveResolution M).ι)
        (fun n ↦ hT ((injectiveResolution M).cocomplex.X n)) q).symm) (by
    intro M N f
    let I := injectiveResolution M
    let K := injectiveResolution N
    let φ := InjectiveResolution.desc f K I
    let ι := T.mapResolution I.ι
    let κ := T.mapResolution K.ι
    let c := F.rightDerivedObjIsoOfResolution ι (fun n ↦ hT (I.cocomplex.X n)) q
    let d := F.rightDerivedObjIsoOfResolution κ (fun n ↦ hT (K.cocomplex.X n)) q
    have hw : ι ≫ (T.mapHomologicalComplex _).map φ =
        (CochainComplex.single₀ _).map (T.map f) ≫ κ := by
      dsimp only [ι, κ, Functor.mapResolution]
      rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
        Functor.map_comp, ← Category.assoc]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ k ≫ (T.mapHomologicalComplex _).map K.ι)
          ((HomologicalComplex.singleMapHomologicalComplex T
            (ComplexShape.up ℕ) 0).inv.naturality f).symm
    have hc := acyclicComparison_naturality F ι κ
      (fun n ↦ hT (I.cocomplex.X n)) (fun n ↦ hT (K.cocomplex.X n))
      (T.map f) ((T.mapHomologicalComplex _).map φ) hw q
    have hd := InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ
      (InjectiveResolution.desc_commutes_zero f K I) (T ⋙ F) q
    change ((T ⋙ F).rightDerived q).map f ≫
        ((K.isoRightDerivedObj (T ⋙ F) q).hom ≫ d.inv) =
      ((I.isoRightDerivedObj (T ⋙ F) q).hom ≫ c.inv) ≫ (F.rightDerived q).map (T.map f)
    rw [← Category.assoc, hd, Category.assoc]
    simp only [Category.assoc]
    convert congrArg (fun k ↦ (I.isoRightDerivedObj (T ⋙ F) q).hom ≫ k) hc using 1
    rfl)

theorem exact_comp_comparison_formula
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I))
    (M : A) (I : InjectiveResolution M) (K : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ) :
    (exact_comp_comparison T F hT q).hom.app M ≫ (K.isoRightDerivedObj F q).hom =
      (I.isoRightDerivedObj (T ⋙ F) q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) q

theorem exact_comp_comparison_zero
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I)) :
    (T ⋙ F).toRightDerivedZero ≫ (exact_comp_comparison T F hT 0).hom =
      Functor.whiskerLeft T F.toRightDerivedZero
```

All three bodies are verbatim. The definition block above includes its body; theorem
blocks show their signatures. Existing public signatures and attributes are unchanged.
No target uses these helpers in its statement or definitions, so target meanings are unchanged.

## Users

The full downstream.py search finds only the defining module mentioning these names,
as expected for private declarations. The direct importers below need no adaptation:
this change only adds public API. The new slice caller is compiled in the same packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison | unclaimed | Expose its existing three helpers; its own theorem proof is unchanged. |
| Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice | G1 | Remove duplicate helpers and import the original ones. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity | unclaimed | No use of the helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity | unclaimed | No use of the helpers; no adaptation. |
| Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility | unclaimed | No use of the helpers; no adaptation. |
| Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic | unclaimed | No use of the helpers; no adaptation. |
| Sheaf.Paper.ComparisonBoundZero | unclaimed | No use of the helpers; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | No use of the helpers; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No use of the helpers; no adaptation. |

## Status

landed 20261021T111124-L-4155636 2026-10-21 (merge of deliver/G1/Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice)
