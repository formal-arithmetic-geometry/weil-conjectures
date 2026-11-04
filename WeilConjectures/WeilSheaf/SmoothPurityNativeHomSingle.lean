/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.DerivedHomSingleResolution
public import WeilConjectures.WeilSheaf.SmoothPurityWhiskering

/-!
# The native closed internal Hom from a sheaf

The representative formulas identify the native closed internal Hom from a
sheaf with its right derived internal Hom, naturally in the target complex.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

private lemma singleProjection_right (A : ProEtaleWeilSheaf k₀ l X)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X)
        (K := (CochainComplex.singleFunctor _ 0).obj A) g ≫
        singleResolutionProjection A I' =
      singleResolutionProjection A I ≫
        ((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [HomologicalComplex.comp_f, singleResolutionProjection]
  rw [Category.assoc, CochainComplex.bifunctorHomMapRight_f_π_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  exact congrArg (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
    ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫ ·)
    (((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).naturality (g.f n))

/-- The closed-model internal Hom from the localization of a single complex is
the right derived internal Hom of its sheaf, naturally in the target. -/
noncomputable def nativeHomSingleComplexIso (A : ProEtaleWeilSheaf k₀ l X) :
    Prod.sectR (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A))) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor := by
  let C := ProEtaleWeilSheaf k₀ l X
  let H := (nativeDerivedClosedComparison k₀ l X).homModels.weilHom
  let M := (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives
  let P := (CochainComplex.singleFunctor C 0).obj A
  let F := ihomFunctor k₀ l X A
  let q := (CochainComplex.KInjectives.ι (C := C)) ⋙ DerivedCategory.Q
  have : q.Full :=
    inferInstanceAs (CochainComplex.KInjectives.toHomotopyCategory ⋙
      (HomotopyCategory.KInjectives.Qh (C := C))).Full
  have : q.EssSurj :=
    inferInstanceAs (CochainComplex.KInjectives.toHomotopyCategory ⋙
      (HomotopyCategory.KInjectives.Qh (C := C))).EssSurj
  apply (Functor.fullyFaithfulWhiskeringLeftOfFullEssSurj q (DerivedCategory C)).preimageIso
  refine NatIso.ofComponents (fun I ↦ ?_) ?_
  · have := I.property
    have := singleResolutionProjection_isIso A I.obj
    exact M.model P I.obj I.property ≪≫
      DerivedCategory.Q.mapIso (asIso (singleResolutionProjection A I.obj)) ≪≫
      (F.rightDerivedFunctorObjQIso I.obj).symm
  · intro I I' g
    have := I.property
    have := I'.property
    have := singleResolutionProjection_isIso A I.obj
    have := singleResolutionProjection_isIso A I'.obj
    have hm : H.map (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
        (DerivedCategory.Q.map g.hom)) ≫ (M.model P I'.obj I'.property).hom =
      (M.model P I.obj I.property).hom ≫ DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X) (K := P) g.hom) := by
      simpa only [Functor.map_id, op_id, CochainComplex.bifunctorHomMapLeft_id,
        Category.id_comp] using M.naturality P P I.obj I'.obj I.property I'.property
          (𝟙 P) g.hom
    apply (cancel_mono (F.rightDerivedFunctorObjQIso I'.obj).hom).mp
    dsimp only [Functor.comp_map, Prod.sectR_map, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_hom]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hm, Category.assoc, ← DerivedCategory.Q.map_comp,
      singleProjection_right, DerivedCategory.Q.map_comp]

/-- The same comparison in the standard derived single-functor coordinates. -/
noncomputable def nativeHomSingleIso (A : ProEtaleWeilSheaf k₀ l X) :
    Prod.sectR (op ((DerivedCategory.singleFunctor _ 0).obj A)) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun _ ↦
      (((DerivedCategory.singleFunctorIsoCompQ _ 0).app A).symm.op).prod (Iso.refl _))
      (fun _ ↦ by simp)) _ ≪≫ nativeHomSingleComplexIso A

end AlgebraicGeometry.ProEtaleWeilSheaf
