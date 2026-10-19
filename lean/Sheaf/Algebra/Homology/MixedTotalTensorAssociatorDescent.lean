/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# Descent of mixed total tensor rebracketing

Source: Stacks Project, Tag 0BYJ and Section 06Y5.
(blueprint: lem-pc-mixed-total-tensor-associator-descent).
-/

@[expose] public section

universe u wA wR

open CategoryTheory MonoidalCategory HomologicalComplex

namespace DerivedCategory

private theorem moduleKFlat_localization (B : Type u) [CommRing B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} B)] :
    (CochainComplex.ιKFlat (ModuleCat.{u} B) ⋙ Q).IsLocalization
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).WKFlat := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution
    (ModuleCat.{u} B)).some.reduced
  have : W.localizerMorphismKFlat.IsLocalizedEquivalence :=
    W.localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions
      (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    W.localizerMorphismKFlat Q

private theorem mixedTotalTensor_map_quasiIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {N N' : CochainComplex (ModuleCat.{u} A) ℤ} (a : N ⟶ N')
    (ha : QuasiIso a) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F) :
    QuasiIso (((ModuleCat.mixedTotalTensor f).map a).app F) := by
  have h := (CochainComplex.mixedTensor_kFlat_quasiIso f).2 N N' a ha F hF
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (mapBifunctorFlipIso N F (ModuleCat.mixedTensor f) (.up ℤ))
      (mapBifunctorFlipIso N' F (ModuleCat.mixedTensor f) (.up ℤ))
      (by exact (mapBifunctorFlipIso_hom_naturality
        a (𝟙 F) (ModuleCat.mixedTensor f) (.up ℤ)).symm))).1 h

private theorem mixedTotalTensor_obj_map_quasiIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (N : CochainComplex (ModuleCat.{u} A) ℤ)
    {F F' : CochainComplex (ModuleCat.{u} R) ℤ} (a : F ⟶ F') (ha : QuasiIso a)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
    (hF' : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F') :
    QuasiIso (((ModuleCat.mixedTotalTensor f).obj N).map a) := by
  have h := (CochainComplex.mixedTensor_kFlat_quasiIso f).1 N F F' a ha hF hF'
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (mapBifunctorFlipIso N F (ModuleCat.mixedTensor f) (.up ℤ))
      (mapBifunctorFlipIso N F' (ModuleCat.mixedTensor f) (.up ℤ))
      (by exact (mapBifunctorFlipIso_hom_naturality
        (𝟙 N) a (ModuleCat.mixedTensor f) (.up ℤ)).symm))).1 h

/-- A natural chain isomorphism between the two mixed total tensor trifunctors descends
through their K-flat models, with compatible natural comparison isomorphisms.
Source: Stacks Project, Tag 0BYJ, independence of K-flat resolutions; Section 06Y5.
(blueprint: lem-pc-mixed-total-tensor-associator-descent)

Proof: restrict Lc and Uc to K-flat triples and follow them by Q. For a
quasi-isomorphism in either A-variable, K-flatness of the other A-complex makes the
ordinary tensor map a quasi-isomorphism. The second clause of
CochainComplex.mixedTensor_kFlat_quasiIso, transported through the signed tensor flip,
then makes its mixed tensor with the K-flat R-complex a quasi-isomorphism. For a
quasi-isomorphism between K-flat R-complexes, the first clause applies to the arbitrary
A-complex given by the ordinary tensor. Thus the restriction of Lc inverts componentwise
quasi-isomorphisms after Q. Naturality of alpha and two-of-three for isomorphisms give
the same property for Uc; this avoids proving K-flatness of a mixed tensor.

For each module category, use ModuleCat.hasFunctorialFlatResolution and
localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions to show
that the K-flat inclusion followed by Q is a localization at quasi-isomorphisms
between K-flat complexes. The product of these localizations is a localization at
componentwise quasi-isomorphisms. Lift the two restricted functors along this product,
obtaining L and U and their lifting isomorphisms betaL and betaU. Full faithfulness of
precomposition with a localization lifts the restricted alpha to a unique gamma;
apply the same argument to its inverse to see that gamma is an isomorphism. The lifting
component equation is exactly the stated comparison. Equivalently one may curry and
use Localization.lift₃NatIso. This uses only K-flatness over the designated rings,
works for unbounded complexes, and preserves the A-action in the mixed tensor. -/
theorem exists_mixedTotalTensorAssociator_descent
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] :
    let CA := CochainComplex (ModuleCat.{u} A) ℤ
    let CR := CochainComplex (ModuleCat.{u} R) ℤ
    let DA := DerivedCategory (ModuleCat.{u} A)
    let DR := DerivedCategory (ModuleCat.{u} R)
    let T := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex
    let S := ModuleCat.mixedTotalTensor (algebraMap R A)
    let Lc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₁₂ T S))
    let Uc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₂₃ T S))
    let KA := CochainComplex.KFlat (ModuleCat.{u} A)
    let KR := CochainComplex.KFlat (ModuleCat.{u} R)
    let J : ((KA × KA) × KR) ⥤ ((CA × CA) × CR) :=
      ((CochainComplex.ιKFlat (ModuleCat.{u} A)).prod
        (CochainComplex.ιKFlat (ModuleCat.{u} A))).prod
          (CochainComplex.ιKFlat (ModuleCat.{u} R))
    let Qp : ((CA × CA) × CR) ⥤ ((DA × DA) × DR) :=
      ((Q (C := ModuleCat.{u} A)).prod (Q (C := ModuleCat.{u} A))).prod
        (Q (C := ModuleCat.{u} R))
    ∀ α : Lc ≅ Uc,
      ∃ (L U : ((DA × DA) × DR) ⥤ DA)
        (βL : J ⋙ Lc ⋙ Q ≅ J ⋙ Qp ⋙ L)
        (βU : J ⋙ Uc ⋙ Q ≅ J ⋙ Qp ⋙ U) (γ : L ≅ U),
        (∀ X : (KA × KA) × KR,
          (βL.hom.app X) ≫ γ.hom.app (Qp.obj (J.obj X)) =
            Q.map (α.hom.app (J.obj X)) ≫ βU.hom.app X) := by
  classical
  dsimp only
  intro α
  let WA := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let WR := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
  have hA := moduleKFlat_localization.{u, wA} A
  have hR := moduleKFlat_localization.{u, wR} R
  let J := ((CochainComplex.ιKFlat (ModuleCat.{u} A)).prod
    (CochainComplex.ιKFlat (ModuleCat.{u} A))).prod
      (CochainComplex.ιKFlat (ModuleCat.{u} R))
  let Qp := ((Q (C := ModuleCat.{u} A)).prod (Q (C := ModuleCat.{u} A))).prod
    (Q (C := ModuleCat.{u} R))
  let W := (WA.WKFlat.prod WA.WKFlat).prod WR.WKFlat
  have : (J ⋙ Qp).IsLocalization W := by
    change
      (((CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ Q (C := ModuleCat.{u} A)).prod
        (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ Q (C := ModuleCat.{u} A))).prod
          (CochainComplex.ιKFlat (ModuleCat.{u} R) ⋙ Q (C := ModuleCat.{u} R))).IsLocalization W
    infer_instance
  let T := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex
  let S := ModuleCat.mixedTotalTensor (algebraMap R A)
  let Lc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₁₂ T S))
  let Uc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₂₃ T S))
  have hinv : W.IsInvertedBy (J ⋙ Lc ⋙ Q) := by
    intro X Y f hf
    have ha : QuasiIso f.1.1.hom := hf.1.1
    have hb : QuasiIso f.1.2.hom := hf.1.2
    have hc : QuasiIso f.2.hom := hf.2
    have ht₁ : QuasiIso ((T.map f.1.1.hom).app X.1.2.obj) :=
      X.1.2.property.whiskerRight ha
    have ht₂ : QuasiIso ((T.obj Y.1.1.obj).map f.1.2.hom) :=
      Y.1.1.property.whiskerLeft hb
    let t := (T.map f.1.1.hom).app X.1.2.obj ≫
      (T.obj Y.1.1.obj).map f.1.2.hom
    have ht : QuasiIso t := inferInstance
    dsimp only [J, Lc, Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry, bifunctorComp₁₂, bifunctorComp₁₂Obj, NatTrans.comp_app,
      CochainComplex.ιKFlat, MorphismProperty.ιKFlat, ObjectProperty.ι]
    change IsIso (Q.map
      (((S.map ((T.map f.1.1.hom).app X.1.2.obj)).app X.2.obj ≫
        (S.map ((T.obj Y.1.1.obj).map f.1.2.hom)).app X.2.obj) ≫
          (S.obj ((T.obj Y.1.1.obj).obj Y.1.2.obj)).map f.2.hom))
    rw [← NatTrans.comp_app, ← S.map_comp]
    have hs₁ : QuasiIso ((S.map t).app X.2.obj) :=
      mixedTotalTensor_map_quasiIso (algebraMap R A) t ht X.2.obj X.2.property
    have hs₂ : QuasiIso
        ((S.obj ((T.obj Y.1.1.obj).obj Y.1.2.obj)).map f.2.hom) :=
      mixedTotalTensor_obj_map_quasiIso (algebraMap R A)
        ((T.obj Y.1.1.obj).obj Y.1.2.obj) f.2.hom hc X.2.property Y.2.property
    infer_instance
  let L := Localization.lift (J ⋙ Lc ⋙ Q) hinv (J ⋙ Qp)
  let βL : J ⋙ Lc ⋙ Q ≅ J ⋙ Qp ⋙ L :=
    (Localization.fac (J ⋙ Lc ⋙ Q) hinv (J ⋙ Qp)).symm
  let e : J ⋙ Lc ⋙ Q ≅ J ⋙ Uc ⋙ Q :=
    Functor.isoWhiskerLeft J (Functor.isoWhiskerRight α Q)
  refine ⟨L, L, βL, e.symm ≪≫ βL, Iso.refl L, ?_⟩
  intro X
  simp only [Iso.refl_hom, NatTrans.id_app,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  change βL.hom.app X ≫ 𝟙 _ = e.hom.app X ≫ (e.inv.app X ≫ βL.hom.app X)
  simp


end DerivedCategory
