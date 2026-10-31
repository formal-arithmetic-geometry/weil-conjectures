/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.ModulePullbackTensorIso
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.RingedTensorSquarePresentation

import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Pullback and localization of total tensor on arbitrary complexes

Source: Stacks Project, sites-cohomology.tex, Tag 0FPH,
lemma-tensor-pull-compatibility (blueprint: lem-sf-ringed-pullback-tensor-localization).
The auxiliary definitions specialize the existing ringed tensor presentation to the
native derived tensor and its canonical inverse localization maps on representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open WeilConjectures

namespace SheafOfModules

/-- The existing ringed-site corner with its native localization tensor.
Source: Stacks 0FPH and 06YT (blueprint: lem-sf-ringed-pullback-tensor-localization). -/
def pullbackLocalizationCorner
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} J R)] :
    RingedTensorCorner.{u, w} where
  site := C
  topology := J
  ring := R
  tensor := @MonoidalCategory.tensor _ _ (RingedDerivedNative.monoidal.{u, u, u, w} J R)

/-- The representative model is the inverse of the canonical lax localization tensorator.
Source: Stacks 06YT, 0FPH (blueprint: lem-sf-ringed-pullback-tensor-localization).
This is a restriction of the existing natural comparison to flat-term K-flat pairs. -/
def pullbackLocalizationModel
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} J R)] :
    RingedTensorModel (pullbackLocalizationCorner.{u, w} J R) where
  representative := NatIso.ofComponents
    (fun X ↦ RingedDerivedNative.tensorIso.{u, u, u, w} J R X.1.obj X.2.obj
      (Or.inl X.1.property.1))
    (fun {X Y} f ↦ RingedDerivedNative.tensorIso_naturality.{u, u, u, w} J R _ _ _ _
      (Or.inl X.1.property.1) (Or.inl Y.1.property.1) f.1.hom f.2.hom)

/-- The canonical lax localization tensorator, defined on every pair of complexes.
Source: Stacks 06YT, 0FPH (blueprint: lem-sf-ringed-pullback-tensor-localization). -/
def pullbackLocalizationTensorator
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} J R)]
    (A B : CochainComplex (RingedDerivedNative.Modules.{u, u, u} J R) ℤ) :
    (pullbackLocalizationCorner.{u, w} J R).tensor.obj
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj ((coefficientTotalTensor.{u, u, u} J R).obj (A, B)) := by
  letI := RingedDerivedNative.monoidal.{u, u, u, w} J R
  letI := RingedDerivedNative.lax.{u, u, u, w} J R
  exact Functor.LaxMonoidal.μ DerivedCategory.Q A B

/-- The ordinary pullback tensor comparison on signed direct-sum total complexes.
Source: Stacks 03EL, 0FPH (blueprint: lem-sf-ringed-pullback-tensor-localization).
The inverse of the recorded total comparison has the orientation used in 0FPH. -/
def pullbackLocalizationTotalComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (S : Sheaf J CommRingCat.{u}) (R : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} J S)]
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} K R)]
    (f : RingedTensorEdge (pullbackLocalizationCorner.{u, w} J S)
      (pullbackLocalizationCorner.{u, w} K R))
    (A B : CochainComplex (RingedDerivedNative.Modules.{u, u, u} J S) ℤ) :
    (f.pullback.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, u, u} J S).obj (A, B)) ⟶
      (coefficientTotalTensor.{u, u, u} K R).obj
        ((f.pullback.mapHomologicalComplex (.up ℤ)).obj A,
          (f.pullback.mapHomologicalComplex (.up ℤ)).obj B) := by
  letI := f.additive
  exact (f.ordinaryTensor.totalIso S R f.inverseRing f.inverse f.algebraic f.ringMap
    f.pullback f.object_eq f.pushforward f.moduleAdjunction A B).inv

set_option maxHeartbeats 5000000 in
-- Compare the two natural transformations and cancel a pair of resolution maps.
/-- The pullback/localization tensor square commutes for arbitrary unbounded complexes.
Source: Stacks Project, Tag 0FPH, lemma-tensor-pull-compatibility
(blueprint: lem-sf-ringed-pullback-tensor-localization).

Proof: package both paths as natural transformations on pairs of complexes. Naturality
of the total pullback comparison is the existing signed-total naturality lemma.
For flat-term K-flat P,T, apply the defining representative equation of the canonical
comparison. Its representative isomorphisms are the inverse native localization
maps. Compose with the target localization map and cancel the image of the source
representative isomorphism to obtain the asserted equality at P,T.
Choose flat-term K-flat resolutions p : P → A and q : T → B. Naturality of the two
transformations gives equality after precomposition with L(tensor(Qp,Qq)). The
localization sends p and q to isomorphisms, hence this precomposition is invertible
and can be canceled. The total tensor map of p,q is never inverted, and neither
are the computation or localization maps at arbitrary A,B. -/
theorem ringed_pullback_tensor_localization
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (S : Sheaf J CommRingCat.{u}) (R : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} J S)]
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{u, u, u} K R)]
    (f : RingedTensorEdge (pullbackLocalizationCorner.{u, w} J S)
      (pullbackLocalizationCorner.{u, w} K R))
    (A B : CochainComplex (RingedDerivedNative.Modules.{u, u, u} J S) ℤ) :
    (f.tensorComparison (pullbackLocalizationModel J S)
        (pullbackLocalizationModel K R)).hom.app
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
      (pullbackLocalizationCorner K R).tensor.map
        (Prod.mkHom (derivedPullbackComplexComparison f.pullback f.left f.epsilon A)
          (derivedPullbackComplexComparison f.pullback f.left f.epsilon B)) ≫
      pullbackLocalizationTensorator K R
        ((f.pullback.mapHomologicalComplex (.up ℤ)).obj A)
        ((f.pullback.mapHomologicalComplex (.up ℤ)).obj B) =
    f.left.map (pullbackLocalizationTensorator J S A B) ≫
      derivedPullbackComplexComparison f.pullback f.left f.epsilon
        ((coefficientTotalTensor.{u, u, u} J S).obj (A, B)) ≫
      DerivedCategory.Q.map (pullbackLocalizationTotalComparison J K S R f A B) := by
  let := f.additive
  let X := pullbackLocalizationCorner.{u, w} J S
  let Y := pullbackLocalizationCorner.{u, w} K R
  let F := f.pullback.mapHomologicalComplex (.up ℤ)
  let QS : CochainComplex (RingedDerivedNative.Modules.{u, u, u} J S) ℤ ⥤
      DerivedCategory (RingedDerivedNative.Modules.{u, u, u} J S) := DerivedCategory.Q
  let QR : CochainComplex (RingedDerivedNative.Modules.{u, u, u} K R) ℤ ⥤
      DerivedCategory (RingedDerivedNative.Modules.{u, u, u} K R) := DerivedCategory.Q
  let tS := coefficientTotalTensor.{u, u, u} J S
  let tR := coefficientTotalTensor.{u, u, u} K R
  let τS : (QS.prod QS) ⋙ X.tensor ⟶ tS ⋙ QS :=
    { app Z := pullbackLocalizationTensorator J S Z.1 Z.2
      naturality Z Z' g := by
        let : MonoidalCategory (DerivedCategory
            (RingedDerivedNative.Modules.{u, u, u} J S)) :=
          RingedDerivedNative.monoidal.{u, u, u, w} J S
        let := RingedDerivedNative.lax.{u, u, u, w} J S
        change (DerivedCategory.Q.map g.1 ⊗ₘ DerivedCategory.Q.map g.2) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q Z'.1 Z'.2 =
          Functor.LaxMonoidal.μ DerivedCategory.Q Z.1 Z.2 ≫
            DerivedCategory.Q.map ((g.1 ▷ Z.2) ≫ (Z'.1 ◁ g.2))
        rw [← tensorHom_def]
        exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q g.1 g.2 }
  let τR : (QR.prod QR) ⋙ Y.tensor ⟶ tR ⋙ QR :=
    { app Z := pullbackLocalizationTensorator K R Z.1 Z.2
      naturality Z Z' g := by
        let : MonoidalCategory (DerivedCategory
            (RingedDerivedNative.Modules.{u, u, u} K R)) :=
          RingedDerivedNative.monoidal.{u, u, u, w} K R
        let := RingedDerivedNative.lax.{u, u, u, w} K R
        change (DerivedCategory.Q.map g.1 ⊗ₘ DerivedCategory.Q.map g.2) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q Z'.1 Z'.2 =
          Functor.LaxMonoidal.μ DerivedCategory.Q Z.1 Z.2 ≫
            DerivedCategory.Q.map ((g.1 ▷ Z.2) ≫ (Z'.1 ◁ g.2))
        rw [← tensorHom_def]
        exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q g.1 g.2 }
  let κ : QS ⋙ f.left ⟶ F ⋙ QR :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso X.mateModules).inv f.left ≫
      Functor.whiskerLeft (HomotopyCategory.quotient X.mateModules (.up ℤ)) f.epsilon ≫
      Functor.whiskerRight (f.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso Y.mateModules).hom
  let β : (F.prod F) ⋙ tR ≅ tS ⋙ F := NatIso.ofComponents
    (fun Z ↦ f.ordinaryTensor.totalIso S R f.inverseRing f.inverse f.algebraic f.ringMap
      f.pullback f.object_eq f.pushforward f.moduleAdjunction Z.1 Z.2)
    (by
      intro Z Z' g
      let := monoidalCategory S
      let := monoidalCategory R
      let := ringedTensorPreadditive S
      let := ringedTensorPreadditive R
      dsimp only [F, tS, tR, coefficientTotalTensor, Functor.comp_map, Functor.prod_map,
        CanonicalRingedTensorComparison.totalIso, CanonicalRingedTensorComparison.total]
      simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
        asIso_hom, CanonicalTensorPullbackOfUniverses.tensorMap_factor]
      exact CanonicalTensorPullbackOfUniverses.tensorPullbackTotal_naturality
        f.pullback f.ordinaryTensor.mu f.ordinaryTensor.naturality g.1 g.2)
  let δ := f.tensorComparison (pullbackLocalizationModel J S) (pullbackLocalizationModel K R)
  let lhs : (QS.prod QS) ⋙ X.tensor ⋙ f.left ⟶ (F.prod F) ⋙ tR ⋙ QR :=
    Functor.whiskerLeft (QS.prod QS) δ.hom ≫
      Functor.whiskerRight (NatTrans.prod κ κ) Y.tensor ≫
      Functor.whiskerLeft (F.prod F) τR
  let rhs : (QS.prod QS) ⋙ X.tensor ⋙ f.left ⟶ (F.prod F) ⋙ tR ⋙ QR :=
    Functor.whiskerRight τS f.left ≫ Functor.whiskerLeft tS κ ≫
      Functor.whiskerRight β.inv QR
  have hrep (P T : CochainComplex (RingedDerivedNative.Modules.{u, u, u} J S) ℤ)
      (hp : X.mateFlat P) (ht : X.mateFlat T) : lhs.app (P, T) = rhs.app (P, T) := by
    have hc := Classical.choose_spec (ringedTopoiCanonicalDerivedTensorPullback
      f.inverse f.direct f.adjunction f.algebraic f.ringMap f.pullback f.object_eq f.map_eq
      f.left f.epsilon f.isLeftDerived X.mateFlat Y.mateFlat (fun _ ↦ Iff.rfl)
      (fun _ ↦ Iff.rfl) X.tensor Y.tensor
      (pullbackLocalizationModel J S).representative
      (pullbackLocalizationModel K R).representative f.ordinaryTensor
      f.pushforward f.moduleAdjunction).2.exists
    obtain ⟨hp', ht', hh⟩ := hc P T hp ht
    let rS := RingedDerivedNative.tensorIso.{u, u, u, w} J S P T (Or.inl hp.1)
    let rR := RingedDerivedNative.tensorIso.{u, u, u, w} K R (F.obj P) (F.obj T)
      (Or.inl hp'.1)
    have hs : rS.hom ≫ τS.app (P, T) = 𝟙 (QS.obj (tS.obj (P, T))) := by
      exact rS.hom_inv_id
    have hr : rR.hom ≫ τR.app (F.obj P, F.obj T) =
        𝟙 (QR.obj (tR.obj (F.obj P, F.obj T))) := by
      exact rR.hom_inv_id
    simp only [Functor.mapIso_inv] at hh
    change f.left.map rS.hom ≫ δ.hom.app (QS.obj P, QS.obj T) ≫
        Y.tensor.map (Prod.mkHom (κ.app P) (κ.app T)) =
      κ.app (tS.obj (P, T)) ≫ QR.map (β.inv.app (P, T)) ≫ rR.hom at hh
    apply (cancel_epi (f.left.map rS.hom)).1
    change f.left.map rS.hom ≫
        (δ.hom.app (QS.obj P, QS.obj T) ≫
          Y.tensor.map (Prod.mkHom (κ.app P) (κ.app T)) ≫
          τR.app (F.obj P, F.obj T)) =
      f.left.map rS.hom ≫ (f.left.map (τS.app (P, T)) ≫
        κ.app (tS.obj (P, T)) ≫ QR.map (β.inv.app (P, T)))
    let v := κ.app (tS.obj (P, T)) ≫ QR.map (β.inv.app (P, T))
    have hsource : f.left.map rS.hom ≫ f.left.map (τS.app (P, T)) =
        𝟙 (f.left.obj (QS.obj (tS.obj (P, T)))) :=
      (f.left.map_comp _ _).symm.trans
        ((congrArg f.left.map hs).trans (f.left.map_id _))
    have hpost : (κ.app (tS.obj (P, T)) ≫ QR.map (β.inv.app (P, T)) ≫ rR.hom) ≫
        τR.app (F.obj P, F.obj T) = v := by
      calc
        _ = v ≫ (rR.hom ≫ τR.app (F.obj P, F.obj T)) := by
          simp only [v, Category.assoc]
        _ = v ≫ 𝟙 _ := congrArg (fun z ↦ v ≫ z) hr
        _ = v := Category.comp_id v
    have hpre : f.left.map rS.hom ≫ (f.left.map (τS.app (P, T)) ≫
        κ.app (tS.obj (P, T)) ≫ QR.map (β.inv.app (P, T))) = v := by
      calc
        _ = (f.left.map rS.hom ≫ f.left.map (τS.app (P, T))) ≫ v := by
          simp only [v, Category.assoc]
        _ = 𝟙 _ ≫ v := congrArg (fun z ↦ z ≫ v) hsource
        _ = v := Category.id_comp v
    have hh' := congrArg (fun z ↦ z ≫ τR.app (F.obj P, F.obj T)) hh
    simpa only [Category.assoc] using (hh'.trans hpost).trans hpre.symm
  obtain ⟨P, p, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := S) A
  obtain ⟨T, q, ht, hg, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := S) B
  have hp' : X.mateFlat P := ⟨hp, hf⟩
  have ht' : X.mateFlat T := ⟨ht, hg⟩
  have : QuasiIso p := hq
  have : QuasiIso q := hr
  have : IsIso (QS.map p) := inferInstance
  have : IsIso (QS.map q) := inferInstance
  have : IsIso (Prod.mkHom (QS.map p) (QS.map q)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have hl := lhs.naturality (Prod.mkHom p q)
  have hr := rhs.naturality (Prod.mkHom p q)
  have he : lhs.app (A, B) = rhs.app (A, B) := by
    apply (cancel_epi (f.left.map
      (X.tensor.map (Prod.mkHom (QS.map p) (QS.map q))))).1
    exact hl.trans ((congrArg (fun z ↦ z ≫
      ((F.prod F) ⋙ tR ⋙ QR).map (Prod.mkHom p q)) (hrep P T hp' ht')).trans hr.symm)
  exact he

end SheafOfModules
