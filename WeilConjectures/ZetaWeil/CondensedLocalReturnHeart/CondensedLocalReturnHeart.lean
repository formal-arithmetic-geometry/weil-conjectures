/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.ZetaWeil.CondensedReturn.CondensedLocalReturnOperators
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructiblePointScalarSectionsFinite
import Mathlib.Lean.Meta.CongrTheorems

/-! # Cohomology hearts and local returns with condensed coefficients

Source: latest blueprint, `prop-every-iterate-trace`, local operators and its opening
proof sentence, expanded by the cohomology-heart comparison
(blueprint: lem-zl-local-return-heart-part).

All objects are modules over the actual pulled-back condensed coefficient ring.
The fibre comparison is the composite of the normalized exact-functor comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedLocalReturnHeart

open CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The same point reparametrization on a module fibre, using the inverse of the
canonical point trivialization and the underived pullback compositor.
Source: clause 2 (blueprint: lem-zl-local-return-heart-part). -/
def moduleReparam {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (z : Spec (.of k) ⟶ T) (β : End (Spec (.of k))) (M : Modules Λ T) :
    (sections Λ (Spec (.of k))).obj ((CondensedRing.upperStar Λ z).obj M) ≅
      (sections Λ (Spec (.of k))).obj ((CondensedRing.upperStar Λ (β ≫ z)).obj M) :=
  (sections Λ (Spec (.of k))).mapIso
    ((CondensedReturn.identityComponent
        (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β)
        ((CondensedRing.upperStar Λ z).obj M)).symm ≪≫
      ((CondensedRing.upperStarComp Λ β z).app M).symm)

section SingleCompatibility

universe uA vA wA uB vB wB

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end SingleCompatibility

set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
attribute [local implicit_reducible] CondensedRing.moduleObjectDerivedPullback

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (d : D ≅ E) (x : A ⟶ D) (y : B ⟶ E)
    (h : x ≫ d.hom = a.hom ≫ y) : y ≫ d.inv = a.inv ≫ x := by
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Canonical concrete module instances require kernel conversion across pullback functors.
@[reassoc] private theorem theta_comp {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V)
    (K : D Λ V) (j : ℤ) :
    (theta Λ (f ≫ g) K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
        ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app K) =
      (CondensedRing.upperStarComp Λ f g).hom.app
          ((DerivedCategory.homologyFunctor _ j).obj K) ≫
        (CondensedRing.upperStar Λ f).map (theta Λ g K j).hom ≫
        (theta Λ f ((L Λ g).obj K) j).hom := by
  exact CondensedRing.leftDerivedUpperStarHomologyIso_comp_hom_app Λ f g j K

-- Canonical concrete module instances require kernel conversion across pullback functors.
private theorem theta_naturality {T U : Scheme.{u}} (f : T ⟶ U)
    {K K' : D Λ U} (v : K ⟶ K') (j : ℤ) :
    (theta Λ f K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map ((L Λ f).map v) =
      (CondensedRing.upperStar Λ f).map ((DerivedCategory.homologyFunctor _ j).map v) ≫
        (theta Λ f K' j).hom := by
  exact (((CondensedRing.upperStar Λ f).leftDerivedFunctorHomologyFunctorIso j).hom.naturality
    v).symm

-- Canonical concrete module instances require kernel conversion across pullback functors.
private theorem theta_id (T : Scheme.{u}) (K : D Λ T) (j : ℤ) :
    (theta Λ (𝟙 T) K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
        ((CondensedRing.leftDerivedUpperStarId Λ T).hom.app K) =
      (CondensedRing.upperStarId Λ T).hom.app ((DerivedCategory.homologyFunctor _ j).obj K) := by
  exact CondensedRing.leftDerivedUpperStarHomologyIso_hom_app_id Λ T j K

private theorem iterate_succ {C : Type*} [Category C] (P : C ⥤ C)
    (F : ℕ → C ⥤ C) (e : F 0 ≅ 𝟭 C) (step : ∀ n, F (n + 1) ≅ P ⋙ F n)
    (M : C) (φ : P.obj M ≅ M) (n : ℕ) :
    (CondensedReturn.iterateFromCompositors P F e step M φ (n + 1)).hom =
      (step n).hom.app M ≫ (F n).map φ.hom ≫
        (CondensedReturn.iterateFromCompositors P F e step M φ n).hom := by
  unfold CondensedReturn.iterateFromCompositors
  rfl

private theorem iterate_zero {C : Type*} [Category C] (P : C ⥤ C)
    (F : ℕ → C ⥤ C) (e : F 0 ≅ 𝟭 C) (step : ∀ n, F (n + 1) ≅ P ⋙ F n)
    (M : C) (φ : P.obj M ≅ M) :
    (CondensedReturn.iterateFromCompositors P F e step M φ 0).hom = e.hom.app M := by
  unfold CondensedReturn.iterateFromCompositors
  rfl

-- Retain the unit as a natural isomorphism when unfolding the abstract recursion.
private theorem moduleIterate_zero {T : Scheme.{u}} (g : End T)
    (M : Modules Λ T) (φ : (CondensedRing.upperStar Λ g).obj M ≅ M) :
    (CondensedReturn.moduleIterate Λ g M φ 0).hom =
      (CondensedRing.upperStarEqToIso Λ (pow_zero g) ≪≫
        CondensedRing.upperStarId Λ T).hom.app M := by
  unfold CondensedReturn.moduleIterate
  rw [iterate_zero]

-- Unfold the canonical compositor recursion across concrete module instances.
private theorem moduleIterate_succ {T : Scheme.{u}} (g : End T)
    (M : Modules Λ T) (φ : (CondensedRing.upperStar Λ g).obj M ≅ M) (n : ℕ) :
    (CondensedReturn.moduleIterate Λ g M φ (n + 1)).hom =
      (CondensedRing.upperStarEqToIso Λ (pow_succ' g n) ≪≫
        CondensedRing.upperStarComp Λ (g ^ n) g).hom.app M ≫
          (CondensedRing.upperStar Λ (g ^ n)).map φ.hom ≫
            (CondensedReturn.moduleIterate Λ g M φ n).hom := by
  unfold CondensedReturn.moduleIterate
  rw [iterate_succ]

private theorem paste_two {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : D ⟶ E) (c : F ⟶ G)
    (x : A ⟶ D) (y : B ⟶ E) (z : D ⟶ F) (w : E ⟶ G)
    (h₁ : a ≫ y = x ≫ b) (h₂ : b ≫ w = z ≫ c) :
    a ≫ (y ≫ w) = (x ≫ z) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

private theorem paste_map_word {C D₁ : Type*} [Category C] [Category D₁]
    (F : C ⥤ D₁) {A B E : C} {X Y Z : D₁}
    (v : A ⟶ E) (v₁ : A ⟶ B) (v₂ : B ⟶ E)
    (w : X ⟶ Z) (w₁ : X ⟶ Y) (w₂ : Y ⟶ Z)
    (a : X ⟶ F.obj A) (b : Y ⟶ F.obj B) (c : Z ⟶ F.obj E)
    (hv : v = v₁ ≫ v₂) (hw : w = w₁ ≫ w₂)
    (h₁ : a ≫ F.map v₁ = w₁ ≫ b) (h₂ : b ≫ F.map v₂ = w₂ ≫ c) :
    a ≫ F.map v = w ≫ c := by
  rw [hv, hw, F.map_comp]
  exact paste_two a b c w₁ (F.map v₁) w₂ (F.map v₂) h₁ h₂

private theorem chain_comparison {C D₁ : Type*} [Category C] [Category D₁]
    (H : C ⥤ D₁) (X : ℕ → C) (Y : ℕ → D₁) (M : C)
    (a : ∀ n, X n ⟶ M) (b : ∀ n, Y n ⟶ H.obj M)
    (c : ∀ n, X (n + 1) ⟶ X n) (d : ∀ n, Y (n + 1) ⟶ Y n)
    (τ : ∀ n, Y n ⟶ H.obj (X n))
    (ha : ∀ n, a (n + 1) = c n ≫ a n) (hb : ∀ n, b (n + 1) = d n ≫ b n)
    (hz : τ 0 ≫ H.map (a 0) = b 0)
    (hs : ∀ n, τ (n + 1) ≫ H.map (c n) = d n ≫ τ n) (n : ℕ) :
    τ n ≫ H.map (a n) = b n := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [ha n, Functor.map_comp, ← Category.assoc, hs n, Category.assoc, ih, ← hb n]

private def moduleStep {T : Scheme.{u}} (g : End T) [IsIso g]
    (K : condensedStrictWeilComplex Λ g) (j : ℤ) (n : ℕ) :
    (CondensedRing.upperStar Λ (g ^ (n + 1))).obj (cohomologyPair Λ g K j).carrier ≅
      (CondensedRing.upperStar Λ (g ^ n)).obj (cohomologyPair Λ g K j).carrier :=
  (CondensedRing.upperStarEqToIso Λ (pow_succ' g n) ≪≫
    CondensedRing.upperStarComp Λ (g ^ n) g).app (cohomologyPair Λ g K j).carrier ≪≫
      (CondensedRing.upperStar Λ (g ^ n)).mapIso (cohomologyPair Λ g K j).str

private theorem theta_step {T U V : Scheme.{u}} (f : T ⟶ V) (a : T ⟶ U)
    (b : U ⟶ V) (h : f = a ≫ b) (K : D Λ V) (K' : D Λ U) (j : ℤ)
    (φ : (L Λ b).obj K ≅ K')
    (ψ : (CondensedRing.upperStar Λ b).obj
      ((DerivedCategory.homologyFunctor _ j).obj K) ≅
        (DerivedCategory.homologyFunctor _ j).obj K')
    (hs : (theta Λ b K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map φ.hom = ψ.hom) :
    (theta Λ f K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
        ((eqToIso (congrArg (fun t ↦ (L Λ t).obj K) h) ≪≫
          (CondensedRing.leftDerivedUpperStarComp Λ a b).app K ≪≫
            (L Λ a).mapIso φ).hom) =
      (((CondensedRing.upperStarEqToIso Λ h ≪≫ CondensedRing.upperStarComp Λ a b).app
          ((DerivedCategory.homologyFunctor _ j).obj K) ≪≫
        (CondensedRing.upperStar Λ a).mapIso ψ).hom) ≫ (theta Λ a K' j).hom := by
  subst f
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    CondensedRing.upperStarEqToIso_hom_app, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [theta_comp_assoc, theta_naturality, ← Functor.map_comp_assoc, hs]

private theorem theta_step_word {T U V : Scheme.{u}} (f : T ⟶ V) (a : T ⟶ U)
    (b : U ⟶ V) (h : f = a ≫ b) (K : D Λ V) (K' : D Λ U) (j : ℤ)
    (φ : (L Λ b).obj K ≅ K')
    (ψ : (CondensedRing.upperStar Λ b).obj
      ((DerivedCategory.homologyFunctor _ j).obj K) ≅
        (DerivedCategory.homologyFunctor _ j).obj K')
    (hs : (theta Λ b K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map φ.hom = ψ.hom) :
    (theta Λ f K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
        (eqToHom (congrArg (fun t ↦ (L Λ t).obj K) h) ≫
          (CondensedRing.leftDerivedUpperStarComp Λ a b).hom.app K ≫
            (L Λ a).map φ.hom) =
      (eqToHom (congrArg
          (fun t ↦ (CondensedRing.upperStar Λ t).obj
            ((DerivedCategory.homologyFunctor _ j).obj K)) h) ≫
        (CondensedRing.upperStarComp Λ a b).hom.app
          ((DerivedCategory.homologyFunctor _ j).obj K) ≫
        (CondensedRing.upperStar Λ a).map ψ.hom) ≫ (theta Λ a K' j).hom := by
  simpa only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    CondensedRing.upperStarEqToIso_hom_app, eqToIso.hom, Functor.mapIso_hom,
    Category.assoc] using theta_step Λ f a b h K K' j φ ψ hs

private theorem moduleIterate_step {T : Scheme.{u}} (g : End T) [IsIso g]
    (K : condensedStrictWeilComplex Λ g) (j : ℤ) (n : ℕ) :
    (CondensedReturn.moduleIterate Λ g (cohomologyPair Λ g K j).carrier
      (cohomologyPair Λ g K j).str (n + 1)).hom =
      (moduleStep Λ g K j n).hom ≫
        (CondensedReturn.moduleIterate Λ g (cohomologyPair Λ g K j).carrier
          (cohomologyPair Λ g K j).str n).hom := by
  simp only [moduleStep, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  exact moduleIterate_succ Λ g (cohomologyPair Λ g K j).carrier
    (cohomologyPair Λ g K j).str n

private def inverseAt {C : Type*} [Category C] {F : C ⥤ C}
    (e : F ≅ 𝟭 C) (X : C) : X ⟶ F.obj X := (CondensedReturn.identityComponent e X).inv

private theorem inverseAt_naturality {C : Type*} [Category C] {F : C ⥤ C}
    (e : F ≅ 𝟭 C) {X Y : C} (f : X ⟶ Y) :
    f ≫ inverseAt e Y = inverseAt e X ≫ F.map f := by
  exact e.inv.naturality f

private theorem insertion_component {C D₁ : Type*} [Category C] [Category D₁]
    (F : C ⥤ C) (G : C ⥤ D₁) (e : F ≅ 𝟭 C) (X : C) :
    ((Functor.leftUnitor G).symm ≪≫ Functor.isoWhiskerRight e.symm G).hom.app X =
      G.map (inverseAt e X) := by
  simp only [inverseAt, CondensedReturn.identityComponent, Iso.trans_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, Category.id_comp]

-- Evaluate the abstract insertion formula before unfolding concrete derived functors.
private theorem insertion_map {k : Type u} [Field k] [IsAlgClosed k]
    (β : End (Spec (.of k))) (N : D Λ (Spec (.of k))) :
    (insertion Λ β).hom.app N =
      (Γ Λ (Spec (.of k))).map
        (inverseAt (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β ≪≫
          Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β) ≪≫
          Functor.mapDerivedCategoryIdIso _) N) := by
  exact insertion_component (L Λ β) (Γ Λ (Spec (.of k)))
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β ≪≫
      Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β) ≪≫
      Functor.mapDerivedCategoryIdIso _) N

private theorem inserted_map_comp {C D₁ : Type*} [Category C] [Category D₁]
    (F : C ⥤ C) (G : C ⥤ D₁) (e : F ≅ 𝟭 C) (X Y : C) (v : F.obj X ⟶ Y) :
    ((Functor.leftUnitor G).symm ≪≫ Functor.isoWhiskerRight e.symm G).hom.app X ≫
        G.map v = G.map (inverseAt e X ≫ v) := by
  rw [insertion_component, ← CategoryTheory.Functor.map_comp]

-- Keep the section functor outside the composite of the two canonical maps.
private def moduleReparamWord {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (z : Spec (.of k) ⟶ T) (β : End (Spec (.of k))) (M : Modules Λ T) :
    (CondensedRing.upperStar Λ z).obj M ⟶ (CondensedRing.upperStar Λ (β ≫ z)).obj M :=
  inverseAt (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β)
      ((CondensedRing.upperStar Λ z).obj M) ≫
    (CondensedRing.upperStarComp Λ β z).inv.app M

private theorem moduleReparam_hom {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (z : Spec (.of k) ⟶ T) (β : End (Spec (.of k))) (M : Modules Λ T) :
    (moduleReparam Λ z β M).hom =
      (sections Λ (Spec (.of k))).map (moduleReparamWord Λ z β M) := by
  rfl


private def sectionsTheta {k : Type u} [Field k] [IsAlgClosed k] (j : ℤ) :
    Γ Λ (Spec (.of k)) ⋙ CondensedReturn.scalarCohomology Λ j ≅
      DerivedCategory.homologyFunctor _ j ⋙ sections Λ (Spec (.of k)) :=
  Functor.isoWhiskerRight
      (sections Λ (Spec (.of k))).rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    ((sections Λ (Spec (.of k))).mapDerivedCategoryHomologyFunctorIso j).symm

-- Compare the concrete exact functors through their normalized natural isomorphisms.
private theorem fibre_map {k : Type u} [Field k] [IsAlgClosed k]
    {T U : Scheme.{u}} (z : Spec (.of k) ⟶ T) (z' : Spec (.of k) ⟶ U)
    (K : D Λ T) (K' : D Λ U) (j : ℤ)
    (v : (L Λ z).obj K ⟶ (L Λ z').obj K')
    (w : (CondensedRing.upperStar Λ z).obj ((DerivedCategory.homologyFunctor _ j).obj K) ⟶
      (CondensedRing.upperStar Λ z').obj ((DerivedCategory.homologyFunctor _ j).obj K'))
    (h : (theta Λ z K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map v =
      w ≫ (theta Λ z' K' j).hom) :
    (CondensedReturn.scalarCohomology Λ j).map ((Γ Λ (Spec (.of k))).map v) ≫
        (fibreComparison Λ z' K' j).hom =
      (fibreComparison Λ z K j).hom ≫ (sections Λ (Spec (.of k))).map w := by
  have hv : (DerivedCategory.homologyFunctor _ j).map v ≫ (theta Λ z' K' j).inv =
      (theta Λ z K j).inv ≫ w := by
    apply (cancel_epi (theta Λ z K j).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (CondensedReturn.scalarCohomology Λ j).map ((Γ Λ (Spec (.of k))).map v) ≫
      (sectionsTheta Λ j).hom.app ((L Λ z').obj K') ≫
        (sections Λ (Spec (.of k))).map (theta Λ z' K' j).inv =
    ((sectionsTheta Λ j).hom.app ((L Λ z).obj K) ≫
      (sections Λ (Spec (.of k))).map (theta Λ z K j).inv) ≫
        (sections Λ (Spec (.of k))).map w
  erw [← Category.assoc, (sectionsTheta Λ j).hom.naturality v]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [hv]

private theorem comparison_inverse {C D₁ : Type*} [Category C] [Category D₁]
    (H : C ⥤ D₁) (P R : C ⥤ C) (Q : D₁ ⥤ D₁)
    (e : P ≅ R) (d : R ≅ 𝟭 C) (κ : Q ≅ 𝟭 D₁) (N : C)
    (θ : Q.obj (H.obj N) ≅ H.obj (P.obj N))
    (τ : Q.obj (H.obj N) ≅ H.obj (R.obj N))
    (hθ : θ.hom ≫ H.map (e.hom.app N) = τ.hom)
    (hτ : τ.hom ≫ H.map (d.hom.app N) = κ.hom.app (H.obj N)) :
    H.map ((e ≪≫ d).inv.app N) = κ.inv.app (H.obj N) ≫ θ.hom := by
  have h : θ.hom ≫ H.map ((e ≪≫ d).hom.app N) = κ.hom.app (H.obj N) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp]
    rw [← Category.assoc, hθ, hτ]
  have hi := inverse_square (κ.app (H.obj N))
    (H.mapIso ((e ≪≫ d).app N)) θ.hom (𝟙 _)
    (by simpa only [Category.comp_id, CategoryTheory.Functor.mapIso_hom,
      Iso.app_hom] using h)
  simpa only [Category.id_comp, CategoryTheory.Functor.mapIso_inv, Iso.app_inv] using hi

private theorem exact_identity_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (I : C ⥤ C) [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (ι : I ≅ 𝟭 C) (N : DerivedCategory C) (j : ℤ) :
    (I.mapDerivedCategoryHomologyFunctorIso j).hom.app N ≫
        (DerivedCategory.homologyFunctor C j).map
          ((Functor.mapDerivedCategoryNatIso ι ≪≫
            Functor.mapDerivedCategoryIdIso C).hom.app N) =
      ι.hom.app ((DerivedCategory.homologyFunctor C j).obj N) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc,
    ← Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality,
    Category.assoc, Functor.mapDerivedCategoryHomologyFunctorIso_id_hom_app]
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id]

private theorem point_return_homology_of_iso {k : Type u} [Field k] [IsAlgClosed k]
    (β : End (Spec (.of k)))
    (κ : CondensedRing.upperStar Λ β ≅ 𝟭 (Modules Λ (Spec (.of k))))
    (N : D Λ (Spec (.of k))) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β ≪≫
          Functor.mapDerivedCategoryNatIso κ ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app N) =
      κ.inv.app
          ((DerivedCategory.homologyFunctor _ j).obj N) ≫ (theta Λ β N j).hom := by
  have hθ : (theta Λ β N j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β).hom.app N) =
      ((CondensedRing.upperStar Λ β).mapDerivedCategoryHomologyFunctorIso j).hom.app N := by
    simp [theta, Functor.leftDerivedFunctorHomologyFunctorIso,
      CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory, Category.assoc,
      ← CategoryTheory.Functor.map_comp]
  exact comparison_inverse (DerivedCategory.homologyFunctor _ j) (L Λ β)
    (CondensedRing.upperStar Λ β).mapDerivedCategory (CondensedRing.upperStar Λ β)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β)
    (Functor.mapDerivedCategoryNatIso κ ≪≫
      Functor.mapDerivedCategoryIdIso _) κ
    N (theta Λ β N j)
    (((CondensedRing.upperStar Λ β).mapDerivedCategoryHomologyFunctorIso j).app N) hθ
    (exact_identity_homology (CondensedRing.upperStar Λ β)
      κ N j)

private theorem point_return_homology {k : Type u} [Field k] [IsAlgClosed k]
    (β : End (Spec (.of k))) (N : D Λ (Spec (.of k))) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β ≪≫
          Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app N) =
      (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β).inv.app
          ((DerivedCategory.homologyFunctor _ j).obj N) ≫ (theta Λ β N j).hom := by
  exact point_return_homology_of_iso Λ β
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β) N j

-- Inverting the compositor square retains exactly the same normalized maps.
private theorem theta_comp_inv {T U V : Scheme.{u}} (f : T ⟶ U)
    (g : U ⟶ V) (K : D Λ V) (j : ℤ) :
    (CondensedRing.upperStar Λ f).map (theta Λ g K j).hom ≫
        (theta Λ f ((L Λ g).obj K) j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
          ((CondensedRing.leftDerivedUpperStarComp Λ f g).inv.app K) =
      (CondensedRing.upperStarComp Λ f g).inv.app
          ((DerivedCategory.homologyFunctor _ j).obj K) ≫ (theta Λ (f ≫ g) K j).hom := by
  simpa only [Category.assoc, CategoryTheory.Functor.mapIso_inv, Iso.app_inv] using
    (inverse_square
    ((CondensedRing.upperStarComp Λ f g).app
      ((DerivedCategory.homologyFunctor _ j).obj K))
    ((DerivedCategory.homologyFunctor _ j).mapIso
      ((CondensedRing.leftDerivedUpperStarComp Λ f g).app K))
    (theta Λ (f ≫ g) K j).hom
    ((CondensedRing.upperStar Λ f).map (theta Λ g K j).hom ≫
      (theta Λ f ((L Λ g).obj K) j).hom)
    (theta_comp Λ f g K j))

private theorem point_return_canonical {k : Type u} [Field k] [IsAlgClosed k]
    (β : End (Spec (.of k))) (N : D Λ (Spec (.of k))) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).map
      (X := N) (Y := (L Λ β).obj N)
      (inverseAt (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β ≪≫
        Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β) ≪≫
        Functor.mapDerivedCategoryIdIso _) N) =
      inverseAt (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β)
        ((DerivedCategory.homologyFunctor _ j).obj N) ≫ (theta Λ β N j).hom := by
  exact point_return_homology Λ β N j

private theorem point_paste {C : Type*} [Category C] {A B D E F G H : C}
    (θ : A ⟶ B) (q : B ⟶ D) (p : D ⟶ E)
    (kA : A ⟶ F) (kB : B ⟶ G) (v : F ⟶ G) (t : G ⟶ D)
    (c : F ⟶ H) (u : H ⟶ E)
    (hq : q = kB ≫ t) (hn : θ ≫ kB = kA ≫ v) (hc : v ≫ t ≫ p = c ≫ u) :
    θ ≫ q ≫ p = (kA ≫ c) ≫ u := by
  rw [hq]
  simp only [Category.assoc]
  rw [← Category.assoc θ kB, hn, Category.assoc, hc]

private theorem point_paste_map {C D₁ : Type*} [Category C] [Category D₁]
    (H : C ⥤ D₁) {X Y Z : C} {A F G L₁ : D₁}
    (θ : A ⟶ H.obj X) (q : X ⟶ Y) (p : Y ⟶ Z)
    (kA : A ⟶ F) (kB : H.obj X ⟶ G) (v : F ⟶ G) (t : G ⟶ H.obj Y)
    (c : F ⟶ L₁) (u : L₁ ⟶ H.obj Z)
    (hq : H.map q = kB ≫ t) (hn : θ ≫ kB = kA ≫ v)
    (hc : v ≫ t ≫ H.map p = c ≫ u) :
    θ ≫ H.map (q ≫ p) = (kA ≫ c) ≫ u := by
  rw [CategoryTheory.Functor.map_comp]
  exact point_paste θ (H.map q) (H.map p) kA kB v t c u hq hn hc

-- Naturality of the point trivialization and the inverse compositor give this square.
private theorem reparam_square {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (z : Spec (.of k) ⟶ T) (β : End (Spec (.of k)))
    (K : D Λ T) (j : ℤ) :
    (theta Λ z K j).hom ≫ (DerivedCategory.homologyFunctor _ j).map
        ((inverseAt (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ β ≪≫
          Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β) ≪≫
          Functor.mapDerivedCategoryIdIso _) ((L Λ z).obj K)) ≫
          (CondensedRing.leftDerivedUpperStarComp Λ β z).inv.app K) =
      (inverseAt (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β)
          ((CondensedRing.upperStar Λ z).obj ((DerivedCategory.homologyFunctor _ j).obj K)) ≫
        (CondensedRing.upperStarComp Λ β z).inv.app
          ((DerivedCategory.homologyFunctor _ j).obj K)) ≫ (theta Λ (β ≫ z) K j).hom := by
  have hq := point_return_canonical Λ β ((L Λ z).obj K) j
  have hn := inverseAt_naturality (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β)
    (theta Λ z K j).hom
  have hc := theta_comp_inv Λ β z K j
  exact point_paste_map (DerivedCategory.homologyFunctor _ j)
    _ _ _ _ _ _ _ _ _ hq hn hc


private theorem square_eq {C : Type*} [Category C] {A B X Y : C}
    (v v' : A ⟶ B) (w w' : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y)
    (hv : v = v') (hw : w = w') (h : v' ≫ b = a ≫ w') :
    v ≫ b = a ≫ w := by
  rw [hv, hw]
  exact h

private theorem map_square_eq {C D₁ : Type*} [Category C] [Category D₁]
    (F : C ⥤ D₁) {A B : C} {X Y : D₁}
    (v v' : A ⟶ B) (w w' : X ⟶ Y) (a : F.obj A ⟶ X) (b : F.obj B ⟶ Y)
    (hv : v = v') (hw : w = w') (h : F.map v' ≫ b = a ≫ w') :
    F.map v ≫ b = a ≫ w := by
  rw [hv, hw]
  exact h

-- Apply the scalar-sections cohomology comparison to the reparametrization square.
private theorem fibre_finite {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (z : Spec (.of k) ⟶ T) (M : Modules Λ T)
    (hM : IsConstructibleModuleObject (condensedRingObj Λ T) M) :
    Module.Finite (condensedScalarRing Λ)
      ((sections Λ (Spec (.of k))).obj ((CondensedRing.upperStar Λ z).obj M)) := by
  exact CondensedRing.constructiblePointScalarSections_finite Λ (RingHom.id _)
    Function.surjective_id k ((CondensedRing.upperStar Λ z).obj M)
      (CondensedRing.isConstructibleModuleObject_upperStar Λ z M hM)

-- Iterate the two geometric-Frobenius projections and use uniqueness of the pullback lift.
private theorem geometric_return (D₀ : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (b : End (Spec (.of D₀.k)))
    (hb : b = (letI : Fintype D₀.k₀ := Fintype.ofFinite D₀.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D₀.k₀ D₀.k).toRingHom)))
    (n : ℕ) (hn : 1 ≤ n) (x : D₀.extensionPoints Y₀ n hn)
    (ι : D₀.extensionSubfield n hn →+* D₀.k)
    (z : Spec (.of D₀.k) ⟶ (D₀.geometricFiber Y₀).left)
    (hz : z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) =
        Spec.map (CommRingCat.ofHom ι) ≫ x.left)
    (hz' : z ≫ (D₀.geometricFiber Y₀).hom = 𝟙 _) :
    z ≫ (End.of (D₀.geometricFrobenius Y₀).hom ^ n) = (b ^ n) ≫ z := by
  let : Fintype D₀.k₀ := Fintype.ofFinite D₀.k₀
  let g : End (D₀.geometricFiber Y₀).left := (D₀.geometricFrobenius Y₀).hom
  have hproj (r : ℕ) :
      (g ^ r) ≫ pullback.fst Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) =
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) ∧
      (g ^ r) ≫ (D₀.geometricFiber Y₀).hom = (D₀.geometricFiber Y₀).hom ≫ (b ^ r) := by
    have h := D₀.galoisMap_projections Y₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D₀.k₀ D₀.k)
    change g ≫ _ = _ ∧ g ≫ (D₀.geometricFiber Y₀).hom =
      (D₀.geometricFiber Y₀).hom ≫ _ at h
    rw [← hb] at h
    induction r with
    | zero =>
      constructor <;> simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
    | succ r ih =>
      simp only [pow_succ', End.mul_def, Category.assoc]
      constructor
      · rw [h.1, ih.1]
      · rw [h.2, ← Category.assoc, ih.2, Category.assoc]
  have hpoint (r : ℕ) : b ^ r =
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D₀.k₀ D₀.k ^ r).toRingHom) := by
    induction r with
    | zero =>
      change 𝟙 (Spec (.of D₀.k)) = Spec.map (𝟙 (CommRingCat.of D₀.k))
      exact (Spec.map_id _).symm
    | succ r ih =>
      rw [pow_succ', End.mul_def, ih, hb, ← Spec.map_comp]
      rfl
  have hc : Nat.card (D₀.extensionSubfield n hn) = Fintype.card D₀.k₀ ^ n := by
    have h := (FiniteField.exists_unique_subfield_of_closure D₀.p D₀.a D₀.q D₀.prime
      D₀.exponent_pos D₀.cardinality_eq D₀.k₀ D₀.card_base D₀.k n hn).choose_spec.2.1
    change Nat.card (D₀.extensionSubfield n hn) = D₀.q ^ n at h
    exact h.trans (congrArg (fun c : ℕ ↦ c ^ n)
      (D₀.card_base.symm.trans Nat.card_eq_fintype_card))
  have : Finite (D₀.extensionSubfield n hn) :=
    (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos Fintype.card_pos n)).2
  have hfixed : (b ^ n) ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom ι) := by
    rw [hpoint, ← Spec.map_comp]
    congr 1
    ext a
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
      D₀.k₀ D₀.k n hc ι a
  apply pullback.hom_ext
  · rw [Category.assoc, (hproj n).1, hz, Category.assoc, hz,
      ← Category.assoc, hfixed]
  · change (z ≫ (g ^ n)) ≫ (D₀.geometricFiber Y₀).hom =
      ((b ^ n) ≫ z) ≫ (D₀.geometricFiber Y₀).hom
    rw [Category.assoc, (hproj n).2, ← Category.assoc, hz', Category.id_comp,
      Category.assoc, hz', Category.comp_id]


-- Build congruence through the proof arguments before projecting concrete functor maps.
private meta def normalizeComparisonExpression (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let mut e := (← Lean.instantiateMVars e).consumeMData
  if let .fvar id := e then
    if let some value := (← Lean.getLCtx).get! id |>.value? then
      e := value.consumeMData
  for _ in [0:2] do
    if e.getAppFn.isConstOf ``CondensedRing.CohomologyTransport.L ||
        e.getAppFn.isConstOf ``CondensedRing.moduleObjectDerivedPullback ||
        e.getAppFn.isConstOf ``CategoryTheory.End then
      if let some value ← Lean.Meta.unfoldDefinition? e then e := value
  if e.getAppFn.isConstOf ``inferInstance then return e.getAppArgs.back!
  let carrier := e.getAppFn.isConstOf ``Endofunctor.IsoAlgebra.carrier
  let structureMap := e.getAppFn.isConstOf ``Endofunctor.IsoAlgebra.str
  if carrier || structureMap then
    let obj := e.getAppArgs.back!
    if obj.getAppFn.isConstOf ``cohomologyPair then
      if let some value ← Lean.Meta.unfoldDefinition? obj then
        let args := value.getAppArgs
        return args[args.size - (if carrier then 2 else 1)]!
  return e

private meta def proofArgumentCongruenceAux (fuel : Nat) (lhs rhs : Lean.Expr) :
    StateRefT (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr) Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => throwError "structural congruence exhausted"
  | fuel + 1 =>
    let lhs ← Lean.instantiateMVars lhs
    let rhs ← Lean.instantiateMVars rhs
    if lhs == rhs then return ← Lean.Meta.mkHEqRefl lhs
    let lhs ← normalizeComparisonExpression lhs
    let rhs ← normalizeComparisonExpression rhs
    let key := (lhs, rhs)
    if let some h := (← get).get? key then return h
    let compute : Unit →
        StateRefT (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr) Lean.MetaM Lean.Expr :=
      fun _ ↦ do
      if lhs == rhs then return ← Lean.Meta.mkHEqRefl lhs
      if let .const name _ := lhs.getAppFn then
        if let .thmInfo _ ← Lean.getConstInfo name then
          return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
      if let (.lam name domain body info, .lam _ domain' body' _) := (lhs, rhs) then
        unless ← Lean.Meta.withTransparency .default (Lean.Meta.isDefEq domain domain') do
          throwError "lambda domains differ: {domain} / {domain'}"
        return ← Lean.Meta.withLocalDecl name info domain fun x ↦ do
          let h ← proofArgumentCongruenceAux fuel (body.instantiate1 x)
            (body'.instantiate1 x) |>.run' {}
          let h ← Lean.Meta.mkAppM ``eq_of_heq #[h]
          let h ← Lean.Meta.mkLambdaFVars #[x] h
          let h ← Lean.Meta.mkAppM ``funext #[h]
          Lean.Meta.mkAppM ``heq_of_eq #[h]
      unless lhs.isApp && rhs.isApp && lhs.getAppFn == rhs.getAppFn &&
          lhs.getAppNumArgs == rhs.getAppNumArgs do
        if ← Lean.Meta.isProof lhs then
          return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
        if ← Lean.Meta.withTransparency .default (Lean.Meta.isDefEq lhs rhs) then
          return ← Lean.Meta.mkHEqRefl lhs
        throwError "structural congruence mismatch: {lhs} / {rhs}"
      let thm ← Lean.Meta.mkHCongrWithArity lhs.getAppFn lhs.getAppNumArgs
      let mut args := #[]
      for a in lhs.getAppArgs, b in rhs.getAppArgs, kind in thm.argKinds do
        let h ← proofArgumentCongruenceAux fuel a b
        match kind with
        | .eq => args := args ++ #[a, b, ← Lean.Meta.mkAppM ``eq_of_heq #[h]]
        | .heq => args := args ++ #[a, b, h]
        | _ => throwError "unexpected congruence argument"
      let h := Lean.mkAppN thm.proof args
      if (← Lean.Meta.inferType h).isHEq then return h
      return ← Lean.Meta.mkAppM ``heq_of_eq #[h]
    let h ← compute ()
    modify (·.insert key h)
    return h

private meta def proofArgumentCongruence (fuel : Nat) (lhs rhs : Lean.Expr) :
    Lean.MetaM Lean.Expr :=
  proofArgumentCongruenceAux fuel lhs rhs |>.run' {}

-- Align proposition arguments before specializing the abstract pasting lemmas.
private meta def alignProofApplication (fuel : Nat) (e : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e ← Lean.instantiateMVars e
    let head := e.getAppFn
    unless head.isConstOf ``map_square_eq || head.isConstOf ``fibre_map ||
        head.isConstOf ``paste_two || head.isConstOf ``paste_map_word ||
        head.isConstOf ``theta_step || head.isConstOf ``theta_step_word do return e
    let mut f := head
    for a in e.getAppArgs do
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType f)
      let .forallE _ domain _ _ := ty | throwError "expected a function type"
      let mut a := a
      if ← Lean.Meta.isProp domain then
        a ← alignProofApplication fuel a
        let type ← Lean.Meta.inferType a
        if type != domain then
          let h ← proofArgumentCongruence 512 type domain
          let e ← Lean.Meta.mkAppM ``eq_of_heq #[h]
          a ← Lean.Meta.mkAppM ``Eq.mp #[e, a]
      f := Lean.mkApp f a
    return f

-- Check and share proof fragments before assembling the concrete comparison.
private meta def pinComparisonProof (label : Lean.Name) (proof : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let proof ← Lean.instantiateMVars proof
  let lctx ← Lean.getLCtx
  let mut used := Lean.collectFVars (Lean.collectFVars {} proof)
    (← Lean.Meta.inferType proof)
  for id in lctx.getFVarIds.reverse do
    if used.fvarIds.contains id then
      let decl := lctx.get! id
      used := Lean.collectFVars used decl.type
      if let some value := decl.value? then used := Lean.collectFVars used value
  let args := (lctx.getFVarIds.filter used.fvarIds.contains).map Lean.mkFVar
  let value ← Lean.Meta.mkLambdaFVars args proof
  let type ← Lean.Meta.inferType value
  let name ← Lean.Meta.mkAuxLemma [`u] type value (kind? := label)
  return Lean.mkAppN (.const name [.param `u]) args

private meta def localParameterSyntax (name : Lean.Name) :
    Lean.Elab.Tactic.TacticM (Lean.TSyntax `term) := do
  for decl in ← Lean.getLCtx do
    if decl.userName.eraseMacroScopes == name then
      return ← Lean.Elab.Term.exprToSyntax decl.toExpr
  throwError "missing parameter {name}"

private theorem moduleOperator_map {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k))) (M : Modules Λ T)
    (φ : (CondensedRing.upperStar Λ g).obj M ≅ M)
    (z : Spec (.of k) ⟶ T) (n : ℕ) (h : z ≫ (g ^ n) = (b ^ n) ≫ z) :
    CondensedReturn.moduleOperator Λ g b M φ z n h =
      (sections Λ (Spec (.of k))).map
        (CondensedReturn.moduleReturnMorphism Λ (g ^ n) (b ^ n) M
          (CondensedReturn.moduleIterate Λ g M φ n) z h) := by
  unfold CondensedReturn.moduleOperator
  apply eq_of_heq
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty ← g.getType'
    let some (_, lhs, _, rhs) := ty.heq? | throwError "expected HEq"
    g.assign (← proofArgumentCongruence 512 lhs rhs)
    Lean.Elab.Tactic.replaceMainGoal []

-- Expose the two pieces that occur in the pasted point and Weil squares.
private theorem moduleReturnMorphism_eq {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (a : End T) (β : End (Spec (.of k))) (M : Modules Λ T)
    (φ : (CondensedRing.upperStar Λ a).obj M ≅ M)
    (z : Spec (.of k) ⟶ T) (h : z ≫ a = β ≫ z) :
    CondensedReturn.moduleReturnMorphism Λ a β M φ z h =
      moduleReparamWord Λ z β M ≫
        eqToHom (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) h.symm) ≫
          (CondensedRing.upperStarComp Λ z a).hom.app M ≫
            (CondensedRing.upperStar Λ z).map φ.hom := by
  unfold CondensedReturn.moduleReturnMorphism moduleReparamWord inverseAt
  conv_rhs => rw [Category.assoc]

private def derivedReturnWord {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (K : D Λ T) (φ : (L Λ g).obj K ≅ K) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) : End ((L Λ z).obj K) :=
  inverseAt (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (b ^ n) ≪≫
      Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (b ^ n)) ≪≫
      Functor.mapDerivedCategoryIdIso _) ((L Λ z).obj K) ≫
    (CondensedRing.leftDerivedUpperStarComp Λ (b ^ n) z).inv.app K ≫
      eqToHom (congrArg (fun f ↦ (L Λ f).obj K) h.symm) ≫
        (CondensedRing.leftDerivedUpperStarComp Λ z (g ^ n)).hom.app K ≫
          (L Λ z).map (CondensedReturn.derivedIterate Λ g K φ n).hom

private theorem derivedReturnWord_split {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (K : D Λ T) (φ : (L Λ g).obj K ≅ K) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) :
    derivedReturnWord Λ g b K φ z n h =
      (inverseAt (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (b ^ n) ≪≫
          Functor.mapDerivedCategoryNatIso
            (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (b ^ n)) ≪≫
          Functor.mapDerivedCategoryIdIso _) ((L Λ z).obj K) ≫
        (CondensedRing.leftDerivedUpperStarComp Λ (b ^ n) z).inv.app K) ≫
      (eqToHom (congrArg (fun f ↦ (L Λ f).obj K) h.symm) ≫
        (CondensedRing.leftDerivedUpperStarComp Λ z (g ^ n)).hom.app K ≫
          (L Λ z).map (CondensedReturn.derivedIterate Λ g K φ n).hom) := by
  unfold derivedReturnWord
  exact (Category.assoc _ _ _).symm

private theorem derivedOperator_map {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (K : D Λ T) (φ : (L Λ g).obj K ≅ K) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) :
    CondensedReturn.derivedOperator Λ g b K φ z n h =
      (Γ Λ (Spec (.of k))).map (derivedReturnWord Λ g b K φ z n h) := by
  exact inserted_map_comp (L Λ (b ^ n)) (Γ Λ (Spec (.of k)))
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (b ^ n) ≪≫
      Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (b ^ n)) ≪≫
      Functor.mapDerivedCategoryIdIso _) ((L Λ z).obj K) ((L Λ z).obj K) _

private theorem cohomologyOperator_map {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (K : D Λ T) (φ : (L Λ g).obj K ≅ K) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) (j : ℤ) :
    CondensedReturn.cohomologyOperator Λ g b K φ z n h j =
      (CondensedReturn.scalarCohomology Λ j).map
        ((Γ Λ (Spec (.of k))).map (derivedReturnWord Λ g b K φ z n h)) := by
  simpa only [CondensedReturn.cohomologyOperator] using
    (congrArg ((CondensedReturn.scalarCohomology Λ j).map)
      (derivedOperator_map Λ g b K φ z n h))

-- Keep each specified return word named while pasting its component squares.
private theorem finite_of_module_iso {R : Type*} [CommRing R]
    (M N : ModuleCat.{u + 1} R) (e : M ≅ N) (hN : Module.Finite R N) :
    Module.Finite R M := by
  have := hN
  exact Module.Finite.equiv e.toLinearEquiv.symm

-- Assemble the scalar conclusions before specializing the scheme and coefficients.
set_option maxRecDepth 4096 in
-- Normalized categorical comparisons require conversion across concrete module instances.
end WeilConjectures.CondensedLocalReturnHeart
