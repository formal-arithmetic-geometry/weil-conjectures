/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.Algebra.Homology.LeftExactHomologyComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Sheaf.Algebra.Homology.AffineKInjectiveReverseComparisonIsIso

/-! # Descent of the affine reverse comparison from K-injectives

The comparison is specified on K-injective representatives by an explicit kernel/cokernel
construction, independently of any compatibility for exact module-valued families. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
private lemma exists_reverseComparison
    {C : Type*} [Category C] [Abelian C]
    {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] (i : ℤ) :
    ∃ α : P.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D i ⟶
        DerivedCategory.homologyFunctor C i ⋙ P,
      ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
        α.app (DerivedCategory.Q.obj I) =
          (DerivedCategory.homologyFunctor D i).map (P.rightDerivedFunctorObjQIso I).hom ≫
          ((DerivedCategory.homologyFunctorFactors D i).app
            ((P.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          (I.sc i).leftExactHomologyComparison P ≫
          P.map (((DerivedCategory.homologyFunctorFactors C i).app I).inv) := by
  let κ := CochainComplex.KInjectives.ι (C := C)
  let L := κ ⋙ DerivedCategory.Q
  let H := DerivedCategory.homologyFunctor D i
  let F := P.rightDerivedFunctor ⋙ H
  let G := DerivedCategory.homologyFunctor C i ⋙ P
  let β : P.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ P.rightDerivedFunctor :=
    (Functor.isoWhiskerLeft (P.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      P.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      P.rightDerivedFunctor).hom
  have hβ : IsIso (Functor.whiskerLeft κ β) := by
    have (I : CochainComplex.KInjectives C) : IsIso ((Functor.whiskerLeft κ β).app I) := by
      have : I.obj.IsKInjective := I.property
      dsimp [β, κ]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let γ : P.mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) i ⟶
      HomologicalComplex.homologyFunctor C (.up ℤ) i ⋙ P :=
    { app := fun I ↦ (I.sc i).leftExactHomologyComparison P
      naturality := fun I J f ↦
        ShortComplex.leftExactHomologyComparison_naturality
          ((HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map f) P }
  let δ : L ⋙ F ⟶ L ⋙ G :=
    Functor.whiskerRight (asIso (Functor.whiskerLeft κ β)).inv H ≫
    Functor.whiskerLeft (κ ⋙ P.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.homologyFunctorFactors D i).hom ≫
    Functor.whiskerLeft κ γ ≫
    Functor.whiskerLeft κ (Functor.whiskerRight (DerivedCategory.homologyFunctorFactors C i).inv P)
  let ff := Localization.fullyFaithfulWhiskeringLeft L
    (CochainComplex.KInjectives.quasiIso C) D
  refine ⟨ff.preimage δ, ?_⟩
  intro I hI
  have he := congr_app (ff.map_preimage δ) (CochainComplex.KInjectives.mk I)
  change (ff.preimage δ).app (DerivedCategory.Q.obj I) = _ at he
  rw [he]
  dsimp only [δ, NatTrans.comp_app, Functor.whiskerRight_app, asIso_inv]
  rw [NatIso.isIso_inv_app]
  dsimp [β, γ, κ, L, F, G, H, Functor.rightDerivedFunctorObjQIso]
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    NatIso.inv_inv_app, Functor.map_comp, Category.assoc]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Direct image preserves finite limits: it is the sheaf module pushforward,
a right adjoint. Source: Stacks Project, Tag 079V. -/
instance affineEdge_moduleDirectImage_preservesFiniteLimits {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) : PreservesFiniteLimits (RingedSpace.moduleDirectImage g) := by
  dsimp [RingedSpace.moduleDirectImage]
  infer_instance

/-- Reverse comparison on a K-injective complex: compute derived direct image by
its unit, compare cohomology of termwise pushforward to pushforward of cohomology,
and transport back through the localization/homology comparison.
Source: Stacks Project, Tag 0AVW, cohomology display in the proof. -/
def affineKInjectiveReverseComparison
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    [I.IsKInjective] :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
      ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).obj
        (DerivedCategory.Q.obj I)) ⟶
    (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj I)) := by
  let P := RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  exact H.map (P.rightDerivedFunctorObjQIso I).hom ≫
    ((DerivedCategory.homologyFunctorFactors _ i).app
      ((P.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
    (I.sc i).leftExactHomologyComparison P ≫
    P.map (((DerivedCategory.homologyFunctorFactors _ i).app I).inv)

private lemma reverseComparison_ext (X : Scheme.{u})
    {D : Type*} [Category D]
    {F G : schemeDerivedQCohCategory X ⥤ D} (α β : F ⟶ G)
    (h : ∀ (I : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) [I.IsKInjective]
        (hI : schemeDerivedQCohProperty X (DerivedCategory.Q.obj I)),
        α.app ⟨_, hI⟩ = β.app ⟨_, hI⟩) : α = β := by
  ext M
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M.obj
  let := hI
  have hq : schemeDerivedQCohProperty X (DerivedCategory.Q.obj I) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (M.property n)
  let e' : M ≅ ⟨_, hq⟩ := (schemeDerivedQCohProperty X).isoMk e
  apply (cancel_mono (G.map e'.hom)).1
  rw [← α.naturality, ← β.naturality, h I hq]

/-- The explicit reverse comparisons on K-injectives descend to a unique natural
isomorphism on the quasi-coherent derived category.
Source: Stacks Project, Tags 0AVW (affine cohomology display), 08D4 (bound one),
and localization by K-injective resolutions.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge-descent).

Proof: Pushforward preserves kernels, so the displayed kernel lift followed by the
mapped cycle-class projection annihilates boundaries. It therefore descends through
homology. Kernel and cokernel universal properties prove naturality for chain maps;
homotopic maps have the same homology map, so it is natural on the K-injective homotopy
category. On every affine open of Spec B, its inverse image is affine, and sections
have cohomological bound one on quasi-coherent sheaves. Tag 08D4 removes both tails;
the resulting degree-i cycle-class comparison is exactly the displayed reverse map.
Affine vanishing makes it invertible on that basis, hence on sheaves. K-injectives
with quasi-coherent cohomology localize equivalently to D_QCoh: transport the natural
comparison along this equivalence and the right-derived-unit isomorphism to obtain
τ. Every object admits such a representative, so naturality with the representative
isomorphism determines every component of τ. Thus τ is unique, including its inverse.
No exact functor F or compatibility equation from the component theorem is used. -/
theorem existsUnique_affineDerivedPushforwardReverseComparison
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    ∃! τ : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
        RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom,
      ∀ (I : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        [I.IsKInjective]
        (hI : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj I)),
        τ.hom.app ⟨_, hI⟩ = affineKInjectiveReverseComparison A B φ i I := by
  let X := Spec (.of A)
  let P := RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  obtain ⟨α, hα⟩ := exists_reverseComparison P i
  let β := Functor.whiskerLeft (schemeDerivedQCohProperty X).ι α
  have hβ (I : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) [I.IsKInjective]
      (hI : schemeDerivedQCohProperty X (DerivedCategory.Q.obj I)) :
      β.app ⟨_, hI⟩ = affineKInjectiveReverseComparison A B φ i I := hα I
  have hi : ∀ M, IsIso (β.app M) := by
    intro M
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M.obj
    let := hI
    have hq : schemeDerivedQCohProperty X (DerivedCategory.Q.obj I) := by
      intro n
      exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (M.property n)
    have hc := affineKInjective_leftExactHomologyComparison_isIso A B φ i I hq
    have : IsIso (β.app ⟨_, hq⟩) := by
      rw [hβ I hq]
      dsimp only [affineKInjectiveReverseComparison]
      infer_instance
    exact (NatTrans.isIso_app_iff_of_iso β ((schemeDerivedQCohProperty X).isoMk e)).mpr
      this
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, hβ, ?_⟩
  intro τ hτ
  apply Iso.ext
  exact reverseComparison_ext X τ.hom β (fun I _ hI ↦ (hτ I hI).trans (hβ I hI).symm)
end AlgebraicGeometry
