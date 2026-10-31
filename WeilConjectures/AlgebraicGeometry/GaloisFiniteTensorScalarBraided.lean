/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisLisseCorrespondenceData
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-! # Braided tensor component of the finite Galois comparison

Source: Stacks Project, Tag 0DV5 (3), and the blueprint `cor-galois-lisse-representations`,
proof steps 4 and 5 (blueprint: new-d9-galois-finite-tensor-scalar-braided). -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open MonoidalCategory
open scoped TensorProduct FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

noncomputable section

private noncomputable def galoisUnderlyingStalkIso
    {Y : Scheme.{u}} (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (galoisUnderlyingSetSheaf R F) ≅
      (CategoryTheory.forget (ModuleCat.{u + 1} R)).obj
        (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((pointSmallEtale y).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F

-- Relate the module and underlying-set notions of finite local constancy.
private theorem galoisLisse_iff_finiteLocallyConstant
    {Y : Scheme.{u}} (R : Type (u + 1)) [Ring R] [Finite R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsLisseModuleSheaf F ↔ IsFiniteLocallyConstantSheaf F := by
  constructor
  · intro hF
    have hU := (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mp hF
    refine { toIsLocallyConstantSheaf := ?_, toIsFiniteSheaf := ?_ }
    · obtain ⟨𝒰, h𝒰⟩ := hF
      exact ⟨⟨⟨𝒰, fun i ↦ by
        obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
        exact Sheaf.isConstant_of_iso _ e⟩⟩⟩
    · refine ⟨fun Ω _ _ y ↦ ?_⟩
      have : Finite (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf R F)) := hU.finite_sheafFiber Ω y
      have : Finite (((pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R)).obj F) :=
        Finite.of_equiv _ (galoisUnderlyingStalkIso R F y).toEquiv
      exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite)
  · intro hF
    have := hF
    apply (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mpr
    apply isFiniteLocallyConstantSheafOfTypes_of_finite_sheafFiber
    · obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
      refine ⟨d.cover, fun i ↦ ?_⟩
      have := d.isConstant i
      change ((sheafCompose (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj
          (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
      infer_instance
    · intro Ω _ _ y
      have := (ModuleCat.isFinitelyGenerated_iff _).mp
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) Ω y)
      have : Finite (((pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R)).obj F) := Module.finite_of_finite R
      exact Finite.of_equiv _ (galoisUnderlyingStalkIso R F y).toEquiv.symm

section Stalk

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) {R : Type (u + 1)} [CommRing R]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- The canonical tensorator, expressed before sheafification.
private theorem tensor_stalk_tensorator
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (let p := pointSmallEtale y
    letI := (sheafificationAdjunction Y.smallEtaleTopology
      (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ p.sheafFiber F G =
      Functor.LaxMonoidal.μ p.presheafFiber F.obj G.obj ≫
        p.presheafFiber.map (Functor.LaxMonoidal.μ
          (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F G)) := by
  dsimp only
  let p := pointSmallEtale y
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} R
  let L := presheafToSheaf J A
  let T := p.sheafFiber (A := A)
  let e := p.presheafToSheafCompSheafFiberIso A
  let adj := sheafificationAdjunction J A
  let := adj.rightAdjointLaxMonoidal
  -- Compare through sheafification, then cancel its monoidal structure maps.
  have ht := NatTrans.IsMonoidal.tensor (τ := e.inv) F.obj G.obj
  dsimp only [Functor.comp_obj] at ht
  have he (H : Sheaf J A) :
      e.inv.app H.obj ≫ T.map (adj.counit.app H) = 𝟙 (T.obj H) := by
    change p.presheafFiber.map (adj.unit.app H.obj) ≫
      p.presheafFiber.map ((sheafToPresheaf J A).map (adj.counit.app H)) = 𝟙 _
    rw [← Functor.map_comp]
    have h := congrArg (fun k ↦ p.presheafFiber.map k) (adj.right_triangle_components H)
    simpa only [sheafToPresheaf, ObjectProperty.ι_obj, CategoryTheory.Functor.map_id,
      Functor.id_obj] using h
  have hm : p.presheafFiber.map (Functor.LaxMonoidal.μ
      (sheafToPresheaf J A) F G) =
      e.inv.app (F.obj ⊗ G.obj) ≫
        T.map (Functor.OplaxMonoidal.δ L F.obj G.obj) ≫
          T.map (adj.counit.app F ⊗ₘ adj.counit.app G) := by
    rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_apply]
    simp only [Functor.map_comp]
    rfl
  rw [hm, ← Category.assoc, ht]
  simp only [Functor.LaxMonoidal.comp_μ, Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.LaxMonoidal.μ_natural]
  rw [tensorHom_comp_tensorHom_assoc]
  change Functor.LaxMonoidal.μ T F G =
    ((e.inv.app F.obj ≫ T.map (adj.counit.app F)) ⊗ₘ
      (e.inv.app G.obj ≫ T.map (adj.counit.app G))) ≫ Functor.LaxMonoidal.μ T F G
  rw [he, he]
  exact ((congrArg (fun k ↦ k ≫ Functor.LaxMonoidal.μ T F G)
    (id_tensorHom_id (T.obj F) (T.obj G))).trans (Category.id_comp _)).symm

private theorem tensor_stalk_germ
    (F H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) :
    (let p := pointSmallEtale y
    (p.toPresheafFiber U x F.obj ⊗ₘ p.toPresheafFiber U x H.obj) ≫
      Functor.LaxMonoidal.μ p.sheafFiber F H =
    (Functor.LaxMonoidal.μ (sheafToPresheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} R)) F H).app (op U) ≫
      p.toPresheafFiber U x (F ⊗ H).obj) := by
  dsimp only
  rw [tensor_stalk_tensorator y]
  rw [← Category.assoc, (pointSmallEtale y).tensorHom_comp_toPresheafFiber_μ]
  exact (pointSmallEtale y).toPresheafFiber_naturality _ U x

@[instance_reducible]
private noncomputable def tensor_stalk_braided :
    ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).Braided := by
  let p := pointSmallEtale y
  let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
  refine { braided := ?_ }
  intro F H
  symm
  apply ((p.isColimitPresheafFiberCocone F.obj).tensor
    (p.isColimitPresheafFiberCocone H.obj)).hom_ext
  rintro ⟨⟨U, x⟩⟩
  change (p.toPresheafFiber U x F.obj ⊗ₘ p.toPresheafFiber U x H.obj) ≫
      (β_ (T.obj F) (T.obj H)).hom ≫ Functor.LaxMonoidal.μ T H F =
    (p.toPresheafFiber U x F.obj ⊗ₘ p.toPresheafFiber U x H.obj) ≫
      Functor.LaxMonoidal.μ T F H ≫ T.map (β_ F H).hom
  erw [BraidedCategory.braiding_naturality_assoc]
  erw [tensor_stalk_germ y H F U x]
  erw [reassoc_of% (tensor_stalk_germ y F H U x)]
  change _ = _ ≫ p.toPresheafFiber U x (F ⊗ H).obj ≫
    p.presheafFiber.map (β_ F H).hom.hom
  erw [p.toPresheafFiber_naturality]
  have h := NatTrans.congr_app
    (Functor.LaxBraided.braided
      (F := sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F H) (op U)
  change (Functor.LaxMonoidal.μ
      (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F H).app (op U) ≫
      (β_ F H).hom.hom.app (op U) =
    (β_ (F.obj.obj (op U)) (H.obj.obj (op U))).hom ≫
      (Functor.LaxMonoidal.μ
        (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) H F).app (op U) at h
  simpa only [← Category.assoc] using
    congrArg (fun f ↦ f ≫ p.toPresheafFiber U x (H ⊗ F).obj) h.symm

end Stalk

-- Coherence lifts once the structure isomorphisms intertwine the actions.
private theorem rep_braided_lift
    {C : Type v} [Category.{w} C] [MonoidalCategory C] [BraidedCategory C]
    {R : Type (u + 1)} [CommRing R] {G : Type u} [Group G]
    (F : C ⥤ Rep.{u + 1} R G)
    [hB : (F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)).Braided]
    (hε : ∀ g z, (Functor.LaxMonoidal.ε
      (F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R))) z =
        (F.obj (𝟙_ C)).ρ g ((Functor.LaxMonoidal.ε
          (F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R))) z))
    (hμ : ∀ (X Y : C) g (z : (F.obj X).V ⊗[R] (F.obj Y).V),
      (Functor.LaxMonoidal.μ
        (F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)) X Y)
          (((F.obj X ⊗ F.obj Y).ρ g) z) =
      (F.obj (X ⊗ Y)).ρ g ((Functor.LaxMonoidal.μ
        (F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)) X Y) z)) :
    Nonempty F.Braided := by
  let K := F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)
  let e : 𝟙_ (Rep.{u + 1} R G) ≅ F.obj (𝟙_ C) :=
    Rep.mkIso { (Functor.Monoidal.εIso K).toLinearEquiv with
      isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ hε g z) }
  let t (X Y : C) : (F.obj X ⊗ F.obj Y : Rep.{u + 1} R G) ≅ F.obj (X ⊗ Y) :=
    Rep.mkIso { (Functor.Monoidal.μIso K X Y).toLinearEquiv with
      isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ hμ X Y g z) }
  let c : F.CoreMonoidal :=
    { εIso := e
      μIso := t
      μIso_hom_natural_left := by
        intro X Y f Z
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        exact congrArg ModuleCat.Hom.hom (Functor.LaxMonoidal.μ_natural_left K f Z)
      μIso_hom_natural_right := by
        intro X Y Z f
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        exact congrArg ModuleCat.Hom.hom (Functor.LaxMonoidal.μ_natural_right K Z f)
      associativity := by
        intro X Y Z
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        exact congrArg ModuleCat.Hom.hom (Functor.LaxMonoidal.associativity K X Y Z)
      left_unitality := by
        intro X
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        exact congrArg ModuleCat.Hom.hom (Functor.LaxMonoidal.left_unitality K X)
      right_unitality := by
        intro X
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        exact congrArg ModuleCat.Hom.hom (Functor.LaxMonoidal.right_unitality K X) }
  let : F.Monoidal := c.toMonoidal
  refine ⟨{ braided := ?_ }⟩
  intro X Y
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg ModuleCat.Hom.hom (Functor.LaxBraided.braided (F := K) X Y)

-- Naturality of the action on finite locally constant sets, expressed in module stalks.
private theorem galois_set_map_equivariant
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) (heval : galoisFiniteEvaluationAction y G d)
    (R : Type (u + 1)) [Ring R] [Finite R]
    (F H : LisseModuleSheafCategory Y R)
    (f : galoisUnderlyingSetSheaf R F.obj ⟶ galoisUnderlyingSetSheaf R H.obj)
    (φ : ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj →
      ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj H.obj)
    (hφ : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
      (s : F.obj.obj.obj (op U)),
      φ ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x H.obj.obj (f.hom.app (op U) s))
    (g : G) (z : ((d.e R).functor.obj F).obj.V) :
    φ ((d.τ R).hom.app F (((d.e R).functor.obj F).obj.ρ g z)) =
      (d.τ R).hom.app H (((d.e R).functor.obj H).obj.ρ g
        ((d.τ R).inv.app H (φ ((d.τ R).hom.app F z)))) := by
  classical
  let p := pointSmallEtale y
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨hF, κF, hgF, haF⟩ := heval R F
  obtain ⟨hH, κH, hgH, haH⟩ := heval R H
  have hn (w : (p.sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) :
      κH (φ w) = p.sheafFiber.map f (κF w) := by
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := F.obj.obj) w
    rw [hφ, hgH, hgF]
    exact (ConcreteCategory.congr_hom (p.toPresheafFiber_naturality f.hom U x) s).symm
  have hi (w) : (d.τ R).hom.app H ((d.τ R).inv.app H w) = w :=
    ConcreteCategory.congr_hom ((d.τ R).inv_hom_id_app H) w
  apply κH.injective
  rw [hn, haF, haH, hi, hn]
  exact (ConcreteCategory.congr_hom
    ((d.γ g).hom.naturality
      (ObjectProperty.homMk (X := galoisUnderlyingFLC R F.obj hF)
        (Y := galoisUnderlyingFLC R H.obj hH) f)) (κF ((d.τ R).hom.app F z))).symm


-- A bilinear pairing is a set-sheaf map on the biproduct of its inputs.
private theorem galois_pairing_equivariant
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) (heval : galoisFiniteEvaluationAction y G d)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (F H K : LisseModuleSheafCategory Y R)
    (ν : F.obj.obj ⊗ H.obj.obj ⟶ K.obj.obj)
    (β : ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj ⊗
      ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj H.obj ⟶
      ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj K.obj)
    (hβ : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U),
      ((pointSmallEtale y).toPresheafFiber U x F.obj.obj ⊗ₘ
        (pointSmallEtale y).toPresheafFiber U x H.obj.obj) ≫ β =
      ν.app (op U) ≫ (pointSmallEtale y).toPresheafFiber U x K.obj.obj)
    (g : G) (a : ((d.e R).functor.obj F).obj.V)
    (b : ((d.e R).functor.obj H).obj.V) :
    β ((d.τ R).hom.app F (((d.e R).functor.obj F).obj.ρ g a) ⊗ₜ[R]
      (d.τ R).hom.app H (((d.e R).functor.obj H).obj.ρ g b)) =
    (d.τ R).hom.app K (((d.e R).functor.obj K).obj.ρ g
      ((d.τ R).inv.app K (β ((d.τ R).hom.app F a ⊗ₜ[R]
        (d.τ R).hom.app H b)))) := by
  classical
  let T := (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)
  let : T.Additive := (pointSmallEtale y).sheafFiber_additive
  have hF := (galoisLisse_iff_finiteLocallyConstant R F.obj).mp F.property
  have hH := (galoisLisse_iff_finiteLocallyConstant R H.obj).mp H.property
  let := hF
  let := hH
  let P : LisseModuleSheafCategory Y R :=
    ⟨biprod F.obj H.obj, (galoisLisse_iff_finiteLocallyConstant R _).mpr
      (IsFiniteLocallyConstantSheaf.biprod F.obj H.obj)⟩
  let π₁ : P ⟶ F := ObjectProperty.homMk biprod.fst
  let π₂ : P ⟶ H := ObjectProperty.homMk biprod.snd
  let ι₁ : F.obj ⟶ P.obj := biprod.inl
  let ι₂ : H.obj ⟶ P.obj := biprod.inr
  let q (w : T.obj P.obj) := β (T.map π₁.hom w ⊗ₜ[R] T.map π₂.hom w)
  let f : galoisUnderlyingSetSheaf R P.obj ⟶ galoisUnderlyingSetSheaf R K.obj :=
    ⟨{ app := fun U ↦ ↾fun z ↦ ν.app U
        (π₁.hom.hom.app U z ⊗ₜ[R] π₂.hom.hom.app U z)
       naturality := by
         intro U V i
         ext z
         have hn := ConcreteCategory.congr_hom (ν.naturality i)
           (π₁.hom.hom.app U z ⊗ₜ[R] π₂.hom.hom.app U z)
         have h₁ := ConcreteCategory.congr_hom (π₁.hom.hom.naturality i) z
         have h₂ := ConcreteCategory.congr_hom (π₂.hom.hom.naturality i) z
         change π₁.hom.hom.app V (P.obj.obj.map i z) =
           F.obj.obj.map i (π₁.hom.hom.app U z) at h₁
         change π₂.hom.hom.app V (P.obj.obj.map i z) =
           H.obj.obj.map i (π₂.hom.hom.app U z) at h₂
         change ν.app V (π₁.hom.hom.app V (P.obj.obj.map i z) ⊗ₜ[R]
           π₂.hom.hom.app V (P.obj.obj.map i z)) = K.obj.obj.map i
             (ν.app U (π₁.hom.hom.app U z ⊗ₜ[R] π₂.hom.hom.app U z))
         rw [h₁, h₂]
         exact hn }⟩
  have hq (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
      (s : P.obj.obj.obj (op U)) :
      q ((pointSmallEtale y).toPresheafFiber U x P.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x K.obj.obj (f.hom.app (op U) s) := by
    dsimp only [q]
    have h₁ := ConcreteCategory.congr_hom
      ((pointSmallEtale y).toPresheafFiber_naturality π₁.hom.hom U x) s
    have h₂ := ConcreteCategory.congr_hom
      ((pointSmallEtale y).toPresheafFiber_naturality π₂.hom.hom U x) s
    change T.map π₁.hom ((pointSmallEtale y).toPresheafFiber U x P.obj.obj s) =
      (pointSmallEtale y).toPresheafFiber U x F.obj.obj (π₁.hom.hom.app (op U) s) at h₁
    change T.map π₂.hom ((pointSmallEtale y).toPresheafFiber U x P.obj.obj s) =
      (pointSmallEtale y).toPresheafFiber U x H.obj.obj (π₂.hom.hom.app (op U) s) at h₂
    rw [h₁, h₂]
    exact ConcreteCategory.congr_hom (hβ U x)
      (π₁.hom.hom.app (op U) s ⊗ₜ[R] π₂.hom.hom.app (op U) s)
  let w : T.obj P.obj := T.map ι₁ ((d.τ R).hom.app F a) +
    T.map ι₂ ((d.τ R).hom.app H b)
  have hw₁ : T.map π₁.hom w = (d.τ R).hom.app F a := by
    have h₁ : T.map ι₁ ≫ T.map π₁.hom = 𝟙 (T.obj F.obj) := by
      rw [← T.map_comp]
      change T.map ((biprod.inl : F.obj ⟶ F.obj ⊞ H.obj) ≫ biprod.fst) = _
      rw [biprod.inl_fst, T.map_id]
    have h₂ : T.map ι₂ ≫ T.map π₁.hom = 0 := by
      rw [← T.map_comp]
      change T.map ((biprod.inr : H.obj ⟶ F.obj ⊞ H.obj) ≫ biprod.fst) = _
      rw [biprod.inr_fst, T.map_zero]
    dsimp only [w]
    rw [map_add]
    have h₁' := ConcreteCategory.congr_hom h₁ ((d.τ R).hom.app F a)
    have h₂' := ConcreteCategory.congr_hom h₂ ((d.τ R).hom.app H b)
    change T.map π₁.hom (T.map ι₁ ((d.τ R).hom.app F a)) = _ at h₁'
    change T.map π₁.hom (T.map ι₂ ((d.τ R).hom.app H b)) = 0 at h₂'
    rw [h₁', h₂', add_zero]
    rfl
  have hw₂ : T.map π₂.hom w = (d.τ R).hom.app H b := by
    have h₁ : T.map ι₁ ≫ T.map π₂.hom = 0 := by
      rw [← T.map_comp]
      change T.map ((biprod.inl : F.obj ⟶ F.obj ⊞ H.obj) ≫ biprod.snd) = _
      rw [biprod.inl_snd, T.map_zero]
    have h₂ : T.map ι₂ ≫ T.map π₂.hom = 𝟙 (T.obj H.obj) := by
      rw [← T.map_comp]
      change T.map ((biprod.inr : H.obj ⟶ F.obj ⊞ H.obj) ≫ biprod.snd) = _
      rw [biprod.inr_snd, T.map_id]
    dsimp only [w]
    rw [map_add]
    have h₁' := ConcreteCategory.congr_hom h₁ ((d.τ R).hom.app F a)
    have h₂' := ConcreteCategory.congr_hom h₂ ((d.τ R).hom.app H b)
    change T.map π₂.hom (T.map ι₁ ((d.τ R).hom.app F a)) = 0 at h₁'
    change T.map π₂.hom (T.map ι₂ ((d.τ R).hom.app H b)) = _ at h₂'
    rw [h₁', h₂', zero_add]
    rfl
  let z := (d.τ R).inv.app P w
  have hz : (d.τ R).hom.app P z = w :=
    ConcreteCategory.congr_hom ((d.τ R).inv_hom_id_app P) w
  have hz₁ : ((d.e R).functor.map π₁).hom.hom z = a := by
    apply ((d.τ R).app F).toLinearEquiv.injective
    change (d.τ R).hom.app F (((d.e R).functor.map π₁).hom.hom z) =
      (d.τ R).hom.app F a
    have hn := ConcreteCategory.congr_hom ((d.τ R).hom.naturality π₁) z
    change (d.τ R).hom.app F (((d.e R).functor.map π₁).hom.hom z) =
      T.map π₁.hom ((d.τ R).hom.app P z) at hn
    rw [hn, hz, hw₁]
  have hz₂ : ((d.e R).functor.map π₂).hom.hom z = b := by
    apply ((d.τ R).app H).toLinearEquiv.injective
    change (d.τ R).hom.app H (((d.e R).functor.map π₂).hom.hom z) =
      (d.τ R).hom.app H b
    have hn := ConcreteCategory.congr_hom ((d.τ R).hom.naturality π₂) z
    change (d.τ R).hom.app H (((d.e R).functor.map π₂).hom.hom z) =
      T.map π₂.hom ((d.τ R).hom.app P z) at hn
    rw [hn, hz, hw₂]
  have hn₁ : T.map π₁.hom ((d.τ R).hom.app P
      (((d.e R).functor.obj P).obj.ρ g z)) =
      (d.τ R).hom.app F (((d.e R).functor.obj F).obj.ρ g a) := by
    have hn := ConcreteCategory.congr_hom ((d.τ R).hom.naturality π₁)
      (((d.e R).functor.obj P).obj.ρ g z)
    change (d.τ R).hom.app F (((d.e R).functor.map π₁).hom.hom
      (((d.e R).functor.obj P).obj.ρ g z)) =
      T.map π₁.hom ((d.τ R).hom.app P (((d.e R).functor.obj P).obj.ρ g z)) at hn
    rw [← hn, (Representation.IntertwiningMap.isIntertwining _ _
      ((d.e R).functor.map π₁).hom.hom g z), hz₁]
  have hn₂ : T.map π₂.hom ((d.τ R).hom.app P
      (((d.e R).functor.obj P).obj.ρ g z)) =
      (d.τ R).hom.app H (((d.e R).functor.obj H).obj.ρ g b) := by
    have hn := ConcreteCategory.congr_hom ((d.τ R).hom.naturality π₂)
      (((d.e R).functor.obj P).obj.ρ g z)
    change (d.τ R).hom.app H (((d.e R).functor.map π₂).hom.hom
      (((d.e R).functor.obj P).obj.ρ g z)) =
      T.map π₂.hom ((d.τ R).hom.app P (((d.e R).functor.obj P).obj.ρ g z)) at hn
    rw [← hn, (Representation.IntertwiningMap.isIntertwining _ _
      ((d.e R).functor.map π₂).hom.hom g z), hz₂]
  have h := galois_set_map_equivariant y G d heval R P K f q hq g z
  dsimp only [q] at h
  rw [hn₁, hn₂, hz, hw₁, hw₂] at h
  exact h

/-- Braided tensor part of the finite Galois comparison: for finite commutative `R`, every
braided monoidal structure on the lisse `R`-module sheaves whose inclusion into all sheaves
is braided makes the representation functor `(d.e R).functor ⋙ ι` braided.
Source: Stacks Project, Tag 0DV5 (3); the blueprint, `cor-galois-lisse-representations`,
proof paragraphs "Naturality of the action" and "Tensor products".
(blueprint: new-d9-galois-finite-tensor-scalar-braided).

Proof: over finite `R`, lisse module sheaves are the finite locally constant ones, so the
biproduct of two lisse sheaves is lisse. The canonical strong monoidal structure of the
geometric-point stalk functor sends two germs to the germ of their sectionwise tensor
(compare with the presheaf stalk through the sheafification adjunction); this formula
and the lax braided sheaf-to-presheaf functor make it braided. Compose the given braided
inclusion with it and transport the result through `d.τ` to the module-valued
representation functor. A point `σ ∈ G` acts by natural automorphisms of the fibre
functor on finite locally constant sheaves of sets (`heval` identifies the action of `d`
on germs with this evaluation action), so any stalk map induced on germs by a map of
underlying set sheaves is equivariant. A bilinear pairing `F ⊗ H → K` is such a map on
the underlying set sheaf of the lisse biproduct `F ⊞ H`; taking the stalk element with
projections `τ a` and `τ b` gives equivariance of the tensorator on pure tensors, hence
on all tensors. The tensor unit is the constant sheaf, whose stalk is the trivial
representation by `hunit`. The equivariant unit and tensor isomorphisms lift to
representations, and every coherence equation, including the braiding, holds there
because it holds on underlying modules. -/
theorem galois_finite_tensor_scalar_braided
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (d : GaloisLisseFiniteData y G)
    (heval : galoisFiniteEvaluationAction y G d) (hunit : galoisFiniteUnit y G d)
    :     (∀ (R : Type (u + 1)) [CommRing R] [Finite R]
      (m : MonoidalCategory (LisseModuleSheafCategory Y R))
      (b : @BraidedCategory (LisseModuleSheafCategory Y R) _ m),
      Nonempty (@Functor.Braided (LisseModuleSheafCategory Y R) _ m b
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) _
        (Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (Sheaf.braidedCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (ObjectProperty.ι _)) →
      Nonempty (@Functor.Braided (LisseModuleSheafCategory Y R) _ m b
        (Rep.{u + 1} R G) _ _ _ ((d.e R).functor ⋙ ObjectProperty.ι _))) := by
  intro R _ _ m b hI
  let := m
  let := b
  let := Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  let := Sheaf.braidedCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  let I := ObjectProperty.ι (IsLisseModuleSheaf (Y := Y) (Λ := R))
  let : I.Braided := hI.some
  let T := (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)
  let : T.Braided := tensor_stalk_braided y (R := R)
  let E := (d.e R).functor ⋙ ObjectProperty.ι _
  let K := I ⋙ T
  let K₀ := E ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)
  let τ : K₀ ≅ K := d.τ R
  let : K₀.Monoidal := Functor.Monoidal.transport τ.symm
  let : NatTrans.IsMonoidal τ.symm.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport τ.symm
  let hK : K₀.LaxBraided := Functor.LaxBraided.ofNatIso τ.symm
  let : K₀.Braided := { toMonoidal := inferInstance, braided := hK.braided }
  apply rep_braided_lift E
  · intro g z
    obtain ⟨C, hC, ⟨eC⟩⟩ := hunit R
    let eCI : C ≅ 𝟙_ (LisseModuleSheafCategory Y R) := ObjectProperty.isoMk _
      (eqToIso hC ≪≫ Functor.Monoidal.εIso I)
    let eU : E.obj (𝟙_ (LisseModuleSheafCategory Y R)) ≅ Rep.trivial R G R :=
      E.mapIso eCI.symm ≪≫ eC
    have hf (x : (E.obj (𝟙_ (LisseModuleSheafCategory Y R))).V) :
        (E.obj (𝟙_ (LisseModuleSheafCategory Y R))).ρ g x = x := by
      let eV := (forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)).mapIso eU
      apply eV.toLinearEquiv.injective
      exact Representation.IntertwiningMap.isIntertwining _ _ eU.hom.hom g x
    exact (hf _).symm
  · intro X Z g z
    have hμ (a : (E.obj X).V) (b : (E.obj Z).V) :
        Functor.LaxMonoidal.μ K₀ X Z (a ⊗ₜ[R] b) =
          (d.τ R).inv.app (X ⊗ Z)
            (Functor.LaxMonoidal.μ K X Z
              ((d.τ R).hom.app X a ⊗ₜ[R] (d.τ R).hom.app Z b)) := by
      erw [Functor.Monoidal.transport_μ τ.symm]
      rfl
    let ν : X.obj.obj ⊗ Z.obj.obj ⟶ (X ⊗ Z).obj.obj :=
      Functor.LaxMonoidal.μ (sheafToPresheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} R)) X.obj Z.obj ≫ (Functor.LaxMonoidal.μ I X Z).hom
    have hν (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) :
        ((pointSmallEtale y).toPresheafFiber U x X.obj.obj ⊗ₘ
          (pointSmallEtale y).toPresheafFiber U x Z.obj.obj) ≫
          Functor.LaxMonoidal.μ K X Z =
        ν.app (op U) ≫ (pointSmallEtale y).toPresheafFiber U x (X ⊗ Z).obj.obj := by
      erw [Functor.LaxMonoidal.comp_μ, ← Category.assoc, tensor_stalk_germ y,
        Category.assoc, (pointSmallEtale y).toPresheafFiber_naturality]
      rfl
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      have h := galois_pairing_equivariant y G d heval R X Z (X ⊗ Z) ν
        (Functor.LaxMonoidal.μ K X Z) hν g a b
      have hρ : ((E.obj X ⊗ E.obj Z : Rep.{u + 1} R G).ρ g) (a ⊗ₜ[R] b) =
          (E.obj X).ρ g a ⊗ₜ[R] (E.obj Z).ρ g b :=
        TensorProduct.map_tmul _ _ a b
      rw [hρ]
      change Functor.LaxMonoidal.μ K₀ X Z
          ((E.obj X).ρ g a ⊗ₜ[R] (E.obj Z).ρ g b) =
        (E.obj (X ⊗ Z)).ρ g (Functor.LaxMonoidal.μ K₀ X Z (a ⊗ₜ[R] b))
      have hi (x : (E.obj (X ⊗ Z)).V) :
          (d.τ R).inv.app (X ⊗ Z) ((d.τ R).hom.app (X ⊗ Z) x) = x :=
        ConcreteCategory.congr_hom ((d.τ R).hom_inv_id_app (X ⊗ Z)) x
      calc
        _ = (d.τ R).inv.app (X ⊗ Z) (Functor.LaxMonoidal.μ K X Z
            ((d.τ R).hom.app X ((E.obj X).ρ g a) ⊗ₜ[R]
              (d.τ R).hom.app Z ((E.obj Z).ρ g b))) := hμ _ _
        _ = (d.τ R).inv.app (X ⊗ Z) ((d.τ R).hom.app (X ⊗ Z)
            ((E.obj (X ⊗ Z)).ρ g ((d.τ R).inv.app (X ⊗ Z)
              (Functor.LaxMonoidal.μ K X Z
                ((d.τ R).hom.app X a ⊗ₜ[R] (d.τ R).hom.app Z b))))) :=
          congrArg ((d.τ R).inv.app (X ⊗ Z)) h
        _ = (E.obj (X ⊗ Z)).ρ g ((d.τ R).inv.app (X ⊗ Z)
            (Functor.LaxMonoidal.μ K X Z
              ((d.τ R).hom.app X a ⊗ₜ[R] (d.τ R).hom.app Z b))) := hi _
        _ = _ := congrArg ((E.obj (X ⊗ Z)).ρ g) (hμ a b).symm
    | add a b ha hb => simp only [map_add, ha, hb]

end

end AlgebraicGeometry.Scheme
