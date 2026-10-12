/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import Sheaf.AlgebraicGeometry.GaloisPointAction
import Sheaf.FieldTheory.GaloisAutomorphismExtension

/-!
# Sections over a field as geometric stalk invariants

Source: Stacks Project, Tags 03QW and 04JQ, Lemma global-sections-point.
(blueprint: lem-sc-etale-field-sections-invariants).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A geometric-stalk equivalence identifies global sections with Galois invariants,
naturally in the abelian sheaf. This is a degree-zero assertion only.

Source: Stacks Project, Lemma global-sections-point (Tag 04JM), and Tag 04JQ.
(blueprint: lem-sc-etale-field-sections-invariants).

Proof: Apply fieldSections_stalkInvariants to the underlying sheaf of sets.
The forgetful functor commutes with the geometric stalk, by sheafFiberCompIso.
Its comparison commutes with every germ map. The action given by the sections
comparison agrees with the action from i: represent any stalk element by a germ,
extend g to an automorphism of Ω, and compare both lift-change formulas using
exists_galoisPointAction. Specialize the sections comparison to the bottom
intermediate field K inside Ks, whose fixing subgroup is all of G. Its etale
spectrum is isomorphic to the terminal etale object via botEquiv. The naturality
of germ maps along that isomorphism identifies global sections with fixed germs.
The additive map given by the terminal germ followed by i.inv has invariant image.
It is injective and surjective onto the invariant subgroup, by the set-valued
comparison and the two stalk isomorphisms. Naturality follows from the natural
terminal germ transformation and i.inv. Its bijective components therefore form
the claimed natural isomorphism. The algebraicity hypothesis on Ω is used by the
existing sections comparison. The zero sheaf, a separably closed base, and an
imperfect base are all included; only finite separable neighbourhoods are used. -/
theorem nonempty_iso_etaleFieldSections_invariants
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    let G := Gal(Ks/K)
    let D := Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ G
    let U : D ⥤ Rep.{u + 1} ℤ G := ObjectProperty.ι _
    ∀ (E : Sheaf J AddCommGrpCat.{u + 1} ≌ D)
      (i : E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
        Action.forget (ModuleCat.{u + 1} ℤ) G ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅ p.sheafFiber),
      (∀ (F : Sheaf J AddCommGrpCat.{u + 1}) (g : G) (τ : Ω ≃ₐ[K] Ω)
        (_hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (X : S.Etale) (x x' : p.fiber.obj X)
        (_hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
        (z : F.obj.obj (op X)),
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      Nonempty
        (sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
            (op (Scheme.Etale.mk (𝟙 S))) ≅
            E.functor ⋙ U ⋙ Rep.invariantsFunctor ℤ G ⋙
              forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat) := by
  classical
  dsimp only
  intro E i hi
  let S := Spec (.of K)
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let T := Scheme.Etale.mk (𝟙 S)
  let xT : p.fiber.obj T := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let Q := sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let γ := p.sheafFiberCompIso (CategoryTheory.forget AddCommGrpCat.{u + 1})
  obtain ⟨lift, act, _, hact, _⟩ :=
    fieldSections_stalkInvariants.{u, 0} K Ks Ω
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) rfl
  obtain ⟨ρ, hρ, _⟩ := exists_galoisPointAction K Ks Ω
  have hγ (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (X : S.Etale) (x : p.fiber.obj X) (z : F.obj.obj (op X)) :
      (γ.hom.app F) (p.toPresheafFiber X x (Q.obj F).obj z) =
        p.toPresheafFiber X x F.obj z := by
    exact ConcreteCategory.congr_hom
      (p.toPresheafFiber_presheafFiberCompIso_hom_app
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) X x F.obj) z
  have ha (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (g : Gal(Ks/K)) (a : p.sheafFiber.obj (Q.obj F)) :
      (γ.hom.app F) ((act (Q.obj F)).smul g a) =
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) ((γ.hom.app F) a))) := by
    obtain ⟨X, x, z, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := (Q.obj F).obj) a
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
    rw [(hact (Q.obj F)).1 g τ hτ X x ((ρ g).app X x) (hρ g τ hτ X x) z]
    rw [hγ, hγ]
    exact (hi F g τ hτ X x ((ρ g).app X x) (hρ g τ hτ X x) z).symm
  let B := etaleSpec K (⊥ : IntermediateField K Ks)
  let eT : T ≅ B := MorphismProperty.Over.isoMk
    (Scheme.Spec.mapIso ((IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso.op)) (by
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp]
      have h : (CommRingCat.ofHom (algebraMap K (⊥ : IntermediateField K Ks))) ≫
          ((IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso).hom = 𝟙 _ := by
        ext k
        exact (IntermediateField.botEquiv K Ks).commutes k
      change Spec.map (CommRingCat.ofHom (algebraMap K (⊥ : IntermediateField K Ks)) ≫
        (IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso.hom) = _
      rw [h]
      exact Spec.map_id _)
  have hpoint : p.fiber.map eT.inv (lift (⊥ : IntermediateField K Ks)) = xT := by
    apply Over.OverMorphism.ext
    have hh := Over.w (p.fiber.map eT.inv (lift (⊥ : IntermediateField K Ks)))
    change _ ≫ 𝟙 S = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) at hh
    change _ = Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    simpa only [Category.comp_id] using hh
  have hgerm (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (z : (Q.obj F).obj.obj (op T)) :
      p.toPresheafFiber B (lift (⊥ : IntermediateField K Ks)) (Q.obj F).obj
        ((Q.obj F).obj.map eT.inv.op z) = p.toPresheafFiber T xT (Q.obj F).obj z := by
    rw [← hpoint]
    exact ConcreteCategory.congr_hom
      (p.toPresheafFiber_w eT.inv (lift (⊥ : IntermediateField K Ks)) (Q.obj F).obj) z
  have hsec (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Set.BijOn (p.toPresheafFiber T xT (Q.obj F).obj) Set.univ
        {a | ∀ g : Gal(Ks/K), (act (Q.obj F)).smul g a = a} := by
    have hb := (hact (Q.obj F)).2.1 (⊥ : IntermediateField K Ks)
    simp only [IntermediateField.fixingSubgroup_bot, Subgroup.mem_top, forall_const] at hb
    have hr := ConcreteCategory.bijective_of_isIso ((Q.obj F).obj.map eT.inv.op)
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [← hgerm F z]
      exact hb.mapsTo (Set.mem_univ _)
    · intro z z' hz hz' heq
      apply hr.1
      apply hb.injOn (Set.mem_univ _) (Set.mem_univ _)
      change p.toPresheafFiber B (lift (⊥ : IntermediateField K Ks)) (Q.obj F).obj
        ((Q.obj F).obj.map eT.inv.op z) = _
      rw [hgerm, hgerm]
      exact heq
    · intro a ha
      obtain ⟨z, hz, hza⟩ := hb.surjOn ha
      obtain ⟨t, ht⟩ := hr.2 z
      refine ⟨t, Set.mem_univ _, ?_⟩
      rw [← hgerm F t, ht]
      exact hza
  let f (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      F.obj.obj (op T) →+ (E.functor.obj F).obj.V :=
    (p.toPresheafFiber T xT F.obj ≫ i.inv.app F).hom
  have hf (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (z : F.obj.obj (op T)) :
      ∀ g : Gal(Ks/K), (E.functor.obj F).obj.ρ g (f F z) = f F z := by
    intro g
    apply (ConcreteCategory.bijective_of_isIso (i.hom.app F)).1
    have h := ha F g (p.toPresheafFiber T xT (Q.obj F).obj z)
    rw [hγ] at h
    change (i.hom.app F) ((E.functor.obj F).obj.ρ g
      ((i.inv.app F) (p.toPresheafFiber T xT F.obj z))) =
        (i.hom.app F) ((i.inv.app F) (p.toPresheafFiber T xT F.obj z))
    rw [← h, (hsec F).mapsTo (Set.mem_univ _) g, hγ]
    exact (i.inv_hom_id_app_apply F _).symm
  let Γ := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op T)
  let U : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)) ⥤
      Rep.{u + 1} ℤ (Gal(Ks/K)) := ObjectProperty.ι _
  let V := E.functor ⋙ U ⋙ Rep.invariantsFunctor ℤ (Gal(Ks/K)) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
  let μ := Functor.whiskerLeft
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (p.toPresheafFiberNatTrans T xT) ≫ i.inv
  let α : Γ ⟶ V :=
    { app := fun F ↦ AddCommGrpCat.ofHom ((f F).codRestrict _ (hf F))
      naturality := by
        intro F F' φ
        ext z
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (μ.naturality φ) z }
  have hbij (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Function.Bijective (α.app F) := by
    let : Module ℤ (E.functor.obj F).obj.V := (E.functor.obj F).obj.hV2
    constructor
    · intro z z' hzz'
      apply (hsec F).injOn (Set.mem_univ _) (Set.mem_univ _)
      apply (ConcreteCategory.bijective_of_isIso (γ.hom.app F)).1
      rw [hγ, hγ]
      apply (ConcreteCategory.bijective_of_isIso (i.inv.app F)).1
      exact congrArg Subtype.val hzz'
    · intro x
      change (E.functor.obj F).obj.ρ.invariants at x
      let a := (γ.inv.app F) ((i.hom.app F) x.val)
      have ha' : ∀ g : Gal(Ks/K), (act (Q.obj F)).smul g a = a := by
        intro g
        apply (ConcreteCategory.bijective_of_isIso (γ.hom.app F)).1
        rw [ha]
        dsimp only [a]
        simp only [Iso.inv_hom_id_app_apply, Iso.hom_inv_id_app_apply]
        rw [x.property g]
      obtain ⟨z, hz, hza⟩ := (hsec F).surjOn ha'
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change (i.inv.app F) (p.toPresheafFiber T xT F.obj z) = x.val
      rw [← hγ, hza]
      dsimp only [a]
      rw [γ.inv_hom_id_app_apply, i.hom_inv_id_app_apply]
  have : ∀ F, IsIso (α.app F) := fun F ↦ (ConcreteCategory.isIso_iff_bijective _).2 (hbij F)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α⟩

end AlgebraicGeometry.Scheme
