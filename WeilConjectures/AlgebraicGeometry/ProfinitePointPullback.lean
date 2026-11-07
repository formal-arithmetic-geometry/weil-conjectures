/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage

import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj

/-!
# The geometric inverse image from the profinite point

Source: RefactorInstruction.tex, Section 4, lem:XS and prop:pX, and Section 5,
eq:triangle and thm:alpha (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The set inverse image is left Kan extension followed by sheafification.
Source: RefactorInstruction, prop:pX
(auxiliary; not a blueprint node). -/
noncomputable abbrev profinitePointSetInverseImage :
    Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology specZ.{u}) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt (Type (u + 1))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)

/-- Geometric inverse image from the profinite point, including the specified monoidal
comparison with the inverse image along every scheme morphism.

Source: RefactorInstruction, lem:XS, prop:pX, eq:triangle, thm:alpha
(auxiliary; not a blueprint node).

Proof: (1) Apply the relative profinite test-object theorem at Spec Z to obtain finite
limits and covering preservation, identifying its maps with spectrum of precomposition.
(2) Apply the left-exact site inverse-image tensor theorem to obtain the sheafified Kan
extension adjunction, exactness and strong symmetric monoidality.
(3) The inverse-image composition comparison is the conjugate of the canonical
fibre-product comparison. Uniqueness of adjunction-compatible comparisons gives the
identity and associativity laws, and the site tensor theorem makes it monoidal.
(4) Whisker the comparison for h and the structure morphism by pointUpperStar and use
comp_toSpecZ. This is exactly upperStarFromPointComp, and is natural and monoidal.
(5) Apply it to ring operations to get the ring-sheaf isomorphism. The subsequent
coherence declarations record the identity, composition, linear, derived and square
clauses explicitly. -/
theorem profinite_point_pullback :
    (∀ S : Profinite.{u}, WeaklyEtale (toSpecZ (profiniteToScheme.obj S))) ∧
    PreservesFiniteLimits profiniteToProEt.{u} ∧
    CoverPreserving (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
      profiniteToProEt ∧
    (∀ F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1),
      profiniteToProEt.op.HasLeftKanExtension F) ∧
    (∀ F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1},
      profiniteToProEt.op.HasLeftKanExtension F) ∧
    Nonempty (profinitePointSetInverseImage.{u} ⊣
      profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)) ∧
    PreservesFiniteLimits profinitePointSetInverseImage.{u} ∧
    PreservesColimitsOfSize.{u + 1, u + 1} profinitePointSetInverseImage.{u} ∧
    PreservesFiniteLimits pointUpperStar.{u} ∧
    PreservesFiniteColimits pointUpperStar.{u} ∧
    Nonempty pointUpperStar.{u}.Monoidal ∧
    Nonempty pointUpperStar.{u}.Braided ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      NatTrans.IsMonoidal (upperStarFromPointComp f).hom) := by
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) := AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} := AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  refine ⟨fun S ↦ inferInstance, inferInstance, coverPreserving_profiniteToProEt,
    fun F ↦ inferInstance, fun F ↦ inferInstance, ⟨?_⟩, ?_, ?_, ?_, ?_,
    ⟨inferInstance⟩, ⟨{ toMonoidal := inferInstance, braided := Functor.LaxBraided.braided }⟩,
    fun X Y f ↦ inferInstance⟩
  · exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      profiniteToProEt (Type (u + 1))
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
  · unfold profinitePointSetInverseImage
    infer_instance
  · exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      profiniteToProEt (Type (u + 1))
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).leftAdjoint_preservesColimits
  · unfold pointUpperStar
    infer_instance
  · have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance


open scoped CategoryTheory.Obj

/-- The identity comparison of module direct images is uniquely determined by the
identity comparison on underlying abelian sheaves.
Source: RefactorInstruction, Section 5, coherence of eq:triangle
(auxiliary; not a blueprint node).

Proof: (5) condensedPushforwardHom_id identifies the scalar action with the identity
action through lowerStarId. (6) Hence that abelian identity map and its inverse are
linear. Faithfulness of forgetting the action proves uniqueness. -/
theorem existsUnique_profinitePointModuleDirectImageIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ∃! r : CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _,
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
        (Mod.forget (condensedRingObj Λ X)).map (r.hom.app M) =
          (lowerStarId Ab.{u + 1} X).hom.app M.X := by
  classical
  have : NatTrans.IsMonoidal (lowerStarId Ab.{u + 1} X).hom :=
    Functor.isMonoidal_sheafPushforwardContinuousId' _ _
  let r : CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦ Mod.isoMk ((lowerStarId Ab.{u + 1} X).app M.X) (by
      change (condensedPushforwardHom Λ (𝟙 X) ▷ _ ≫
          Functor.LaxMonoidal.μ (lowerStar Ab.{u + 1} (𝟙 X)) _ _ ≫
          (lowerStar Ab.{u + 1} (𝟙 X)).map (Mod.act M.X)) ≫
          (lowerStarId Ab.{u + 1} X).hom.app M.X = _
      change (condensedPushforwardHom Λ (𝟙 X) ▷ _ ≫
          Functor.LaxMonoidal.μ (lowerStar Ab.{u + 1} (𝟙 X)) _ _ ≫
          (lowerStar Ab.{u + 1} (𝟙 X)).map (Mod.act M.X)) ≫
          (lowerStarId Ab.{u + 1} X).hom.app M.X =
        condensedRingObj Λ X ◁ (lowerStarId Ab.{u + 1} X).hom.app M.X ≫ Mod.act M.X
      rw [condensedPushforwardHom_id]
      simp only [Category.assoc]
      rw [(lowerStarId Ab.{u + 1} X).hom.naturality,
        NatTrans.IsMonoidal.tensor_assoc]
      simp [Functor.LaxMonoidal.id_μ, MonoidalCategory.tensorHom_def,
        ← MonoidalCategory.comp_whiskerRight_assoc])) (fun φ ↦ by
      apply Mod.hom_ext
      exact (lowerStarId Ab.{u + 1} X).hom.naturality φ.hom)
  refine ⟨r, fun M ↦ ?_, ?_⟩
  · rfl
  · intro t ht
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (Mod.forget (condensedRingObj Λ X)).map_injective
    exact ht M

/-- The canonical identity comparison of module direct images, selected by its unique
underlying map, not by a mere existence of an unrelated isomorphism.
Source: RefactorInstruction, Section 5, eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleDirectImageIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  (existsUnique_profinitePointModuleDirectImageIdentity Λ X).exists.choose

/-- The canonical identity comparison of module inverse images is the conjugate of
that of the direct images under the specified module adjunction.
Source: RefactorInstruction, Section 5, eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CondensedRing.upperStar Λ (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))).symm
    (profinitePointModuleDirectImageIdentity Λ X).symm

/-- The scalar-extension pullback has the original exact abelian inverse image as its
underlying sheaf, via restriction along the inverse coefficient isomorphism.
Source: RefactorInstruction, thm:alpha; Stacks, Tags 03D2 and 03D8
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleForgetPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)))
    (Mod.forget (condensedRingObj Λ X))

private lemma moduleLowerStarComp_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((CondensedRing.lowerStarComp Λ f g).hom.app M).hom =
      (lowerStarComp Ab.{u + 1} f g).hom.app M.X := by
  simp only [Functor.comp_obj, CondensedRing.lowerStarComp, Functor.isoWhiskerLeft_trans,
    Functor.isoWhiskerLeft_twice, Functor.mapModCompIso,
    CondensedRing.comapCondensedPushforwardHomComp, Iso.trans_assoc,
    Iso.self_symm_id_assoc, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatIso.ofComponents_hom_app, Category.id_comp, Mod.comp_hom', Mod.id_hom',
    Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom, Mod.comapComp_inv_app_hom,
    Mod.isoMk_hom_hom, asIso_hom, Mod.comapCongr_hom_app_hom]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
    Category.comp_id]

private lemma moduleLowerStarId_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((profinitePointModuleDirectImageIdentity Λ X).hom.app M).hom =
      (lowerStarId Ab.{u + 1} X).hom.app M.X := by
  exact (existsUnique_profinitePointModuleDirectImageIdentity Λ X).exists.choose_spec M

private lemma moduleUnit_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).hom.app M) =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X := by
  let φ := condensedPullbackHom Λ f
  let N := ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M
  have he := congrArg (fun k ↦ k.hom)
    (Adjunction.unit_leftAdjointUniq_hom_app (Mod.extendRestrictAdjunction φ)
      (Mod.comapEquivalenceOfIsIso φ).symm.toAdjunction N)
  simp only [Mod.comp_hom', Mod.comap_map_hom] at he
  have he' : ((Mod.extendRestrictAdjunction φ).unit.app N).hom ≫
      ((Mod.extendScalarsIsoComapInv φ).hom.app N).hom = 𝟙 N.X := by
    change _ = (𝟙 N.X ≫ 𝟙 N.X) ≫ 𝟙 N.X at he
    simpa only [Mod.extendScalarsIsoComapInv, Category.id_comp] using he
  have hc : ((CondensedRing.comapPullbackHomCompIso Λ f).hom.app
      ((CondensedRing.upperStar Λ f).obj M)).hom = 𝟙 _ := by
    simp only [CondensedRing.comapPullbackHomCompIso, Iso.trans_hom,
      Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Mod.comp_hom',
      Mod.id_hom', Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom,
      Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
    rfl
  unfold CondensedRing.upperStarLowerStarAdjunction
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Mod.comp_hom',
    Adjunction.mapModAdjunction_unit_app_hom]
  rw [hc]
  erw [Category.comp_id]
  change ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
      (lowerStar Ab.{u + 1} f).map
        (((Mod.extendRestrictAdjunction φ).unit.app N).hom)) ≫
      (lowerStar Ab.{u + 1} f).map
        (((Mod.extendScalarsIsoComapInv φ).hom.app N).hom) = _
  rw [Category.assoc, ← Functor.map_comp, he']
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma moduleUnit_forget_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).inv.app M) =
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom := by
  rw [← moduleUnit_forget Λ f M, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma moduleIdentity_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((profinitePointModuleIdentity Λ X).hom.app N).hom =
      (profinitePointModuleForgetPullbackIso Λ (𝟙 X)).hom.app N ≫
        (upperStarId Ab.{u + 1} X).hom.app N.X := by
  have hd : ((profinitePointModuleDirectImageIdentity Λ X).inv.app N).hom =
      (lowerStarId Ab.{u + 1} X).inv.app N.X := by
    rw [← cancel_mono ((lowerStarId Ab.{u + 1} X).hom.app N.X), Iso.inv_hom_id_app]
    rw [← moduleLowerStarId_underlying Λ X N]
    change (Mod.forget _).map _ ≫ (Mod.forget _).map _ = _
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    rfl
  have hc : conjugateEquiv Adjunction.id
      (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))
      (profinitePointModuleIdentity Λ X).hom =
      (profinitePointModuleDirectImageIdentity Λ X).inv := by
    exact congrArg Iso.hom ((conjugateIsoEquiv Adjunction.id
      (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))).apply_symm_apply
      (profinitePointModuleDirectImageIdentity Λ X).symm)
  have hm := unit_conjugateEquiv Adjunction.id
    (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))
    (profinitePointModuleIdentity Λ X).hom N
  rw [hc] at hm
  have hm' := congrArg (fun k ↦ k.hom) hm
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Mod.comp_hom'] at hm'
  have ha := unit_conjugateEquiv Adjunction.id
    (upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X))
    (upperStarId Ab.{u + 1} X).hom N.X
  rw [show conjugateEquiv Adjunction.id
      (upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X))
      (upperStarId Ab.{u + 1} X).hom = (lowerStarId Ab.{u + 1} X).inv from
      congrArg Iso.hom (conjugateIsoEquiv_upperStarId Ab.{u + 1} X)] at ha
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at ha
  apply (cancel_epi ((profinitePointModuleForgetPullbackIso Λ (𝟙 X)).inv.app N)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc]
  erw [moduleUnit_forget_inv Λ (𝟙 X) N]
  exact hm'.symm.trans (hd.trans ha)

private lemma moduleCompositeUnit_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f)).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} g).map ((lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M))) =
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app M.X := by
  simp only [Adjunction.comp_unit_app, Mod.comp_hom', Functor.map_comp]
  change (((CondensedRing.upperStarLowerStarAdjunction Λ g).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} g).map
        (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app
          ((CondensedRing.upperStar Λ g).obj M)).hom)) ≫
      ((lowerStar Ab.{u + 1} g).map ((lowerStar Ab.{u + 1} f).map
          ((profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M))) ≫
        (lowerStar Ab.{u + 1} g).map ((lowerStar Ab.{u + 1} f).map
          ((upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M)))) = _
  have hf := congrArg ((lowerStar Ab.{u + 1} g).map)
    (moduleUnit_forget Λ f ((CondensedRing.upperStar Λ g).obj M))
  simp only [Functor.map_comp] at hf
  simp only [Category.assoc]
  erw [reassoc_of% hf]
  rw [← Functor.map_comp]
  have hn := (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality
    ((profinitePointModuleForgetPullbackIso Λ g).hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← hn]
  rw [Functor.map_comp, ← Category.assoc]
  erw [moduleUnit_forget Λ g M]
  rfl

private lemma comparisonFromUnits
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R S : D ⥤ C} (adj : L ⊣ R) (β : S ⟶ R)
    {M : C} {A B B' : D} (e : A ⟶ L.obj M) (ei : L.obj M ⟶ A)
    (a : A ⟶ B) (q : B ⟶ B') (c : L.obj M ⟶ B')
    (η : M ⟶ R.obj A) (ν : M ⟶ S.obj B) (ν' : M ⟶ S.obj B')
    (he : e ≫ ei = 𝟙 _) (hη : adj.unit.app M ≫ R.map ei = η)
    (ha : η ≫ R.map a = ν ≫ β.app B)
    (hq : ν ≫ S.map q = ν')
    (hc : adj.unit.app M ≫ R.map c = ν' ≫ β.app B') :
    a ≫ q = e ≫ c := by
  have hh : ei ≫ (a ≫ q) = c := by
    apply (adj.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc, hη, ← Category.assoc, ha, Category.assoc,
      ← β.naturality q, ← Category.assoc, hq, hc]
  calc
    a ≫ q = e ≫ ei ≫ (a ≫ q) := by
      rw [reassoc_of% he]
    _ = e ≫ c := by rw [hh]

private lemma moduleComposition_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((CondensedRing.upperStarComp Λ f g).hom.app M) ≫
          (profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
        (profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app M.X := by
  intro X Y Z f g M
  let q : ((CondensedRing.upperStar Λ f).obj
      ((CondensedRing.upperStar Λ g).obj M)).X ⟶
      (upperStar Ab.{u + 1} f).obj ((upperStar Ab.{u + 1} g).obj M.X) :=
    (profinitePointModuleForgetPullbackIso Λ f).hom.app
      ((CondensedRing.upperStar Λ g).obj M) ≫
    (upperStar Ab.{u + 1} f).map ((profinitePointModuleForgetPullbackIso Λ g).hom.app M)
  have hc : conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f))
      (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
      (CondensedRing.upperStarComp Λ f g).hom =
      (CondensedRing.lowerStarComp Λ f g).hom := by
    change (conjugateIsoEquiv _ _ (CondensedRing.upperStarComp Λ f g)).hom = _
    rw [CondensedRing.upperStarComp, conjugateIsoEquiv_iso_symm]
    simp
  have hm := unit_conjugateEquiv
    ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f))
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g).hom M
  rw [hc] at hm
  have hm' := congrArg (fun k ↦ k.hom) hm
  simp only [Mod.comp_hom', moduleLowerStarComp_underlying, Functor.comp_obj] at hm'
  have ha := unit_conjugateEquiv
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f))
    (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (upperStarComp Ab.{u + 1} f g).hom M.X
  rw [conjugateEquiv_upperStarComp_hom] at ha
  have hu : (((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f)).unit.app M).hom ≫
      ((lowerStar Ab.{u + 1} f) ⋙ (lowerStar Ab.{u + 1} g)).map q =
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app M.X :=
    moduleCompositeUnit_forget Λ f g M
  exact comparisonFromUnits (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (lowerStarComp Ab.{u + 1} f g).hom
    ((profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M)
    ((profinitePointModuleForgetPullbackIso Λ (f ≫ g)).inv.app M)
    (((CondensedRing.upperStarComp Λ f g).hom.app M).hom) q
    ((upperStarComp Ab.{u + 1} f g).hom.app M.X)
    (((CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g)).unit.app M).hom)
    ((((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f)).unit.app M).hom)
    (((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app M.X)
    (Iso.hom_inv_id_app _ M) (moduleUnit_forget_inv Λ (f ≫ g) M)
    hm'.symm hu ha.symm

/-- The module comparison is the linear lift of the abelian comparison. Exactness
follows because extension of scalars along the coefficient isomorphism is an equivalence.
Source: RefactorInstruction, thm:alpha; Stacks, Tags 03D2 and 03D8
(auxiliary; not a blueprint node).

Proof: (6) Apply inverse image to the module action and substitute the inverse coefficient
isomorphism in the scalar variable. The balanced maps r tensor m to alpha inverse(r)m
and m to 1 tensor m are inverse, giving profinitePointModuleForgetPullbackIso. Naturality
of the abelian composition comparison at the action makes it linear; its underlying map
is the equation below. Forgetting is faithful and creates kernels and sheafified cokernels,
so exactness and the abelian unit and associativity equations lift to modules. -/
theorem profinite_point_pullback_module_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      PreservesFiniteLimits (CondensedRing.upperStar Λ f) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ f)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((profinitePointModuleIdentity Λ X).hom.app
            ((CondensedRing.upperStar Λ f).obj M)) =
        (profinitePointModuleForgetPullbackIso Λ (𝟙 X)).hom.app
            ((CondensedRing.upperStar Λ f).obj M) ≫
          (upperStarId Ab.{u + 1} X).hom.app
            ((CondensedRing.upperStar Λ f).obj M).X) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((CondensedRing.upperStarComp Λ f g).hom.app M) ≫
          (profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
        (profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app M.X) := by
  refine ⟨?_, ?_, moduleComposition_forget Λ⟩
  · intro X Y f
    exact ⟨inferInstance, inferInstance⟩
  · intro X Y f M
    exact moduleIdentity_forget Λ X ((CondensedRing.upperStar Λ f).obj M)


private lemma eqToIso_congr_symm
    {A B : Type*} [Category B] (F : A → B) {a b : A} (w : a = b) :
    eqToIso (congrArg F w.symm) = (eqToIso (congrArg F w)).symm := by
  cases w
  rfl

section ModuleMates
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]


end ModuleMates


/-- Monoidality of the canonical abelian inverse-image composition comparison.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(auxiliary; not a blueprint node).

Proof: (2) The sheafified Kan-extension inverse images have their canonical tensor
structures by the site inverse-image tensor theorem. (3) The composition comparison
is adjunction-compatible, so the monoidal comparison clause of that theorem applies.
Equivalently, conjugate the monoidal direct-image comparison and use the tensor mates. -/
@[instance]
theorem profinitePoint_isMonoidal_upperStarComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
      Functor.Monoidal.toOplaxMonoidal _ :=
    isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := Adjunction.isMonoidal_comp _ _
  have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).symm.hom :=
    isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f g).inv
  exact inferInstanceAs (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).symm.inv)

/-- Monoidality of the canonical identity comparison of abelian inverse images.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(auxiliary; not a blueprint node).

Proof: (3) Compare the inverse-image identity adjunction with the identity adjunction.
The unit equation uniquely specifies upperStarId; the monoidal identity clause of the
site inverse-image tensor theorem says this same comparison is monoidal. -/
@[instance]
theorem profinitePoint_isMonoidal_upperStarId (X : Scheme.{u}) :
    NatTrans.IsMonoidal (upperStarId Ab.{u + 1} X).hom := by
  have : NatTrans.IsMonoidal (lowerStarId Ab.{u + 1} X).hom :=
    Functor.isMonoidal_sheafPushforwardContinuousId' _ _
  have h : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X))
      Functor.Monoidal.toOplaxMonoidal _ :=
    isMonoidal_upperStarLowerStarAdjunction _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarId Ab.{u + 1} X).inv

/-- The canonical ring-object composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointRingComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Ab.{u + 1} (f ≫ g)).mapMon ≅ (upperStar Ab.{u + 1} g).mapMon ⋙ (upperStar Ab.{u +
      1} f).mapMon :=
  Functor.mapMonNatIso (upperStarComp Ab.{u + 1} f g) ≪≫ Functor.mapMonCompIso

/-- The canonical ring-object identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointRingIdentity
    (X : Scheme.{u}) :
    (upperStar Ab.{u + 1} (𝟙 X)).mapMon ≅ 𝟭 (Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
  Functor.mapMonNatIso (upperStarId Ab.{u + 1} X) ≪≫ Functor.mapMonIdIso


end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Functor

section TransferUnits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]


end TransferUnits

section TransferAssociativity
variable {C D E J : Type*} [Category C] [Category D] [Category E] [Category J]
  [Abelian C] [Abelian D] [Abelian E] [Abelian J]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory J]
  (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ J)
  (P : C ⥤ E) (Q : D ⥤ J) (R R' : C ⥤ J)
  [F.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive] [R.Additive] [R'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']

end TransferAssociativity

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open scoped CategoryTheory.Obj

/-- The canonical termwise derived composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointAbelianDerivedComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Ab.{u + 1} (f ≫ g)).mapDerivedCategory ≅
      (upperStar Ab.{u + 1} g).mapDerivedCategory ⋙ (upperStar Ab.{u + 1} f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Ab.{u + 1} f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1} f)).symm

/-- The canonical termwise derived identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointAbelianDerivedIdentity
    (X : Scheme.{u}) :
    (upperStar Ab.{u + 1} (𝟙 X)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1})) :=
  Functor.mapDerivedCategoryNatIso (upperStarId Ab.{u + 1} X) ≪≫ Functor.mapDerivedCategoryIdIso _


/-- The canonical termwise derived composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleDerivedComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CondensedRing.upperStar Λ (f ≫ g)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ g).mapDerivedCategory ⋙ (CondensedRing.upperStar Λ
        f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
      (CondensedRing.upperStar Λ f)).symm

/-- The canonical termwise derived identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleDerivedIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    (CondensedRing.upperStar Λ (𝟙 X)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Mod (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  Functor.mapDerivedCategoryNatIso (profinitePointModuleIdentity Λ X) ≪≫
      Functor.mapDerivedCategoryIdIso _


/-- The geometric set inverse image for an arbitrary scheme is the point inverse image
followed by the actual scheme inverse image along its structure morphism.
Source: RefactorInstruction, prop:pX and eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable abbrev profinitePointSetSchemeInverseImage (X : Scheme.{u}) :=
  profinitePointSetInverseImage.{u} ⋙
    Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1))

/-- Set inverse-image composition, conjugate to the canonical direct-image comparison.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointSetComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.proEtaleSheafInverseImage (f ≫ g) (Type (u + 1)) ≅
      Scheme.proEtaleSheafInverseImage g (Type (u + 1)) ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) :=
  ((conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction (f ≫ g) (Type (u + 1)))
      ((Scheme.proEtaleSheafAdjunction g (Type (u + 1))).comp
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))).symm
    (lowerStarComp (Type (u + 1)) f g).symm).symm

/-- Set inverse-image identity, conjugate to the canonical direct-image identity.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointSetIdentity (X : Scheme.{u}) :
    Scheme.proEtaleSheafInverseImage (𝟙 X) (Type (u + 1)) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))).symm
      (lowerStarId (Type (u + 1)) X).symm

/-- The set-level point comparison is composition followed by the structure-map equality.
Source: RefactorInstruction, Section 5, eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointSetSchemeComp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profinitePointSetSchemeInverseImage Y ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) ≅
      profinitePointSetSchemeInverseImage X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft profinitePointSetInverseImage
    ((profinitePointSetComp f (toSpecZ Y)).symm ≪≫
      eqToIso (congrArg
        (fun k : X ⟶ specZ ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1)))
        (comp_toSpecZ f)))


end AlgebraicGeometry.ProEtale
