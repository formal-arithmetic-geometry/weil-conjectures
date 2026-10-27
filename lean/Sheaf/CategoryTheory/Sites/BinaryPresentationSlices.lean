/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.CategoryTheory.Sites.BinaryPresentationModuleData
import Sheaf.CategoryTheory.Sites.BinaryPresentationRingedSlices
import Sheaf.CategoryTheory.Sites.BinaryPresentationRestrictionData


/-! # Simultaneous ringed slice comparisons for a specified nerve equivalence -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
section
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  (eC : C ≌ E) (eD : D ≌ F)
  (b : R₁ ⋙ eC.functor ≅ eD.functor ⋙ R₂)

private theorem equivalentMate_bijective (A : C) (B : D) :
    Function.Bijective (fun g : eD.functor.obj (L₁.obj A) ⟶ eD.functor.obj B ↦
      ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A ≫ g) := by
  let l := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A
  let h := eD.fullyFaithfulFunctor.homEquiv.symm |>.trans (a₁.homEquiv A B)
  let k := h.trans eC.fullyFaithfulFunctor.homEquiv
  let z := k.trans (Iso.homCongr (Iso.refl _) (b.app B))
  have hz (g : eD.functor.obj (L₁.obj A) ⟶ eD.functor.obj B) :
      a₂.homEquiv _ _ (l ≫ g) = z g := by
    obtain ⟨g, rfl⟩ := eD.fullyFaithfulFunctor.homEquiv.surjective g
    rw [Adjunction.homEquiv_unit, R₂.map_comp, ← Category.assoc]
    change (a₂.unit.app (eC.functor.obj A) ≫
      R₂.map (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A)) ≫
        R₂.map (eD.functor.map g) = z (eD.functor.map g)
    have hu := unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ b.hom) A
    change eC.functor.map (a₁.unit.app A) ≫ b.hom.app (L₁.obj A) =
      a₂.unit.app (eC.functor.obj A) ≫ R₂.map
        (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A) at hu
    rw [← hu]
    have hn := b.hom.naturality g
    change eC.functor.map (R₁.map g) ≫ b.hom.app B =
      b.hom.app (L₁.obj A) ≫ R₂.map (eD.functor.map g) at hn
    rw [Category.assoc, ← hn, ← eC.functor.map_comp_assoc]
    simp [z, k, h, Adjunction.homEquiv_unit]
  rw [← (a₂.homEquiv _ _).bijective.of_comp_iff']
  change Function.Bijective (fun g ↦ a₂.homEquiv _ _ (l ≫ g))
  have he : (fun g ↦ a₂.homEquiv _ _ (l ≫ g)) = z := funext hz
  rw [he]
  exact z.bijective

private theorem equivalentMate_isIso :
    IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  apply isIso_of_coyoneda_map_bijective
  intro B
  let l := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A
  let z := eD.counitIso.app B
  have h := equivalentMate_bijective a₁ a₂ eC eD b A (eD.inverse.obj B)
  constructor
  · intro g g' hh
    apply (cancel_mono z.inv).1
    apply h.injective
    change l ≫ g ≫ z.inv = l ≫ g' ≫ z.inv
    change l ≫ g = l ≫ g' at hh
    rw [← Category.assoc, ← Category.assoc, hh]
  · intro k
    obtain ⟨g, hg⟩ := h.surjective (k ≫ z.inv)
    refine ⟨g ≫ z.hom, ?_⟩
    change l ≫ g = k ≫ z.inv at hg
    change l ≫ g ≫ z.hom = k
    rw [← Category.assoc, hg, Category.assoc, z.inv_hom_id]
    exact Category.comp_id k
end


/-- The four ringed slice comparisons, including the restriction squares and their coherence.
Source: Stacks Sites 00Y1, 04GZ and 03EH; Modules on Sites 03CR and 04IE.
(blueprint: lem-sp-nerve-ringed-slice-comparisons). -/
structure BinaryPresentationSlices
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{u}) (ring : Sheaf K CommRingCat.{u})
    (F : E ⥤ Sheaf J (Type u)) (Z : Fin 4 → E)
    (ringed : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R))
    (wholeModules : BinaryPresentationModules ringed)
    (sourceSlice : ∀ i : Fin 4,
      RingedSheafSliceAdjunctionData (localCoefficientRings R) (F.obj (Z i)))
    (slice : ∀ i : Fin 4, Over (F.obj (Z i)) ≌ Sheaf (K.over (Z i)) (Type u)) where
  sliceRinged : ∀ i : Fin 4,
    RingedToposMorphism (localCoefficientRings (ring.over (Z i)))
      (localCoefficientRings (presentationElementRing R (F.obj (Z i))))
  sliceInverse : ∀ i : Fin 4, Nonempty ((sliceRinged i).inverse ≅
    (sourceSlice i).fibreEquivalence.functor ⋙ (slice i).functor)
  sliceRingIsIso : ∀ i : Fin 4, IsIso (sliceRinged i).ringMap
  sliceModules : ∀ i : Fin 4, BinaryPresentationModules (sliceRinged i)
  sourceContinuous : ∀ (i j : Fin 4) (f : Z i ⟶ Z j),
    Functor.IsContinuous (elementMap (F.map f))
      (elementTopology (F.obj (Z i)))
      (elementTopology (F.obj (Z j)))
  restriction : ∀ i : Fin 4, BinaryPresentationAdjointSquare
    wholeModules.modules (sliceModules i).modules
    (elementModulePullback.{u, u} (localCoefficientRings R) (F.obj (Z i)))
    (SheafOfModules.overFunctor.{u} (localCoefficientRings ring) (Z i))

  further : ∀ (i j : Fin 4) (f : Z i ⟶ Z j),
    BinaryPresentationAdjointSquare (sliceModules j).modules (sliceModules i).modules
      (elementModulePullbackOver.{u, u} (localCoefficientRings R) (F.map f)
        (sourceContinuous i j f))
      (SheafOfModules.overMap.{u} (localCoefficientRings ring) f)

  restrictionComposition : ∀ (i j : Fin 4) (f : Z i ⟶ Z j)
      (M : PresentationModules R),
    HEq ((restriction i).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullback.{u, u} (localCoefficientRings R)
            (F.obj (Z j))).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((restriction j).comparison.hom.app M) ≫
        (SheafOfModules.overFunctorMap.{u} (localCoefficientRings ring) f).hom.app
          (wholeModules.modules.functor.obj M))
  furtherIdentity : ∀ (i : Fin 4)
      (M : PresentationModules (presentationElementRing R (F.obj (Z i)))),
    HEq ((further i i (𝟙 (Z i))).comparison.hom.app M)
      (𝟙 ((sliceModules i).modules.functor.obj M))
  furtherComposition : ∀ (i j k : Fin 4) (f : Z i ⟶ Z j)
      (g : Z j ⟶ Z k)
      (M : PresentationModules (presentationElementRing R (F.obj (Z k)))),
    HEq ((further i k (f ≫ g)).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullbackOver.{u, u} (localCoefficientRings R) (F.map g)
            (sourceContinuous j k g)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((further j k g).comparison.hom.app M))

private theorem rightEquivalentMate
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') {F : A ⥤ B} {F' : A' ⥤ B'}
    {G : B ⥤ A} {G' : B' ⥤ A'} (a : F ⊣ G) (a' : F' ⊣ G')
    (c : F ⋙ E'.functor ≅ E.functor ⋙ F') :
    IsIso ((mateEquiv a a' (TwoSquare.mk _ _ _ _ c.inv)).natTrans) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let m := (mateEquiv a a' (TwoSquare.mk _ _ _ _ c.inv)).natTrans.app Y
  have hb (X : A) : Function.Bijective
      (fun f : E.functor.obj X ⟶ E.functor.obj (G.obj Y) ↦ f ≫ m) := by
    let e1 := E.fullyFaithfulFunctor.homEquiv.symm |>.trans (a.homEquiv X Y).symm
    let e2 := e1.trans E'.fullyFaithfulFunctor.homEquiv
    let e3 := e2.trans (Iso.homCongr (c.app X) (Iso.refl _))
    let e := e3.trans (a'.homEquiv _ _)
    have he (f : E.functor.obj X ⟶ E.functor.obj (G.obj Y)) : f ≫ m = e f := by
      apply (a'.homEquiv _ _).symm.injective
      obtain ⟨f, rfl⟩ := E.fullyFaithfulFunctor.homEquiv.surjective f
      rw [Adjunction.homEquiv_naturality_left_symm]
      have hm := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ c.inv) Y
      change F'.map m ≫ a'.counit.app (E'.functor.obj Y) =
        c.inv.app (G.obj Y) ≫ E'.functor.map (a.counit.app Y) at hm
      rw [Adjunction.homEquiv_counit, hm]
      have hn := c.inv.naturality f
      change F'.map (E.functor.map f) ≫ c.inv.app (G.obj Y) =
        c.inv.app X ≫ E'.functor.map (F.map f) at hn
      change F'.map (E.functor.map f) ≫ c.inv.app (G.obj Y) ≫
        E'.functor.map (a.counit.app Y) = _
      rw [← Category.assoc, hn, Category.assoc, ← E'.functor.map_comp]
      simp [e, e3, e2, e1, Adjunction.homEquiv_counit]
    have hfun : (fun f : E.functor.obj X ⟶ E.functor.obj (G.obj Y) ↦ f ≫ m) = e :=
      funext he
    rw [hfun]
    exact e.bijective
  apply isIso_of_yoneda_map_bijective
  intro X
  let z := E.counitIso.app X
  constructor
  · intro f g h
    apply (cancel_epi z.hom).mp
    apply (hb (E.inverse.obj X)).injective
    change (z.hom ≫ f) ≫ m = (z.hom ≫ g) ≫ m
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun q ↦ z.hom ≫ q) h
  · intro f
    obtain ⟨g, hg⟩ := (hb (E.inverse.obj X)).surjective (z.hom ≫ f)
    refine ⟨z.inv ≫ g, ?_⟩
    change g ≫ m = z.hom ≫ f at hg
    change (z.inv ≫ g) ≫ m = f
    rw [Category.assoc, hg, ← Category.assoc, z.inv_hom_id, Category.id_comp]

private def adjointSquare
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') (F : A ⥤ B) (F' : A' ⥤ B')
    (c : F ⋙ E'.functor ≅ E.functor ⋙ F') : BinaryPresentationAdjointSquare E E' F F' where
  comparison := c
  rightMate := fun _ _ a a' ↦ rightEquivalentMate E E' a a' c
  leftMate := fun _ _ a a' ↦ equivalentMate_isIso a a' E' E c

/-- A specified nerve equivalence has simultaneous ringed slice comparisons.
Source: Stacks Sites 00Y1, 04GZ and 03EH; Modules on Sites 03CR and 04IE.
(blueprint: lem-sp-nerve-ringed-slice-comparisons).

Proof: over Z use the fibre nerve sending B → F(Z) to the sheaf
(C → Z) ↦ Hom over F(Z) from F(C) to B. The subcanonical localized-site
comparison and full faithfulness of F identify this with the equivalence induced
on slices by N. Composing the element-site fibre equivalence gives its source
site. The product/fibre bijection sends (b,c) to b, so it identifies the restricted
ring with ring.over Z and commutes with all ring operations. Transport module
addition and scalar multiplication through these specified fibre bijections.
The resulting equivalences have the underlying and rank-one equations of
BinaryPresentationModules; the induced direct images are their inverses by
adjunction uniqueness. Localizing their termwise functors gives the ordinary
derived equivalences. All restriction comparisons send (m,c) to m. On identities
and composites their components coincide, since both select this same component.
Both mates are invertible: conjugate each adjoint under the two equivalences and
use adjunction uniqueness, with the comparison fixing the unit and counit.
Subterminality is used for coherent restriction; no binary-cover assumption is needed. -/
theorem exists_binaryPresentationSlices
    {C E : Type u} [SmallCategory C] [SmallCategory E] [HasFiniteLimits E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E} [K.Subcanonical]
    (R : Sheaf J CommRingCat.{u}) (ring : Sheaf K CommRingCat.{u})
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful] [PreservesFiniteLimits F]
    (Z : Fin 4 → E) (hsub : ∀ i : Fin 4, IsSubterminal (F.obj (Z i)))
    (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (hN : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F)
    (ringed : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R))
    (hi : ringed.inverse = N.functor) (_hd : ringed.direct = N.inverse)
    (hr : IsIso ringed.ringMap) (whole : BinaryPresentationModules ringed)
    (sourceSlice : ∀ i : Fin 4,
      RingedSheafSliceAdjunctionData (localCoefficientRings R) (F.obj (Z i)))
    (slice : ∀ i : Fin 4, Over (F.obj (Z i)) ≌ Sheaf (K.over (Z i)) (Type u))
    (hSlice : ∀ i : Fin 4,
      (slice i).functor ⋙ sheafToPresheaf (K.over (Z i)) (Type u) ≅
        yoneda ⋙ (Functor.whiskeringLeft (Over (Z i))ᵒᵖ
          (Over (F.obj (Z i)))ᵒᵖ (Type u)).obj (Over.post F).op) :
    Nonempty (BinaryPresentationSlices R ring F Z ringed whole sourceSlice slice) := by
  classical
  choose e he hring loc c using fun i : Fin 4 ↦
    exists_binaryPresentationRingedSlice R ring F N hN ringed hi hr whole
      (Z i) (sourceSlice i) (slice i) (hSlice i)
  obtain ⟨d⟩ := exists_binaryPresentationRestrictionData R ring F Z hsub ringed whole e loc c
  exact ⟨{
    sliceRinged := e
    sliceInverse := fun i ↦ ⟨eqToIso (he i)⟩
    sliceRingIsIso := hring
    sliceModules := loc
    sourceContinuous := d.sourceContinuous
    restriction := fun i ↦ adjointSquare _ _ _ _ (d.restriction i)
    further := fun i j f ↦ adjointSquare _ _ _ _ (d.further i j f)
    restrictionComposition := d.restrictionComposition
    furtherIdentity := d.furtherIdentity
    furtherComposition := d.furtherComposition }⟩

end CategoryTheory
