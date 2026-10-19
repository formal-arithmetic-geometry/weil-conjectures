/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Derived section functors under an additive equivalence

Source: Stacks Project, Derived Categories, Tag 015M, lemma-compose-derived-functors,
with Tags 013K, 013P and 05TD for resolutions, their maps and degree zero
(blueprint: lem-exc-equivalence-derived-sections).
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open Category Limits

/-- The specified injective resolution transported termwise along an additive equivalence.
Its augmentation is the image of the given augmentation, using the canonical identification
of the image of a degree-zero single complex with the single complex of the image.
The equivalence preserves injectives, finite limits and colimits, hence quasi-isomorphisms.
Source: Stacks Project, Tag 015M, proof on the complex `F(I)`, and Tag 015Z
(blueprint: lem-exc-equivalence-derived-sections). -/
noncomputable def InjectiveResolution.equivalenceImage
    {C : Type u₁} {B : Type u₂} [Category.{v₁} C] [Category.{v₂} B]
    [Abelian C] [Abelian B] {X : C} (I : InjectiveResolution X)
    (E : C ⥤ B) [E.Additive] [E.IsEquivalence] : InjectiveResolution (E.obj X) where
  cocomplex := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := E.injective_obj_of_injective (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.up ℕ) 0).inv.app X ≫
    (E.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

set_option backward.isDefEq.respectTransparency false in
/-- An additive equivalence intertwining left exact section functors intertwines all their
right derived functors. The comparison is computed by the given natural isomorphism on
*every* injective resolution, and its degree-zero normalization is that same isomorphism.
Source: Stacks Project, Tag 015M, exact-equivalence special case; Tag 05TD for degree zero
(blueprint: lem-exc-equivalence-derived-sections).

Proof:
1. Enough injectives gives a resolution by successively embedding cokernels into injectives
   (def-sp-enough-injectives, def-sp-injective-resolutions, def-sp-abelian; Tag 013K).
2. The equivalence preserves injectives and exactness, so its termwise image is the resolution
   `I.equivalenceImage E` (lem-weil-pbc-equivalence-injective-resolutions; Tag 015Z).
3. Naturality of `α` on each differential makes its components an isomorphism of complexes;
   its termwise inverse is a chain map as well. Taking cohomology gives inverse maps.
4. Conjugate this cohomology map by `I.isoRightDerivedObj S q` and the corresponding
   isomorphism for `T` on the transported resolution (lem-weil-pbc-derived-functor-map-via-lift).
   This gives the stated component formula and invertibility.
5. Lift any object morphism to a map of resolutions (lem-weil-pbc-injective-resolution-lift-exists,
   Tag 013P). Apply the map formula of lem-weil-pbc-derived-functor-map-via-lift twice and
   naturality of `α` on the lift. Cancellation of the resolution isomorphisms gives naturality.
6. Apply the same square to the identity between any two resolutions. The derived maps are
   identities, proving resolution independence. Inverse components are natural by cancellation.
7. In degree zero, left exactness identifies each section object with the kernel of the first
   differential, via its augmentation (lem-weil-pbc-left-exact-injective-resolution-degree-zero).
   There are no negative-degree boundaries. Naturality of `α` on the augmentation gives the
   last equality under the canonical degree-zero identifications of lem-sp-derived-well-defined.
-/
theorem exists_equivalence_derivedSections
    {C : Type u₁} {B : Type u₂} {D : Type u₃}
    [Category.{v₁} C] [Category.{v₂} B] [Category.{v₃} D]
    [Abelian C] [Abelian B] [Abelian D] [EnoughInjectives C] [EnoughInjectives B]
    (E : C ⥤ B) [E.Additive] [E.IsEquivalence]
    (S : C ⥤ D) (T : B ⥤ D) [S.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteLimits T] (α : S ≅ E ⋙ T) :
    ∃ c : ∀ q : ℕ, S.rightDerived q ≅ E ⋙ T.rightDerived q,
      (∀ (q : ℕ) (X : C) (I : InjectiveResolution X),
        (c q).hom.app X ≫ ((I.equivalenceImage E).isoRightDerivedObj T q).hom =
          (I.isoRightDerivedObj S q).hom ≫
            HomologicalComplex.homologyMap
              ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex) q) ∧
      (c 0).hom ≫ Functor.whiskerLeft E T.rightDerivedZeroIsoSelf.hom =
        S.rightDerivedZeroIsoSelf.hom ≫ α.hom := by
  let H (q : ℕ) := HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q
  let a := NatIso.mapHomologicalComplex α (ComplexShape.up ℕ)
  let e (q : ℕ) (X : C) (I : InjectiveResolution X) :
      (S.rightDerived q).obj X ≅ (T.rightDerived q).obj (E.obj X) :=
    I.isoRightDerivedObj S q ≪≫ (H q).mapIso (a.app I.cocomplex) ≪≫
      ((I.equivalenceImage E).isoRightDerivedObj T q).symm
  have image_ι {X : C} (I : InjectiveResolution X) :
      (I.equivalenceImage E).ι.f 0 = E.map (I.ι.f 0) := by
    simp [InjectiveResolution.equivalenceImage,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  have natural (q : ℕ) {X Y : C} (f : X ⟶ Y)
      (I : InjectiveResolution X) (J : InjectiveResolution Y) :
      (S.rightDerived q).map f ≫ (e q Y J).hom =
        (e q X I).hom ≫ (T.rightDerived q).map (E.map f) := by
    let φ := InjectiveResolution.desc f J I
    have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 := by simp [φ]
    have hEφ : (I.equivalenceImage E).ι.f 0 ≫
        ((E.mapHomologicalComplex _).map φ).f 0 =
          E.map f ≫ (J.equivalenceImage E).ι.f 0 := by
      simp only [image_ι, Functor.mapHomologicalComplex_map_f, ← E.map_comp, hφ]
    have ha := congrArg (fun z ↦ (H q).map z) (a.hom.naturality φ)
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← assoc, ← assoc,
      I.isoRightDerivedObj_hom_naturality f J φ hφ S q]
    simp only [assoc]
    rw [InjectiveResolution.isoRightDerivedObj_inv_naturality
      (E.map f) (I.equivalenceImage E) (J.equivalenceImage E)
      ((E.mapHomologicalComplex _).map φ) hEφ T q]
    simp only [Functor.map_comp] at ha
    change (I.isoRightDerivedObj S q).hom ≫
        (H q).map ((S.mapHomologicalComplex _).map φ) ≫
        (H q).map (a.hom.app J.cocomplex) ≫ _ =
      (I.isoRightDerivedObj S q).hom ≫ (H q).map (a.hom.app I.cocomplex) ≫
        (H q).map (((E ⋙ T).mapHomologicalComplex _).map φ) ≫ _
    rw [reassoc_of% ha]
  let c (q : ℕ) : S.rightDerived q ≅ E ⋙ T.rightDerived q :=
    NatIso.ofComponents (fun X ↦ e q X (injectiveResolution X))
      (fun f ↦ natural q f _ _)
  refine ⟨c, ?_, ?_⟩
  · intro q X I
    have h := natural q (𝟙 X) (injectiveResolution X) I
    simp only [Functor.map_id, id_comp, comp_id] at h
    change (e q X (injectiveResolution X)).hom ≫ _ = _
    rw [← h]
    simp [e, H, a, NatIso.mapHomologicalComplex]
  · have zero (X : C) (I : InjectiveResolution X) :
        S.toRightDerivedZero.app X ≫ (e 0 X I).hom =
          α.hom.app X ≫ T.toRightDerivedZero.app (E.obj X) := by
      have hc : I.toRightDerivedZero' S ≫
          HomologicalComplex.cyclesMap (a.hom.app I.cocomplex) 0 =
            α.hom.app X ≫ (I.equivalenceImage E).toRightDerivedZero' T := by
        apply (cancel_mono (HomologicalComplex.iCycles _ 0)).1
        simp only [assoc, HomologicalComplex.cyclesMap_i,
          InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
        change S.map (I.ι.f 0) ≫ α.hom.app (I.cocomplex.X 0) =
          α.hom.app X ≫ (I.equivalenceImage E).toRightDerivedZero' T ≫
            HomologicalComplex.iCycles
              ((T.mapHomologicalComplex _).obj (I.equivalenceImage E).cocomplex) 0
        rw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
        rw [image_ι]
        exact α.hom.naturality (I.ι.f 0)
      rw [I.toRightDerivedZero_eq S, (I.equivalenceImage E).toRightDerivedZero_eq T]
      dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      simp only [assoc, Iso.inv_hom_id_assoc]
      change I.toRightDerivedZero' S ≫
          (CochainComplex.isoHomologyπ₀ _).hom ≫
          HomologicalComplex.homologyMap (a.hom.app I.cocomplex) 0 ≫ _ = _
      change I.toRightDerivedZero' S ≫
          HomologicalComplex.homologyπ _ 0 ≫
          HomologicalComplex.homologyMap (a.hom.app I.cocomplex) 0 ≫ _ = _
      rw [HomologicalComplex.homologyπ_naturality_assoc, reassoc_of% hc]
      rfl
    ext X
    apply (cancel_epi (S.toRightDerivedZero.app X)).1
    change S.toRightDerivedZero.app X ≫
        (e 0 X (injectiveResolution X)).hom ≫ T.rightDerivedZeroIsoSelf.hom.app (E.obj X) =
      S.toRightDerivedZero.app X ≫ S.rightDerivedZeroIsoSelf.hom.app X ≫ α.hom.app X
    rw [← assoc, zero, assoc]
    erw [T.rightDerivedZeroIsoSelf_inv_hom_id_app,
      S.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc]
    exact comp_id _

end CategoryTheory
