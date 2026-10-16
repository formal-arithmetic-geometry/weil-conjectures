/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.CategoryTheory.ExactCouple

/-!
# Exchange on truncation exact couples

Source: Stacks Project, Tag 0DDE, proof, with the truncation construction of Tags
08J5, 0148 and 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism).
-/

@[expose] public section

set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.TruncationExchange

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- Upper truncation in D+, using the standard t-structure.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev trunc (K : DerivedCategory.Plus A) (q : ℤ) :=
  (DerivedCategory.Plus.TStructure.t.truncLE q).obj K

/-- The sheaf H^q(K) placed in degree zero.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev sheaf (K : DerivedCategory.Plus A) (q : ℤ) :=
  (DerivedCategory.Plus.singleFunctor A 0).obj
    ((DerivedCategory.Plus.homologyFunctor A q).obj K)

/-- The layer H^q(K)[-q].
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev layer (K : DerivedCategory.Plus A) (q : ℤ) :=
  (sheaf K q)⟦-q⟧

/-- The canonical inclusion of consecutive upper truncations.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def inclusion (K : DerivedCategory.Plus A) (q : ℤ) :
    trunc K (q - 1) ⟶ trunc K q :=
  (DerivedCategory.Plus.TStructure.t.natTransTruncLEOfLE (q - 1) q (by omega)).app K

/-- The canonical identification H^q(H^q(K)[-q]) = H^q(K).
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def layerIso (K : DerivedCategory.Plus A) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor A q).obj (layer K q) ≅
      (DerivedCategory.Plus.homologyFunctor A q).obj K :=
  ((DerivedCategory.Plus.homologyFunctor A 0).shiftIso (-q) q 0 (by omega)).app
      (sheaf K q) ≪≫
    (DerivedCategory.homologyFunctor A 0).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso A 0).app
        ((DerivedCategory.Plus.homologyFunctor A q).obj K)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app
      ((DerivedCategory.Plus.homologyFunctor A q).obj K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The projection and connecting morphism of the canonical truncation triangle exist.
The projection is characterized by the cohomology of the inclusion into K.
Proof: use the standard t-structure's distinguished triangle of consecutive
truncations. Its third term and H^q(K)[-q] are concentrated in degree q.
The degree-q homology functor is bijective on morphisms between these objects.
Lift the isomorphism obtained from the homology of the truncation projection,
the inclusion into K and layerIso. This lift is an isomorphism: in degree q it
induces that isomorphism, and in every other degree both homology objects vanish.
Transport the distinguished triangle along the lift. The choice of its homology
map gives exactly the displayed normalization of the projection.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
theorem exists_triangle (K : DerivedCategory.Plus A) (q : ℤ) :
    ∃ j : trunc K q ⟶ layer K q,
      ∃ k : layer K q ⟶ (trunc K (q - 1))⟦(1 : ℤ)⟧,
        (DerivedCategory.Plus.homologyFunctor A q).map j ≫ (layerIso K q).hom =
          (DerivedCategory.Plus.homologyFunctor A q).map
            ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K) ∧
        Triangle.mk (inclusion K q) j k ∈ distTriang (DerivedCategory.Plus A) := by
  let t := DerivedCategory.Plus.TStructure.t (C := A)
  let H := DerivedCategory.Plus.homologyFunctor A
  let T := (t.triangleLTLTGELT ((q - 1) + 1) (q + 1) (by omega)).obj K
  have hT : T ∈ distTriang _ := t.triangleLTLTGELT_distinguished _ _ (by omega) K
  have h₃ge : t.IsGE T.obj₃ q := by
    change t.IsGE ((t.truncGELT ((q - 1) + 1) (q + 1)).obj K) q
    exact t.isGE_of_ge _ q ((q - 1) + 1) (by omega)
  have h₃le : t.IsLE T.obj₃ q := by
    change t.IsLE ((t.truncGELT ((q - 1) + 1) (q + 1)).obj K) q
    exact t.isLE_of_le _ ((q + 1) - 1) q (by omega)
  have hlge : t.IsGE (layer K q) q := t.isGE_shift (sheaf K q) 0 (-q) q (by omega)
  have hlle : t.IsLE (layer K q) q := t.isLE_shift (sheaf K q) 0 (-q) q (by omega)
  have hproj : IsIso ((H q).map T.mor₂) :=
    DerivedCategory.Plus.isIso_homologyFunctor_map_truncGEπ_app
      (trunc K q) ((q - 1) + 1) q (by omega)
  have hinc : IsIso ((H q).map ((t.truncLEι q).app K)) :=
    DerivedCategory.Plus.isIso_homologyFunctor_map_truncLTι_app K (q + 1) q (by omega)
  have hbij : Function.Bijective (fun e : T.obj₃ ⟶ layer K q ↦ (H q).map e) :=
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE q).comp
      ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).map_bijective _ _)
  let d := inv ((H q).map T.mor₂) ≫
    (H q).map ((t.truncLEι q).app K) ≫ (layerIso K q).inv
  obtain ⟨e, he⟩ := hbij.2 d
  dsimp only at he
  have heiso : IsIso e := by
    apply (DerivedCategory.Plus.isIso_iff e).2
    intro n
    by_cases hn : n = q
    · subst n
      change IsIso ((H q).map e)
      rw [he]
      dsimp only [d]
      infer_instance
    · have z (L : DerivedCategory.Plus A) [L.IsGE q] [L.IsLE q] :
          IsZero ((H n).obj L) := by
        rcases lt_or_gt_of_ne hn with h | h
        · exact DerivedCategory.Plus.isZero_homology_of_isGE L q n h
        · exact DerivedCategory.Plus.isZero_homology_of_isLE L q n h
      exact (z T.obj₃).isIso (z (layer K q)) _
  let j := T.mor₂ ≫ e
  let k := inv e ≫ T.mor₃
  refine ⟨j, k, ?_, ?_⟩
  · change (H q).map j ≫ (layerIso K q).hom =
      (H q).map ((t.truncLEι q).app K)
    dsimp only [j]
    rw [Functor.map_comp, he]
    simp [d, Category.assoc]
  · apply isomorphic_distinguished _ hT
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso e).symm ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp [j]
    · simp [k]

/-- The canonical projection in the truncation triangle, chosen by its characterization.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def projection (K : DerivedCategory.Plus A) (q : ℤ) :
    trunc K q ⟶ layer K q :=
  (exists_triangle K q).choose

/-- The connecting arrow in the canonical truncation triangle.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def boundary (K : DerivedCategory.Plus A) (q : ℤ) :
    layer K q ⟶ (trunc K (q - 1))⟦(1 : ℤ)⟧ :=
  (exists_triangle K q).choose_spec.choose

/-- D^{p,q} = H^{p+q}(F tau_{<=q}K).
Source: Stacks 0DDE, 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def D (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).obj (F.obj (trunc K q))

/-- E^{p,q} = H^{p+q}(F(H^q(K)[-q])).
Source: Stacks 0DDE, 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def E (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).obj (F.obj (layer K q))

/-- The inclusion map of bidegree (-1,1), with the total degree transported.
Source: Stacks 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def alpha (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : D F K p q ⟶ D F K (p - 1) (q + 1) :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map
    (F.map (eqToHom (congrArg (trunc K) (by omega : q = (q + 1) - 1)) ≫
      inclusion K (q + 1))) ≫
    eqToHom (congrArg (fun n : ℤ => (DerivedCategory.Plus.homologyFunctor B n).obj
      (F.obj (trunc K (q + 1)))) (by omega : p + q = (p - 1) + (q + 1)))

/-- The projection map of bidegree (0,0).
Source: Stacks 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def g (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : D F K p q ⟶ E F K p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (F.map (projection K q))

/-- The connecting map of bidegree (2,-1), using F's composite shift isomorphism.
Source: Stacks 0148, 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def f (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [F.CommShift ℤ] (K : DerivedCategory.Plus A) (p q : ℤ) :
    E F K p q ⟶ D F K (p + 2) (q - 1) :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map
      (F.map (boundary K q) ≫ (F.commShiftIso (1 : ℤ)).hom.app (trunc K (q - 1))) ≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso
      (1 : ℤ) (p + q) ((p + 2) + (q - 1)) (by omega)).hom.app (F.obj (trunc K (q - 1)))

/-- The canonical comparison E^{p,q} = H^p(F H^q(K)), via the iterated shift isomorphism.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def pageIso (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [F.CommShift ℤ] (K : DerivedCategory.Plus A) (p q : ℤ) :
    E F K p q ≅ (DerivedCategory.Plus.homologyFunctor B p).obj (F.obj (sheaf K q)) :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).mapIso
      ((F.commShiftIso (-q)).app (sheaf K q)) ≪≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega)).app
      (F.obj (sheaf K q))

/-- Cohomology of a transformation on the truncation terms.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def tD {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (t : F ⟶ G) (K : DerivedCategory.Plus A) (p q : ℤ) : D F K p q ⟶ D G K p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (t.app (trunc K q))

/-- Cohomology of a transformation on the layers.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def tE {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (t : F ⟶ G) (K : DerivedCategory.Plus A) (p q : ℤ) : E F K p q ⟶ E G K p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (t.app (layer K q))

private lemma exact_transport {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) (hS : S.Exact) {X Y Z : C}
    (a : X ≅ S.X₁) (b : Y ≅ S.X₂) (c : Z ≅ S.X₃)
    (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : i ≫ b.hom = a.hom ≫ S.f) (hj : j ≫ c.hom = b.hom ≫ S.g) :
    ∃ h : i ≫ j = 0, (ShortComplex.mk i j h).Exact := by
  have h : i ≫ j = 0 := by
    apply (cancel_mono c.hom).1
    rw [Category.assoc, hj, ← Category.assoc, hi, Category.assoc, S.zero,
      comp_zero, zero_comp]
  exact ⟨h, ShortComplex.exact_of_iso (ShortComplex.isoMk a b c hi.symm hj.symm).symm hS⟩

private lemma triangle_distinguished (K : DerivedCategory.Plus A) (q : ℤ) :
    Triangle.mk (inclusion K q) (projection K q) (boundary K q) ∈
      distTriang (DerivedCategory.Plus A) :=
  (exists_triangle K q).choose_spec.choose_spec.2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma exact_g_f
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) (p q : ℤ) :
    ∃ h : g F K p q ≫ f F K p q = 0,
      (ShortComplex.mk (g F K p q) (f F K p q) h).Exact := by
  let T := F.mapTriangle.obj
    (Triangle.mk (inclusion K q) (projection K q) (boundary K q))
  have hT : T ∈ distTriang _ := F.map_distinguished _ (triangle_distinguished K q)
  exact ⟨(DerivedCategory.Plus.homologyFunctor B 0).comp_homologySequenceδ T hT
      (p + q) ((p + 2) + (q - 1)) (by omega),
    (DerivedCategory.Plus.homologyFunctor B 0).homologySequence_exact₃ T hT
      (p + q) ((p + 2) + (q - 1)) (by omega)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma exact_alpha_g
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) (p q : ℤ) :
    ∃ h : alpha F K p q ≫ g F K (p - 1) (q + 1) = 0,
      (ShortComplex.mk (alpha F K p q) (g F K (p - 1) (q + 1)) h).Exact := by
  let H := DerivedCategory.Plus.homologyFunctor B
  let T := F.mapTriangle.obj
    (Triangle.mk (inclusion K (q + 1)) (projection K (q + 1)) (boundary K (q + 1)))
  have hT : T ∈ distTriang _ := F.map_distinguished _ (triangle_distinguished K (q + 1))
  let S := (shortComplexOfDistTriangle T hT).map (H (p + q))
  have hS : S.Exact := (H (p + q)).map_distinguished_exact T hT
  let a : D F K p q ≅ S.X₁ := eqToIso
    (congrArg (fun i ↦ (H (p + q)).obj (F.obj (trunc K i)))
      (by omega : q = (q + 1) - 1))
  let b : D F K (p - 1) (q + 1) ≅ S.X₂ := eqToIso
    (congrArg (fun n ↦ (H n).obj (F.obj (trunc K (q + 1))))
      (by omega : (p - 1) + (q + 1) = p + q))
  let c : E F K (p - 1) (q + 1) ≅ S.X₃ := eqToIso
    (congrArg (fun n ↦ (H n).obj (F.obj (layer K (q + 1))))
      (by omega : (p - 1) + (q + 1) = p + q))
  apply exact_transport S hS a b c
  · simp [a, b, alpha, S, T, H, Functor.map_comp, eqToHom_map, Category.assoc]
  · exact eqToHom_naturality
      (fun n ↦ (H n).map (F.map (projection K (q + 1)))) (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma exact_f_alpha
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) (p q : ℤ) :
    ∃ h : f F K p q ≫ alpha F K (p + 2) (q - 1) = 0,
      (ShortComplex.mk (f F K p q) (alpha F K (p + 2) (q - 1)) h).Exact := by
  let H := DerivedCategory.Plus.homologyFunctor B
  let T := F.mapTriangle.obj
    (Triangle.mk (inclusion K q) (projection K q) (boundary K q))
  have hT : T ∈ distTriang _ := F.map_distinguished _ (triangle_distinguished K q)
  let S := ShortComplex.mk _ _ ((H 0).homologySequenceδ_comp T hT
    (p + q) ((p + 2) + (q - 1)) (by omega))
  have hS : S.Exact := (H 0).homologySequence_exact₁ T hT
    (p + q) ((p + 2) + (q - 1)) (by omega)
  let c : D F K ((p + 2) - 1) ((q - 1) + 1) ≅ S.X₃ :=
    eqToIso (congrArg
      (fun n ↦ (H n).obj (F.obj (trunc K ((q - 1) + 1))))
      (by omega : ((p + 2) - 1) + ((q - 1) + 1) = (p + 2) + (q - 1))) ≪≫
    eqToIso (congrArg
      (fun r ↦ (H ((p + 2) + (q - 1))).obj (F.obj (trunc K r)))
      (by omega : (q - 1) + 1 = q))
  apply exact_transport S hS (Iso.refl _) (Iso.refl _) c
  · change f F K p q ≫ 𝟙 _ = 𝟙 _ ≫ S.f
    rw [Category.comp_id, Category.id_comp]
    rfl
  · change alpha F K (p + 2) (q - 1) ≫ c.hom =
      𝟙 _ ≫ (H ((p + 2) + (q - 1))).map (F.map (inclusion K q))
    rw [Category.id_comp]
    dsimp only [alpha, c, Iso.trans_hom, eqToIso.hom]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
    rw [eqToHom_naturality
      (fun r ↦ (H ((p + 2) + (q - 1))).map (F.map (inclusion K r)))
      (by omega : (q - 1) + 1 = q)]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

private noncomputable def gShifted
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) :
    D F K p q ⟶ E F K (p + ((0 : ℕ) : ℤ)) (q - ((0 : ℕ) : ℤ)) :=
  g F K p q ≫ eqToHom (by simp)

set_option backward.isDefEq.respectTransparency false in
private lemma exact_gShifted_f
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) (p q : ℤ) :
    ∃ h : gShifted F K p q ≫ f F K (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
      (ShortComplex.mk _ _ h).Exact := by
  let S := ShortComplex.mk _ _ (exact_g_f F K p q).choose
  let b : E F K (p + (0 : ℕ)) (q - (0 : ℕ)) ≅ S.X₂ := eqToIso (by simp [S])
  let c : D F K ((p + (0 : ℕ)) + 2) ((q - (0 : ℕ)) - 1) ≅ S.X₃ :=
    eqToIso (by simp [S])
  apply exact_transport S (exact_g_f F K p q).choose_spec (Iso.refl _) b c
  · dsimp only [gShifted, b, S, Iso.refl_hom, eqToIso.hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Category.id_comp]
  · exact eqToHom_naturality (fun i : ℤ × ℤ ↦ f F K i.1 i.2)
      (by simp : (p + (0 : ℕ), q - (0 : ℕ)) = (p, q))

private lemma exact_alpha_gShifted
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) (p q : ℤ) :
    ∃ h : alpha F K p q ≫ gShifted F K (p - 1) (q + 1) = 0,
      (ShortComplex.mk _ _ h).Exact := by
  let S := ShortComplex.mk _ _ (exact_alpha_g F K p q).choose
  let c : E F K ((p - 1) + (0 : ℕ)) ((q + 1) - (0 : ℕ)) ≅ S.X₃ :=
    eqToIso (by simp [S])
  apply exact_transport S (exact_alpha_g F K p q).choose_spec
    (Iso.refl _) (Iso.refl _) c
  · change alpha F K p q ≫ 𝟙 _ = 𝟙 _ ≫ alpha F K p q
    rw [Category.comp_id, Category.id_comp]
  · dsimp only [gShifted, c, S, Iso.refl_hom, eqToIso.hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Category.id_comp]

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private noncomputable def couple
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) : BigradedExactCouple B 0 :=
  BigradedExactCouple.ofShifted (D F K) (E F K) (alpha F K) (f F K) (gShifted F K)
    (fun p q ↦ (exact_f_alpha F K p q).choose)
    (fun p q ↦ (exact_gShifted_f F K p q).choose)
    (fun p q ↦ (exact_alpha_gShifted F K p q).choose)
    (fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
      (exact_f_alpha F K p q).choose_spec)
    (fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
      (exact_gShifted_f F K p q).choose_spec)
    (fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
      (exact_alpha_gShifted F K p q).choose_spec)
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma couple_data
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) :
    (couple F K).D = D F K ∧ (couple F K).E = E F K ∧
      HEq (couple F K).alpha (alpha F K) ∧
      HEq (couple F K).f (f F K) ∧ HEq (couple F K).g (g F K) := by
  sorry
-/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma alpha_naturality
    {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B} (t : F ⟶ G)
    (K : DerivedCategory.Plus A) (p q : ℤ) :
    alpha F K p q ≫ tD t K (p - 1) (q + 1) = tD t K p q ≫ alpha G K p q := by
  dsimp [alpha, tD]
  rw [Category.assoc, ← eqToHom_naturality
    (fun n ↦ (DerivedCategory.Plus.homologyFunctor B n).map (t.app (trunc K (q + 1))))
      (by omega : p + q = (p - 1) + (q + 1))]
  simp only [← Category.assoc, ← Functor.map_comp, t.naturality]

private lemma g_naturality
    {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B} (t : F ⟶ G)
    (K : DerivedCategory.Plus A) (p q : ℤ) :
    g F K p q ≫ tE t K p q = tD t K p q ≫ g G K p q := by
  simpa only [g, tE, tD, ← Functor.map_comp] using
    congrArg (DerivedCategory.Plus.homologyFunctor B (p + q)).map
      (t.naturality (projection K q))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma f_naturality
    {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [F.CommShift ℤ] [G.CommShift ℤ] (t : F ⟶ G) [NatTrans.CommShift t ℤ]
    (K : DerivedCategory.Plus A) (p q : ℤ) :
    f F K p q ≫ tD t K (p + 2) (q - 1) = tE t K p q ≫ f G K p q := by
  let H := DerivedCategory.Plus.homologyFunctor B
  let e := (H 0).shiftIso (1 : ℤ) (p + q) ((p + 2) + (q - 1)) (by omega)
  have hs : (H (p + q)).map ((t.app (trunc K (q - 1)))⟦(1 : ℤ)⟧') ≫
      e.hom.app (G.obj (trunc K (q - 1))) =
    e.hom.app (F.obj (trunc K (q - 1))) ≫
      (H ((p + 2) + (q - 1))).map (t.app (trunc K (q - 1))) :=
    e.hom.naturality _
  dsimp only [f, tD, tE, D, E]
  rw [Category.assoc, ← hs]
  simp only [← Category.assoc]
  apply congrArg (fun z ↦ z ≫ e.hom.app (G.obj (trunc K (q - 1))))
  change (H (p + q)).map
      (F.map (boundary K q) ≫ (F.commShiftIso (1 : ℤ)).hom.app (trunc K (q - 1))) ≫
      (H (p + q)).map ((t.app (trunc K (q - 1)))⟦(1 : ℤ)⟧') =
    (H (p + q)).map (t.app (layer K q)) ≫
      (H (p + q)).map
        (G.map (boundary K q) ≫ (G.commShiftIso (1 : ℤ)).hom.app (trunc K (q - 1)))
  simp only [← Functor.map_comp]
  congr 1
  rw [Category.assoc, NatTrans.shift_app_comm t, ← Category.assoc, t.naturality,
    Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma pageIso_naturality
    {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [F.CommShift ℤ] [G.CommShift ℤ] (t : F ⟶ G) [NatTrans.CommShift t ℤ]
    (K : DerivedCategory.Plus A) (p q : ℤ) :
    tE t K p q ≫ (pageIso G K p q).hom =
      (pageIso F K p q).hom ≫
        (DerivedCategory.Plus.homologyFunctor B p).map (t.app (sheaf K q)) := by
  let H := DerivedCategory.Plus.homologyFunctor B
  let e := (H 0).shiftIso (-q) (p + q) p (by omega)
  have hs : (H (p + q)).map ((t.app (sheaf K q))⟦-q⟧') ≫
      e.hom.app (G.obj (sheaf K q)) =
    e.hom.app (F.obj (sheaf K q)) ≫ (H p).map (t.app (sheaf K q)) :=
    e.hom.naturality _
  change (H (p + q)).map (t.app (layer K q)) ≫
      ((H (p + q)).map ((G.commShiftIso (-q)).hom.app (sheaf K q)) ≫
        e.hom.app (G.obj (sheaf K q))) =
    ((H (p + q)).map ((F.commShiftIso (-q)).hom.app (sheaf K q)) ≫
      e.hom.app (F.obj (sheaf K q))) ≫ (H p).map (t.app (sheaf K q))
  rw [← Category.assoc, ← Functor.map_comp, ← NatTrans.shift_app_comm t (-q),
    Functor.map_comp, Category.assoc, hs, Category.assoc]

end CategoryTheory.TruncationExchange

namespace AlgebraicGeometry.Etale

open CategoryTheory.TruncationExchange

/-- Phi = g inverse image after Rf pushforward.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev truncationPhi {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :=
  (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus ⋙
    (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus

/-- Psi = Rf' pushforward after g' inverse image.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev truncationPsi {X' X Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') :=
  (upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus ⋙
    (lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus

/-- H^p(Phi M) identifies with g inverse image of R^p f_* M.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def truncationSourceIso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ) :
    (_root_.DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
        ((truncationPhi f g).obj ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso p).symm.app
    ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))

/-- H^p(Psi M) identifies with R^p f'_* of g' inverse image of M.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def truncationTargetIso {X' X Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ) :
    (_root_.DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
        ((truncationPsi g' f').obj ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
    (_root_.DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
        ((lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus.obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} g').obj M))) :=
  (_root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus.mapIso
        (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusSingleFunctor 0).app M))

/-- The exchange maps give a morphism of the two truncation exact couples, and on
E they identify with the degree-p exchange of H^q(K).

Proof:
1. Construct the normalized truncation triangles by exists_triangle. Exact inverse
   image and right derived direct image are triangulated with their recorded shift
   isomorphisms, so both composite functors send these triangles to distinguished ones.
2. Apply the long exact homology sequence to each image triangle. Transport the
   total degrees along the displayed integer equalities to obtain the three exact
   short complexes. The shifted-map constructor packages them as exact couples.
3. Naturality gives the inclusion and projection squares. For the connecting square,
   use naturality for boundary, compatibility of exchange with shift by 1, and
   naturality of the homology shift isomorphism.
4. Apply the same shift compatibility at -q to the sheaf H^q(K). Naturality of the
   homology shift isomorphism gives the pageIso square. Compose with the target
   comparison and insert the cancelling source comparison and its inverse to obtain
   the stated degree-p exchange formula.
Source: Stacks 0DDE, proof, and 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
theorem truncation_exchange_couple_morphism
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (∃ P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0,
      P.D = D (truncationPhi f g) K ∧ Q.D = D (truncationPsi g' f') K ∧
      P.E = E (truncationPhi f g) K ∧ Q.E = E (truncationPsi g' f') K ∧
      HEq P.alpha (alpha (truncationPhi f g) K) ∧
      HEq Q.alpha (alpha (truncationPsi g' f') K) ∧
      HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) ∧
      HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) ∧
      HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) ∧
      HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K)) ∧
    (∀ p q : ℤ,
      alpha (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p - 1) (q + 1) =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          alpha (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.g (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.f (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p + 2) (q - 1) =
        tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.f (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          (pageIso (truncationPsi g' f') K p q ≪≫
            truncationTargetIso g' f'
              ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom =
        (pageIso (truncationPhi f g) K p q ≪≫
          truncationSourceIso f g
            ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom ≫
        (truncationSourceIso f g
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).inv ≫
        (_root_.DerivedCategory.Plus.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app (sheaf K q)) ≫
        (truncationTargetIso g' f'
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom) := by
  sorry

end AlgebraicGeometry.Etale
