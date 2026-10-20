/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs

/-! # Differential compatibility for normalized Hom degree maps

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency true
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open scoped ChangeOfRings

namespace CategoryTheory

-- Use the projection API without unfolding the chosen bifunctor.
attribute [local irreducible] homComplexFunctor


set_option backward.isDefEq.respectTransparency false in
private theorem ringExtension_map_pure
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    {M N : RingSiteModules A} (a : M ⟶ N)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : M.val.obj U) :
    (F.map a).val.app U (ringExtensionPure φ F h M U b x) =
      ringExtensionPure φ F h N U b (a.val.app U x) := by
  let : Module A B := Module.compHom B φ
  have hmap : eqToHom (h M).symm ≫ F.map a =
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M a ≫ eqToHom (h N).symm := by
    rw [hm]
    simp
  change ((eqToHom (h M).symm ≫ F.map a).val.app U)
    ((toSheafify ⊥
      (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
        (b ⊗ₜ[A, φ] x)) = _
  rw [hmap]
  change (eqToHom (h N).symm).val.app U
    ((SheafOfModules.changeOfRingsHom (ringSiteMap φ) M a).val.app U
      ((toSheafify ⊥
        (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
          (b ⊗ₜ[A, φ] x))) = _
  apply congrArg ((eqToHom (h N).symm).val.app U)
  let a' : SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) N :=
    { app := fun U ↦ (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (ringSiteMap φ) M a }
  let α := (PresheafOfModules.toPresheaf _).map a'
  have hn := congr_app (toSheafify_naturality (J := ⊥) α) U
  let : Module A B := Module.compHom B φ
  have hv := congrArg (fun f ↦ f (b ⊗ₜ[A] x)) hn
  exact hv.symm

set_option backward.isDefEq.respectTransparency false in
private theorem pure_linear_ext
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    {N : Type u} [AddCommGroup N] [Module B N]
    (f g : (F.obj M).val.obj U →ₗ[B] N)
    (ht : ∀ b x, f (ringExtensionPure φ F h M U b x) =
      g (ringExtensionPure φ F h M U b x)) : f = g := by
  let : Module A B := Module.compHom B φ
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) M
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let α := (eqToHom (h M).symm).val.app U
  have : IsIso α := by
    change IsIso ((SheafOfModules.evaluation _ _).map (eqToHom (h M).symm))
    infer_instance
  have hs := (ConcreteCategory.bijective_of_isIso α).2.comp
    (ConcreteCategory.bijective_of_isIso (η.app U)).2
  ext z
  obtain ⟨z, rfl⟩ := hs z
  induction z using TensorProduct.induction_on with
  | zero => simp [Function.comp_apply]
  | tmul b x => exact ht b x
  | add z w hz hw => simpa only [Function.comp_apply, map_add] using congrArg₂ (· + ·) hz hw

set_option backward.isDefEq.respectTransparency false in
private theorem pure_hom_ext
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) {N : RingSiteModules B} (f g : F.obj M ⟶ N)
    (ht : ∀ U b x, f.val.app U (ringExtensionPure φ F h M U b x) =
      g.val.app U (ringExtensionPure φ F h M U b x)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact pure_linear_ext φ F h M U (f.val.app U).hom (g.val.app U).hom (ht U)

private noncomputable def coordinateValue {A : Type u} [CommRing A]
    {T M N : RingSiteModules A} (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (z : T.val.obj U) (x : M.val.obj U) :
    (T ⟶ SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) →+
      N.val.obj U where
  toFun a := ((a.val.app U z).app (op (Over.mk (𝟙 U.unop)))) x
  map_zero' := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false

private abbrev HomProjection {A : Type u} [CommRing A]
    (P Q H : CochainComplex (RingSiteModules A) ℤ) :=
  ∀ (n p q : ℤ) (_hpq : p + n = q), H.X n ⟶
    SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X q)

private structure HomPresentation {A : Type u} [CommRing A]
    (P Q H : CochainComplex (RingSiteModules A) ℤ) (projection : HomProjection P Q H) :
    Prop where
  isLimit : ∀ n, Nonempty (IsLimit (Fan.mk (H.X n)
    (fun p : ℤ ↦ projection n p (p + n) rfl)))
  differential : ∀ (n m p q q' p' : ℤ), n + 1 = m →
    ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
    H.d n m ≫ projection m p q hpq =
      projection n p q' hq' ≫
        SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
          (𝟙 (P.X p)) (Q.d q' q) -
      n.negOnePow • (projection n p' q hp' ≫
        SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
          (P.d p p') (𝟙 (Q.X q)))

-- Evaluation depends only on the projection data, never its large specification proof.
private noncomputable def projectionValue {A : Type u} [CommRing A]
    {P Q H : CochainComplex (RingSiteModules A) ℤ} (π : HomProjection P Q H)
    (n p q : ℤ) (hpq : p + n = q) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (H.X n).val.obj U) (x : (P.X p).val.obj U) : (Q.X q).val.obj U :=
  (((π n p q hpq).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x

private abbrev CanonicalProjection {A : Type u} [CommRing A]
    (P Q H : CochainComplex (RingSiteModules A) ℤ) :=
  ∀ n p : ℤ, H.X n ⟶ SheafOfModules.homObj
    (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X (p + n))

private noncomputable def canonicalValue {A : Type u} [CommRing A]
    {P Q H : CochainComplex (RingSiteModules A) ℤ} (π : CanonicalProjection P Q H)
    (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (H.X n).val.obj U) (x : (P.X p).val.obj U) : (Q.X (p + n)).val.obj U :=
  (((π n p).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x

private noncomputable def fullProjection {A : Type u} [CommRing A]
    {P Q H : CochainComplex (RingSiteModules A) ℤ} (π : CanonicalProjection P Q H) :
    HomProjection P Q H := fun n p _q hpq ↦ hpq ▸ π n p

private theorem projectionValue_d {A : Type u} [CommRing A]
    {P Q H : CochainComplex (RingSiteModules A) ℤ} {π : HomProjection P Q H}
    (D : HomPresentation P Q H π)
    (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (H.X n).val.obj U) (x : (P.X p).val.obj U) :
    projectionValue π m p q hpq U ((H.d n m).val.app U f) x =
      (Q.d q' q).val.app U (projectionValue π n p q' hq' U f x) -
        (n.negOnePow : ℤ) • projectionValue π n p' q hp' U f ((P.d p p').val.app U x) := by
  have hd := congrArg (coordinateValue U f x)
    (D.differential n m p q q' p' hnm hpq hq' hp')
  rw [map_sub, Units.smul_def, map_zsmul] at hd
  exact hd

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pureAddHom
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) :
    M.val.obj U →+ (F.obj M).val.obj U where
  toFun := ringExtensionPure φ F h M U b
  map_zero' := by
    let : Module A B := Module.compHom B φ
    simp only [ringExtensionPure, TensorProduct.tmul_zero, map_zero]
  map_add' x y := by
    let : Module A B := Module.compHom B φ
    simp only [ringExtensionPure, TensorProduct.tmul_add, map_add]

-- Keep scalar-extension sheafification folded in the coordinate calculation.
attribute [local irreducible] ringExtensionPure

set_option maxHeartbeats 100000 in
-- The two tensor inductions and internal-Hom extensionality need this elaboration budget.
private theorem normalized_differential
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q HA : CochainComplex (RingSiteModules A) ℤ)
    (HB : CochainComplex (RingSiteModules B) ℤ) (πAc : CanonicalProjection P Q HA)
    (πBc : CanonicalProjection ((ringExtensionComplex F hF).obj P)
      ((ringExtensionComplex F hF).obj Q) HB)
    (DA : HomPresentation P Q HA (fullProjection πAc))
    (DB : HomPresentation ((ringExtensionComplex F hF).obj P)
      ((ringExtensionComplex F hF).obj Q) HB (fullProjection πBc))
    (t : ∀ n, F.obj (HA.X n) ⟶ HB.X n) (n : ℤ)
    (ht : ∀ (k p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (HA.X k).val.obj U) (x : (P.X p).val.obj U),
      canonicalValue πBc k p U
        ((t k).val.app U (ringExtensionPure φ F h (HA.X k) U b f))
        (ringExtensionPure φ F h (P.X p) U c x) =
      ringExtensionPure φ F h (Q.X (p + k)) U (b * c)
        (canonicalValue πAc k p U f x)) :
    t n ≫ HB.d n (n + 1) = F.map (HA.d n (n + 1)) ≫ t (n + 1) := by
  classical
  let πA := fullProjection πAc
  let πB := fullProjection πBc
  let : F.Additive := hF
  let FP := (ringExtensionComplex F hF).obj P
  let FQ := (ringExtensionComplex F hF).obj Q
  have ht' (k i j : ℤ) (hij : i + k = j)
      (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (z : (HA.X k).val.obj U) (y : (P.X i).val.obj U) :
      projectionValue πB k i j hij U
        ((t k).val.app U (ringExtensionPure φ F h (HA.X k) U b z))
        (ringExtensionPure φ F h (P.X i) U c y) =
      ringExtensionPure φ F h (Q.X j) U (b * c)
        (projectionValue πA k i j hij U z y) := by
    subst j
    exact ht k i U b c z y
  obtain ⟨hB⟩ := DB.isLimit (n + 1)
  apply hB.hom_ext
  intro p
  change (t n ≫ HB.d n (n + 1)) ≫
      πB (n + 1) p.as (p.as + (n + 1)) rfl =
    (F.map (HA.d n (n + 1)) ≫ t (n + 1)) ≫
      πB (n + 1) p.as (p.as + (n + 1)) rfl
  apply pure_hom_ext φ F h (HA.X n)
  intro U b f
  rcases U with ⟨⟨⟨⟩⟩⟩
  apply PresheafOfModules.hom_ext
  intro W
  have hW : W = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
    rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, a⟩⟩
    rfl
  subst W
  apply ModuleCat.hom_ext
  apply pure_linear_ext φ F h (P.X p.as) (op ⟨PUnit.unit⟩)
  intro c x
  let U : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩
  let p₀ := p.as
  let q := p₀ + (n + 1)
  let q' := p₀ + n
  let p' := p₀ + 1
  have hp' : p' + n = q := by dsimp [p', q]; omega
  change projectionValue πB (n + 1) p₀ q rfl U
      ((HB.d n (n + 1)).val.app U
        ((t n).val.app U (ringExtensionPure φ F h (HA.X n) U b f)))
      (ringExtensionPure φ F h (P.X p₀) U c x) =
    projectionValue πB (n + 1) p₀ q rfl U
      ((t (n + 1)).val.app U
        ((F.map (HA.d n (n + 1))).val.app U
          (ringExtensionPure φ F h (HA.X n) U b f)))
      (ringExtensionPure φ F h (P.X p₀) U c x)
  rw [projectionValue_d DB n (n + 1) p₀ q q' p' rfl rfl rfl hp']
  change @Sub.sub ((F.obj (Q.X q)).val.obj U) _
      ((F.map (Q.d q' q)).val.app U
        (projectionValue πB n p₀ q' rfl U
          ((t n).val.app U (ringExtensionPure φ F h (HA.X n) U b f))
          (ringExtensionPure φ F h (P.X p₀) U c x)))
      ((n.negOnePow : ℤ) • projectionValue πB n p' q hp' U
        ((t n).val.app U (ringExtensionPure φ F h (HA.X n) U b f))
        ((F.map (P.d p₀ p')).val.app U (ringExtensionPure φ F h (P.X p₀) U c x))) = _
  rw [ringExtension_map_pure φ F h hm (P.d p₀ p'),
    ringExtension_map_pure φ F h hm (HA.d n (n + 1))]
  have ht'' (k i j : ℤ) (hij : i + k = j)
      (z : (HA.X k).val.obj U) (y : (P.X i).val.obj U) :
      projectionValue πB k i j hij U
        ((t k).val.app U (ringExtensionPure φ F h (HA.X k) U b z))
        (ringExtensionPure φ F h (P.X i) U c y) =
      ringExtensionPure φ F h (Q.X j) U (b * c)
        (projectionValue πA k i j hij U z y) := ht' k i j hij U b c z y
  rw [ht'', ht'', ht'', ringExtension_map_pure φ F h hm]
  rw [projectionValue_d DA n (n + 1) p₀ q q' p' rfl rfl rfl hp']
  change _ = (pureAddHom φ F h (Q.X q) U (b * c)) (_ - (n.negOnePow : ℤ) • _)
  rw [map_sub, map_zsmul]
  rfl

private theorem canonicalPresentation {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) :
    HomPresentation P Q (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)
      (fullProjection (ringHomComplexProjection P Q)) := by
  let π := (homComplex_projections_exists
    (R := CochainComplex.onePointRingSheaf A)).choose P Q
  have hπ (n p q : ℤ) (hpq : p + n = q) :
      fullProjection (ringHomComplexProjection P Q) n p q hpq = π n p q hpq := by
    subst q
    rfl
  constructor
  · exact (homComplex_projections_exists
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.1 P Q
  · intro n m p q q' p' hnm hpq hq' hp'
    rw [hπ, hπ, hπ]
    exact (homComplex_projections_exists
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.2.1
      P Q n m p q q' p' hnm hpq hq' hp'

set_option backward.isDefEq.respectTransparency true in
/-- Adjacent-degree differential compatibility for normalized maps.
This is the pure-tensor calculation from the Hom-complex differential formula.
Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential-adjacent).
Proof: compose with each target product projection, then use the supplied evaluation
formula on pure tensors in both arguments. The two terms are respectively the
postcomposition by `d_Q` and the signed precomposition by `d_P`; naturality of the
extension unit and additivity of `F` identify the corresponding extended terms.
Tensor-product induction and internal-Hom extensionality finish the equality. -/
theorem ringHomExtension_differential_adjacent
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (_hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ)
    (t : ∀ n : ℤ,
      F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf B)
          ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).X n)
    (n : ℤ) (ht : ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hF).obj P)
        ((ringExtensionComplex F hF).obj Q) n p U
        ((t n).val.app U (ringExtensionPure φ F h _ U b f))
        (ringExtensionPure φ F h (P.X p) U c x) =
      ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) :
    t n ≫ (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).d n (n + 1) =
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).d n (n + 1) ≫ t (n + 1) := by
  exact normalized_differential φ F h _hm hF P Q
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)
    (homComplex (R := CochainComplex.onePointRingSheaf B)
      ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q))
    (ringHomComplexProjection P Q)
    (ringHomComplexProjection ((ringExtensionComplex F hF).obj P)
      ((ringExtensionComplex F hF).obj Q))
    (canonicalPresentation P Q)
    (canonicalPresentation ((ringExtensionComplex F hF).obj P)
      ((ringExtensionComplex F hF).obj Q)) t n ht

set_option backward.isDefEq.respectTransparency false in
/-- Any degree maps with the normalized tensor-Hom formula commute with differentials.
Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential).
Proof: in adjacent degrees use `ringHomExtension_differential_adjacent`. In all other
degrees both differentials are zero by the complex shape, so both composites vanish. -/
theorem ringHomExtension_differential
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ)
    (t : ∀ n : ℤ,
      F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf B)
          ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).X n)
    (ht : ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hF).obj P)
        ((ringExtensionComplex F hF).obj Q) n p U
        ((t n).val.app U (ringExtensionPure φ F h _ U b f))
        (ringExtensionPure φ F h (P.X p) U c x) =
      ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) :
    ∀ n m : ℤ,
      t n ≫ (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).d n m =
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).d n m ≫ t m := by
  intro n m
  by_cases hnm : n + 1 = m
  · subst m
    exact ringHomExtension_differential_adjacent φ F h hm hF P Q t n ht
  · rw [((homComplex (R := CochainComplex.onePointRingSheaf B)
      ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).shape n m hnm),
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).shape n m hnm,
      comp_zero, zero_comp]

end CategoryTheory
