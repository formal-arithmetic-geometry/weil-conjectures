/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4, SHEAF group N4
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.CategoryTheory
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Sheaf.Algebra.Homology.HomComplex

/-! # Flat terms of the finite-projective ring dual

Source: Stacks Project, More on Algebra, Tags 0A6A and 064K;
Modules on Sites, Tag 03ET.
(blueprint: lem-pc-perfect-ring-dual-term-flat)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The actual Hom complex into the ring in degree zero; no dual object is chosen.
Source: Stacks Project, More on Algebra, Tag 0A6A, finite-projective argument.
(blueprint: lem-pc-perfect-ring-dual-term-flat) -/
noncomputable def perfectRingDual {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) :
    CochainComplex (RingSiteModules A) ℤ :=
  homComplex (R := CochainComplex.onePointRingSheaf A) P
    ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))))

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private lemma slice_unique (U : Discrete PUnit.{u + 1})
    (W : Over U) : W = Over.mk (𝟙 U) := by
  cases U with
  | mk U =>
    cases U
    cases W
    aesop

private noncomputable def pointPreimage {A : Type u} [CommRing A]
    {M N : RingSiteModules A} (f : M.val.obj point ⟶ N.val.obj point) :
    M.val ⟶ N.val where
  app X := by
    obtain rfl : X = point := Subsingleton.elim _ _
    exact f
  naturality {X Y} g := by
    obtain rfl : X = point := Subsingleton.elim _ _
    obtain rfl : Y = point := Subsingleton.elim _ _
    obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
    ext x
    simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homPointEquiv {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    ((SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj point)
      ≃ₗ[A] (M.val.obj point →ₗ[A] N.val.obj point) := by
  let f : ((SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
      M N).val.obj point) →ₗ[A] (M.val.obj point →ₗ[A] N.val.obj point) :=
    { toFun φ := (φ.app (op (Over.mk (𝟙 point.unop)))).hom
      map_add' _ _ := rfl
      map_smul' a φ := by
        ext x
        rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro φ ψ h
    apply PresheafOfModules.hom_ext
    intro W
    obtain ⟨W⟩ := W
    obtain rfl := slice_unique point.unop W
    exact ModuleCat.hom_ext h
  · intro g
    refine ⟨(PresheafOfModules.restrictOver (CochainComplex.onePointRingSheaf A).obj
      point.unop).map (pointPreimage (ModuleCat.ofHom g)), ?_⟩
    rfl

private theorem homObj_zero_target {A : Type u} [CommRing A]
    (M N : RingSiteModules A) (hN : IsZero N) :
    IsZero (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := CochainComplex.onePointRingSheaf A),
    hN.eq_zero_of_tgt (𝟙 N)]
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver _ X.unop).map (𝟙 M.val) ≫ φ ≫
    (PresheafOfModules.restrictOver _ X.unop).map 0 = 0
  ext W x
  rfl

/-- Keep the specified product property behind a theorem, avoiding reduction of the
whole Hom-complex construction when using its limiting fan. -/
private theorem ringHomComplex_isLimit {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk
      ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n)
      (ringHomComplexProjection P Q n))) :=
  (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose_spec.1
    P Q n

set_option backward.isDefEq.respectTransparency true in
private noncomputable def dualTermIso {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    (perfectRingDual P).X n ≅
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X (-n))
        (SheafOfModules.unit ((sheafCompose ⊥
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) := by
  classical
  let O := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let L := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj O
  let M (p : ℤ) := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
    (P.X p) (L.X (p + n))
  let T := (homComplex (R := CochainComplex.onePointRingSheaf A) P L).X n
  let π : ∀ p, T ⟶ M p := ringHomComplexProjection P L n
  let hπ : IsLimit (Fan.mk T π) :=
    (ringHomComplex_isLimit P L n).some
  let ι : M (-n) ⟶ T :=
    Fan.IsLimit.lift hπ (fun p => if h : p = -n then eqToHom (congrArg M h.symm) else 0)
  have hι (p : ℤ) : ι ≫ π p =
      if h : p = -n then eqToHom (congrArg M h.symm) else 0 :=
    Fan.IsLimit.fac hπ _ p
  let e : T ≅ M (-n) :=
    { hom := π (-n)
      inv := ι
      hom_inv_id := by
        apply Fan.IsLimit.hom_ext hπ
        intro p
        change (π (-n) ≫ ι) ≫ π p = 𝟙 _ ≫ π p
        rw [Category.assoc, hι]
        by_cases h : p = -n
        · subst p
          simp only [dif_pos rfl, eqToHom_refl, Category.comp_id, Category.id_comp]
        · have hz : IsZero (M p) := homObj_zero_target _ _
            (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 O (p + n) (by omega))
          exact hz.eq_of_tgt _ _
      inv_hom_id := by
        rw [hι]
        simp only [dif_pos rfl, eqToHom_refl] }
  let eO : L.X (-n + n) ≅ O :=
    HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 O (-n + n) (by omega)
  exact e ≪≫ ((SheafOfModules.homFunctor (CochainComplex.onePointRingSheaf A)).obj
    (op (P.X (-n)))).mapIso eO

private theorem flat_of_iso {A : Type u} [CommRing A]
    {M N : RingSiteModules A} (e : M ≅ N) (hN : SheafOfModules.IsFlat N) :
    SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  change exactFunctor _ _ (MonoidalCategory.tensorRight N) at hN
  change exactFunctor _ _ (MonoidalCategory.tensorRight M)
  exact ObjectProperty.prop_of_iso _
    ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hN

set_option backward.isDefEq.respectTransparency false in
private theorem ringFlat_of_point_flat {A : Type u} [CommRing A]
    (M : RingSiteModules A) (hM : Module.Flat A (M.val.obj point)) :
    SheafOfModules.IsFlat M := by
  let R := CochainComplex.onePointRingSheaf A
  let O := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  have hflat (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
      Module.Flat (R.obj.obj V) (M.val.obj V) := by
    obtain rfl : V = point := Subsingleton.elim _ _
    exact hM
  have hP : PreservesFiniteLimits (MonoidalCategory.tensorRight M.val) := by
    constructor
    intro K _ _
    have (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
        Module.Flat (R.obj.obj V) (M.val.obj V) := hflat V
    exact ⟨⟨fun hc => ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V => isLimitOfPreserves
        (MonoidalCategory.tensorRight (show ModuleCat (R.obj.obj V) from M.val.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective ⊥ (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective ⊥ _ (fun _ => Function.injective_id)
  have : Presheaf.IsLocallySurjective ⊥ (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective ⊥ _ (fun _ => Function.surjective_id)
  have hs := (PresheafOfModules.isFlat_sheafification_obj
    (R := R) (𝟙 O.obj) M.val hP).2
  let e := asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit.app M)
  exact flat_of_iso e.symm hs

/-- Every term of the dual of a complex of finite-projective ring modules is flat.
Source: Stacks Project, More on Algebra, Tag 0A6A, clause (1), finite-projective
representative argument; Mathlib `Module.dual_projective` and `Module.Flat.of_projective`.
(blueprint: lem-pc-perfect-ring-dual-term-flat)

Proof: in degree n the product defining Hom(P,A[0]) has only one possibly nonzero
factor, Hom(P^(-n),A). All other factors vanish because A[0] vanishes there.
Its projection to this factor is an isomorphism by the product universal property.
Evaluation at the unique object of the discrete one-object bottom-topology site
is an exact equivalence with A-modules and identifies sheaf tensor with module tensor.
A finite projective module is a summand of a finite free module. Applying Hom(-,A)
to its splitting exhibits its dual as a summand of the dual finite free module,
which is finite free by coordinate evaluation. Hence this dual is projective,
therefore flat. Under the evaluation equivalence tensoring with this sheaf
preserves finite limits and finite colimits, which is the predicate IsFlat.
This includes the zero ring, zero modules and rank-zero summands. No boundedness
or assertion about a second complex is used. -/
theorem perfectRingDual_term_isFlat {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ)
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    ∀ n : ℤ, SheafOfModules.IsFlat ((perfectRingDual P).X n) := by
  intro n
  let O := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let M : ModuleCat A := (P.X (-n)).val.obj point
  let N : ModuleCat A := (SheafOfModules.homObj
    (R := CochainComplex.onePointRingSheaf A) (P.X (-n)) O).val.obj point
  have : Module.Projective A M := hp (-n)
  have : Module.Finite A M := hf (-n)
  have : Module.Flat A (Module.Dual A M) := inferInstance
  let e : N ≃ₗ[A] Module.Dual A M := homPointEquiv (P.X (-n)) O
  have hN : Module.Flat A N := Module.Flat.of_linearEquiv e
  exact flat_of_iso (dualTermIso P n) (ringFlat_of_point_flat _ hN)

end CategoryTheory
