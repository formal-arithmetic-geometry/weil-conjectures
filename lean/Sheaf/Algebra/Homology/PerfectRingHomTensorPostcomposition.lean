/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1, SHEAF group T4
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # The postcomposition term of signed tensor-dual evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1),
expanded differential calculation of signed tensor-dual evaluation.
(blueprint: lem-pc-perfect-ring-hom-tensor-postcomposition)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_sections_ext {A : Type u} [CommRing A]
    (M N Z : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (f g : M ⊗ N ⟶ Z),
      (∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
        f.val.app U ((perfectRingTensorSectionMap M N).app U (x ⊗ₜ[A] y)) =
          g.val.app U ((perfectRingTensorSectionMap M N).app U (x ⊗ₜ[A] y))) → f = g := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro f g h
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv
    (M.val ⊗ N.val) Z).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_section_natural {A : Type u} [CommRing A]
    (M N N' : RingSiteModules A) (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    perfectRingTensorSectionMap M N ≫ (M ◁ g).val =
      (M.val ◁ g.val) ≫ perfectRingTensorSectionMap M N' := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let S := PresheafOfModules.sheafification (𝟙
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)).obj)
  have hi : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ M ◁ g =
      S.map (M.val ◁ g.val) ≫ (SheafOfModules.tensorObjIsoSheafification M N').inv := by
    have hc := SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom
      (R := CochainComplex.onePointRingSheaf A) M g
    change M ◁ g ≫ (SheafOfModules.tensorObjIsoSheafification M N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        S.map (M.val ◁ g.val) at hc
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hv := congrArg SheafOfModules.Hom.val hi
  change (SheafOfModules.tensorObjIsoSheafification M N).inv.val ≫ (M ◁ g).val =
    (S.map (M.val ◁ g.val)).val ≫
      (SheafOfModules.tensorObjIsoSheafification M N').inv.val at hv
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)).obj)).unit.naturality (M.val ◁ g.val)
  change (M.val ◁ g.val) ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N'.val) =
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
      (S.map (M.val ◁ g.val)).val at hn
  unfold perfectRingTensorSectionMap
  erw [Category.assoc, hv, ← Category.assoc, ← hn]
  rfl

private theorem smul_app_apply {A : Type u} [CommRing A]
    {M N : RingSiteModules A} (c : ℤˣ) (f : M ⟶ N)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (x : M.val.obj U) :
    (c • f).val.app U x = c • f.val.app U x := by
  change ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).map (c • f)) x = _
  rw [Functor.map_units_smul]
  rfl

private theorem hom_smul_app_apply
    {R : Sheaf ⊥ CommRingCat.{u}}
    {M N : SheafOfModules ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (c : ℤˣ) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (SheafOfModules.homObj (R := R) M N).val.obj U)
    (x : ((PresheafOfModules.restrictOver R.obj U.unop).obj M.val).obj
      (op (Over.mk (𝟙 U.unop)))) :
    ((c • f).app (op (Over.mk (𝟙 U.unop)))) x =
      c • (f.app (op (Over.mk (𝟙 U.unop)))) x := by
  change ((PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U.unop)))).map (c • f)) x = _
  rw [Functor.map_units_smul]
  rfl

private theorem transport_d_apply {A : Type u} [CommRing A]
    (Q : CochainComplex (RingSiteModules A) ℤ) (s t v w : ℤ)
    (hs : s = v) (ht : t = w) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (y : (Q.X s).val.obj U) :
    (eqToHom (congrArg Q.X ht)).val.app U ((Q.d s t).val.app U y) =
      (Q.d v w).val.app U ((eqToHom (congrArg Q.X hs)).val.app U y) := by
  subst v w
  rfl

private theorem sign_post (r s : ℤ) :
    r.negOnePow * (r * (s + 1)).negOnePow = (r * s).negOnePow := by
  calc
    _ = (r * s).negOnePow * (r.negOnePow * r.negOnePow) := by
      rw [mul_add, mul_one, Int.negOnePow_add]
      ac_rfl
    _ = _ := by rw [Int.units_mul_self, mul_one]

private theorem map_units_smul_apply {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (c : ℤˣ) (x : M) :
    f (c • x) = c • f x := by
  change f.hom ((c : ℤ) • x) = (c : ℤ) • f.hom x
  exact map_zsmul f.hom _ _

set_option backward.isDefEq.respectTransparency false in
private theorem signed_transport_d {A : Type u} [CommRing A]
    (Q : CochainComplex (RingSiteModules A) ℤ) (r s n : ℤ) (h : r + s = n)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (lam : A) (y : (Q.X s).val.obj U) :
    r.negOnePow •
      (eqToHom (congrArg Q.X (show s + 1 = -r + (n + 1) by omega))).val.app U
        ((r * (s + 1)).negOnePow • (lam • (Q.d s (s + 1)).val.app U y)) =
    (Q.d (-r + n) (-r + (n + 1))).val.app U
      ((eqToHom (congrArg Q.X (show s = -r + n by omega))).val.app U
        ((r * s).negOnePow • (lam • y))) := by
  rw [map_units_smul_apply, smul_smul, sign_post, map_units_smul_apply,
    map_units_smul_apply]
  apply congrArg (fun z => (r * s).negOnePow • z)
  rw [← ((Q.d s (s + 1)).val.app U).hom.map_smul]
  exact transport_d_apply Q s (s + 1) (-r + n) (-r + (n + 1))
    (by omega) (by omega) U (lam • y)

set_option backward.isDefEq.respectTransparency true in
/-- The postcomposition term on a single tensor summand and Hom coordinate.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1),
expanded differential calculation.
(blueprint: lem-pc-perfect-ring-hom-tensor-postcomposition)

Proof: expand the second tensor summand differential as (-1)^r times
id tensor d_Q followed by the (r,s+1) inclusion. If p differs from -r,
both sides vanish by the off-diagonal clause of the two degree conditions.
If p=-r, test on lambda tensor y and x. Naturality of the tensor
sheafification comparison gives (-1)^r lambda tensor d_Q(y). The degree
n+1 condition evaluates this as (-1)^r (-1)^(r*(s+1)) lambda(x) d_Q(y).
The degree n condition followed by postcomposition gives
(-1)^(r*s) d_Q(lambda(x) y). Linearity of d_Q and the identity
(-1)^r (-1)^(r*(s+1)) = (-1)^(r*s) give equality. The equation
s=-r+n identifies the target degrees; naturality of eqToHom identifies
the transported differentials. Extend from pure tensors by the tensor
universal property, then use the sheafification adjunction and equality
on the unique slice object to recover the sheaf morphisms. No finite
support, projectivity, or bounds are used. The same equations hold over
the zero ring, for zero modules, and for negative degrees. -/
theorem perfectRingHom_tensorDual_postcomposition {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (a : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n)
      (b : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X (n + 1) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X (n + 1)),
      PerfectRingHomTensorDegreeCondition P Q n a →
      PerfectRingHomTensorDegreeCondition P Q (n + 1) b →
      ∀ (r s p : ℤ) (h : r + s = n),
      HomologicalComplex.mapBifunctor.d₂ (perfectRingDual P) Q (curriedTensor _)
          (ComplexShape.up ℤ) r s (n + 1) ≫ b ≫ ringHomComplexProjection P Q (n + 1) p =
        CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
          r s n h ≫ a ≫ ringHomComplexProjection P Q n p ≫
            SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
              (𝟙 (P.X p)) (Q.d (p + n) (p + (n + 1))) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro a b ha hb r s p h
  have hs : r + (s + 1) = n + 1 := by omega
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ r
    (show (ComplexShape.up ℤ).Rel s (s + 1) from rfl) (n + 1) hs]
  by_cases hp : p = -r
  · subst p
    simp only [Linear.units_smul_comp, Category.assoc]
    apply tensor_sections_ext
    intro U lam y
    apply PresheafOfModules.hom_ext
    intro W
    obtain ⟨W⟩ := W
    obtain ⟨V, f, rfl⟩ := CostructuredArrow.mk_surjective W
    obtain rfl := IsDiscrete.eq_of_hom f
    obtain rfl : f = 𝟙 U.unop := Subsingleton.elim _ _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (((r.negOnePow •
      (((perfectRingDual P).X r ◁ Q.d s (s + 1)) ≫
        CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
          r (s + 1) (n + 1) hs ≫ b ≫ ringHomComplexProjection P Q (n + 1) (-r))).val.app U
      ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
        (lam ⊗ₜ[(CochainComplex.onePointRingSheaf A).obj.obj U] y))).app
          (op (Over.mk (𝟙 U.unop)))) x = _
    rw [smul_app_apply]
    rw [hom_smul_app_apply (R := CochainComplex.onePointRingSheaf A)
      (M := P.X (-r)) (N := Q.X (-r + (n + 1))) r.negOnePow U]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    have hbn := hb.2 r (s + 1) hs U lam
      ((Q.d s (s + 1)).val.app U y) x
    have han := ha.2 r s h U lam y x
    have hn := tensor_section_natural ((perfectRingDual P).X r) (Q.X s) (Q.X (s + 1))
      (Q.d s (s + 1))
    have hnv := congrArg (fun f => f.app U
      (lam ⊗ₜ[(CochainComplex.onePointRingSheaf A).obj.obj U] y)) hn
    change ((perfectRingDual P).X r ◁ Q.d s (s + 1)).val.app U
      ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
        (lam ⊗ₜ[(CochainComplex.onePointRingSheaf A).obj.obj U] y)) =
      (perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X (s + 1))).app U
        (lam ⊗ₜ[(CochainComplex.onePointRingSheaf A).obj.obj U]
          (Q.d s (s + 1)).val.app U y) at hnv
    rw [hnv]
    refine (congrArg (fun z : (Q.X (-r + (n + 1))).val.obj U => r.negOnePow • z)
      hbn).trans ?_
    change r.negOnePow • (_ : (Q.X (-r + (n + 1))).val.obj U) =
      (Q.d (-r + n) (-r + (n + 1))).val.app U
      (((ringHomComplexProjection P Q n (-r)).val.app U
        (a.val.app U ((CochainComplex.ιMapBifunctor (perfectRingDual P) Q
          (curriedTensor _) r s n h).val.app U
            ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
              (lam ⊗ₜ[(CochainComplex.onePointRingSheaf A).obj.obj U] y))))).app
                (op (Over.mk (𝟙 U.unop))) x)
    have han' := congrArg
      (fun z => (Q.d (-r + n) (-r + (n + 1))).val.app U z) han
    refine Eq.trans ?_ han'.symm
    exact signed_transport_d Q r s n h U (perfectRingDualEvaluate P r U lam x) y
  · have ha0 := ha.1 r s h p hp
    have hb0 := hb.1 r (s + 1) hs p hp
    simp only [Linear.units_smul_comp, Category.assoc]
    simp only [hb0, comp_zero, smul_zero]
    simpa only [Category.assoc, zero_comp] using
      (congrArg (fun f => f ≫ SheafOfModules.homObjMap
        (R := CochainComplex.onePointRingSheaf A) (𝟙 (P.X p))
          (Q.d (p + n) (p + (n + 1)))) ha0).symm

end CategoryTheory
