/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Localized Hom boundaries and null-homotopies

Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

private lemma fan_bijective {X : Type u} {Y : ℤ → Type u} (g : ∀ i, X → Y i)
    (h : Limits.IsLimit (Limits.Fan.mk X (fun i ↦ (↾g i)))) :
    Function.Bijective (fun x i ↦ g i x) := by
  constructor
  · intro x y hxy
    have h' : (↾fun _ : PUnit.{u + 1} ↦ x) = (↾fun _ ↦ y) := by
      apply h.hom_ext
      intro j
      apply ConcreteCategory.hom_ext
      intro t
      exact congrFun hxy j.as
    exact ConcreteCategory.congr_hom h' PUnit.unit
  · intro y
    let fan := Limits.Fan.mk (PUnit.{u + 1}) (fun i ↦ (↾fun _ ↦ y i))
    refine ⟨h.lift fan PUnit.unit, ?_⟩
    funext i
    exact ConcreteCategory.congr_hom (h.fac fan ⟨i⟩) PUnit.unit

private def cochainUnderlyingEquiv {D : Type u} [Category.{v} D]
    {K : GrothendieckTopology D} {A : Sheaf K RingCat.{max u v}}
    (L I : CochainComplex (SheafOfModules.{max u v} A) ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain L I n ≃
      (∀ p : ℤ, (L.X p).val ⟶ (I.X (p + n)).val) where
  toFun c p := (c.v p (p + n) rfl).val
  invFun g := CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦ by
    subst q
    exact ⟨g p⟩
  left_inv c := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    subst q
    rfl
  right_inv g := rfl

set_option maxHeartbeats 400000 in
-- Comparing the sectionwise product with localized cochains needs extra elaboration steps.
/-- A localized chain map represented by a cycle is null-homotopic exactly when
that cycle is a boundary in the section complex.
Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)

Proof: the product fan specified by homComplex_exists remains limiting after
forgetting module sheaves, evaluating at U, and forgetting modules to abelian
groups. In degree -1 it identifies a section x with the family of localized
maps h_p : L^p|_U → I^(p-1)|_U supplied by the projections. Lift the underlying
presheaf-module maps to sheaf-module maps using the fully faithful forgetful
functor. The differential projection formula in degree -1 says that the p-th
component of d(x) is h_p followed by d_I plus d_L followed by h_(p+1), since
(-1)^(-1)=-1. The identity toCycles followed by iCycles equals d therefore
shows, using the assumed component formula for f, that these h_p form a
null-homotopy of f when z=toCycles(x). This proves the boundary-to-homotopy direction.
Conversely, take the adjacent-degree components h_p of a null-homotopy of f.
Their underlying presheaf maps assemble uniquely into a degree -1 section x
by the evaluated product fan. The same differential identity and the homotopy
commutation equation give d(x)=iCycles(z), component by component. The product
projections are jointly injective on sections. Since iCycles is monic, the
identity iCycles(toCycles(x))=d(x) implies toCycles(x)=z.
There is no boundedness or finite support assumption. For zero complexes the
section and map groups are zero. If both differentials vanish, the homotopy
equation forces f=0 and both sides require z=0. -/
theorem localizedHomComplex_nullHomotopy_iff_boundary
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    let := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ (z : S.cycles 0) (f : res.obj L ⟶ res.obj I),
      (∀ (p : ℤ) (W : (Over U)ᵒᵖ),
        (f.f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      (Nonempty (Homotopy f 0) ↔ ∃ x : S.X (-1), S.toCycles (-1) 0 x = z) := by
  classical
  intro R₀ H π S hi res z f hf
  let e (n : ℤ) (x : S.X n) :
      CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n :=
    CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
      ⟨((π L I n p q hpq).val.app (op U)) x⟩
  have he : e 0 (S.iCycles 0 z) = CochainComplex.HomComplex.Cochain.ofHom f := by
    apply CochainComplex.HomComplex.Cochain.ext₀
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    simpa [e] using (hf p W).symm
  let F := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat ⋙ forget AddCommGrpCat
  have hπ := Classical.choose_spec (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  have hprod (n : ℤ) : Nonempty (Limits.IsLimit
      (Limits.Fan.mk (H.X n) (fun p : ℤ ↦ π L I n p (p + n) rfl))) := hπ.1 L I n
  have hfan (n : ℤ) : Limits.IsLimit (Limits.Fan.mk (F.obj (H.X n))
      (fun p : ℤ ↦ F.map (π L I n p (p + n) rfl))) :=
    (Limits.Fan.isLimitMapConeEquiv F _ _).toFun
      (Limits.isLimitOfPreserves F (hprod n).some)
  have hbij (n : ℤ) : Function.Bijective (e n) := by
    let eqv := cochainUnderlyingEquiv (res.obj L) (res.obj I) n
    have hb := fan_bijective.{max u v}
      (fun p : ℤ ↦ fun x ↦ F.map (π L I n p (p + n) rfl) x) (hfan n)
    exact (eqv.comp_bijective (e n)).1 hb
  have hd (x : S.X (-1)) : e 0 (S.d (-1) 0 x) =
      CochainComplex.HomComplex.δ (-1) 0 (e (-1) x) := by
    apply CochainComplex.HomComplex.Cochain.ext₀
    intro p
    apply SheafOfModules.hom_ext
    have hdiff := hπ.2.1 L I (-1) 0 p p (p - 1) (p + 1)
      (by omega) (add_zero p) (by omega) (by omega)
    have hval := congrArg (fun g ↦ g.val.app (op U)) hdiff
    have hx := ConcreteCategory.congr_hom hval x
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul,
      one_smul, sub_neg_eq_add] at hx
    rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) _ p p (add_zero p)
      (p - 1) (p + 1) (by omega) (by omega)]
    simp only [Int.negOnePow_zero, one_smul]
    change ((π L I 0 p p (add_zero p)).val.app (op U)) (S.d (-1) 0 x) = _
    change ((π L I 0 p p (add_zero p)).val.app (op U)) (S.d (-1) 0 x) =
      ((π L I (-1) p (p - 1) (by omega)).val.app (op U)) x ≫
        (PresheafOfModules.restrictOver R.obj U).map (I.d (p - 1) p).val +
      (PresheafOfModules.restrictOver R.obj U).map (L.d p (p + 1)).val ≫
        ((π L I (-1) (p + 1) p (by omega)).val.app (op U)) x
    change ((π L I 0 p p (add_zero p)).val.app (op U)).hom
      (H.d (-1) 0 |>.val.app (op U) |>.hom <| x) = _ at hx
    simp only [SheafOfModules.comp_val, SheafOfModules.add_val,
      PresheafOfModules.comp_app, PresheafOfModules.add_app,
      ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
      LinearMap.comp_apply, SheafOfModules.homObjMap_val,
      SheafOfModules.id_val] at hx
    exact hx
  have htc (x : S.X (-1)) : S.iCycles 0 (S.toCycles (-1) 0 x) = S.d (-1) 0 x :=
    ConcreteCategory.congr_hom (S.toCycles_i (-1) 0) x
  constructor
  · rintro ⟨h⟩
    obtain ⟨x, hx⟩ := (hbij (-1)).2 (CochainComplex.HomComplex.Cochain.ofHomotopy h)
    refine ⟨x, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (S.iCycles 0)).1 inferInstance
    apply (hbij 0).1
    rw [htc, hd, hx, CochainComplex.HomComplex.δ_ofHomotopy, he]
    simp
  · rintro ⟨x, hx⟩
    apply Nonempty.map (CochainComplex.HomComplex.Cochain.equivHomotopy f 0).symm
    refine ⟨⟨e (-1) x, ?_⟩⟩
    rw [← hd, ← htc, hx, he]
    simp

end CategoryTheory
