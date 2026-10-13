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

set_option maxHeartbeats 600000 in
-- Evaluating a product cone requires extra elaboration heartbeats.
private theorem boundaryComparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U))
    (H : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (H.X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X q)))
    (hfan : ∀ n, Nonempty (Limits.IsLimit
      (Limits.Fan.mk (H.X n) (fun p : ℤ ↦ π n p (p + n) rfl))))
    (hdiff : ∀ p : ℤ,
      H.d (-1) 0 ≫ π 0 p p (add_zero p) =
        π (-1) p (p - 1) (by omega) ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (I.d (p - 1) p) -
        (-1 : ℤ).negOnePow • (π (-1) (p + 1) p (by omega) ≫
          SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (I.X p)))) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
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
          (((π 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      (Nonempty (Homotopy f 0) ↔ ∃ x : S.X (-1), S.toCycles (-1) 0 x = z) :=
    open Limits CochainComplex.HomComplex in by
  classical
  intro R₀ S _ res z f hf
  let E := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat (R₀.obj.obj (op U))) AddCommGrpCat
  let c : ∀ n, S.X n → Cochain (res.obj L) (res.obj I) n := fun n x ↦
    Cochain.mk fun p q hpq ↦
      ⟨((π n p q hpq).val.app (op U)) x⟩
  have hc : ∀ n, Function.Bijective (c n) := by
    intro n
    let T := E ⋙ forget AddCommGrpCat
    let fan := Fan.mk (H.X n) (fun p : ℤ ↦ π n p (p + n) rfl)
    have hlimit : IsLimit fan := (hfan n).some
    have ht : IsLimit (Fan.mk (S.X n : Type (max u v))
        (fun p : ℤ ↦ TypeCat.ofHom ((π n p (p + n) rfl).val.app (op U)).hom)) :=
      (Fan.isLimitMapConeEquiv T _ fan) (isLimitOfPreserves T hlimit)
    constructor
    · intro x y h
      have hxy : (TypeCat.ofHom fun _ : PUnit ↦ x) =
          (TypeCat.ofHom fun _ : PUnit ↦ y) := by
        apply ht.hom_ext
        intro j
        obtain ⟨p⟩ := j
        ext t
        exact congrArg SheafOfModules.Hom.val
          (Cochain.congr_v h p (p + n) rfl)
      exact ConcreteCategory.congr_hom hxy PUnit.unit
    · intro y
      let a := Fan.mk PUnit (fun p : ℤ ↦
        TypeCat.ofHom fun _ : PUnit ↦ (y.v p (p + n) rfl).val)
      refine ⟨ht.lift a PUnit.unit, ?_⟩
      apply Cochain.ext
      intro p q hpq
      subst q
      apply SheafOfModules.hom_ext
      exact ConcreteCategory.congr_hom (ht.fac a ⟨p⟩) PUnit.unit
  have hd : ∀ x : S.X (-1), c 0 (S.d (-1) 0 x) = δ (-1) 0 (c (-1) x) := by
    intro x
    apply Cochain.ext₀
    intro p
    apply SheafOfModules.hom_ext
    have h := hdiff p
    have hsign : (-1 : ℤ).negOnePow = -1 := by
      rw [Int.negOnePow_neg, Int.negOnePow_one]
    rw [hsign, Units.neg_smul, one_smul, sub_neg_eq_add] at h
    have hx := congrArg (fun g ↦ (g.val.app (op U)).hom x) h
    change ((π 0 p p (add_zero p)).val.app (op U)).hom
      (((H.d (-1) 0).val.app (op U)).hom x) =
      ((PresheafOfModules.restrictOver R.obj U).map (𝟙 (L.X p).val) ≫
        ((π (-1) p (p - 1) (by omega)).val.app (op U)).hom x ≫
        (PresheafOfModules.restrictOver R.obj U).map (I.d (p - 1) p).val) +
      ((PresheafOfModules.restrictOver R.obj U).map (L.d p (p + 1)).val ≫
        ((π (-1) (p + 1) p (by omega)).val.app (op U)).hom x ≫
        (PresheafOfModules.restrictOver R.obj U).map (show I.X p ⟶ I.X p from 𝟙 _).val) at hx
    simp only [SheafOfModules.id_val, Functor.map_id, Category.id_comp,
      Category.comp_id] at hx
    rw [δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
    simp only [Int.negOnePow_zero, one_smul]
    exact hx
  have hz : c 0 (S.iCycles 0 z) = Cochain.ofHom f := by
    apply Cochain.ext₀
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (hf p W).symm
  have hi (x : S.X (-1)) : S.iCycles 0 (S.toCycles (-1) 0 x) = S.d (-1) 0 x :=
    ConcreteCategory.congr_hom (S.toCycles_i (-1) 0) x
  constructor
  · rintro ⟨h⟩
    obtain ⟨x, hx⟩ := (hc (-1)).2 (Cochain.ofHomotopy h)
    refine ⟨x, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (S.iCycles 0)).1 inferInstance
    rw [hi]
    apply (hc 0).1
    rw [hd, hx, δ_ofHomotopy, Cochain.ofHom_zero, sub_zero, hz]
  · rintro ⟨x, hx⟩
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨c (-1) x, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero, ← hd, ← hi, hx, hz]

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
  intro R₀ H π S _ res z f hf
  have hs := Classical.choose_spec (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  exact boundaryComparison J R U L I hzero H (π L I) (hs.1 L I)
    (fun p ↦ hs.2.1 L I (-1) 0 p p (p - 1) (p + 1)
      (by omega) (add_zero p) (by omega) (by omega)) z f hf

end CategoryTheory
