/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import Sheaf.CategoryTheory.ScalarLocalizationModuleColimit

/-!
# Sequential complex colimits for scalar localization

Source: Stacks Project, algebra.tex, Tag 00CM (section-localization), and
sites-modules.tex, Tags 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-complex-colimit)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

set_option linter.style.whitespace false in
set_option maxHeartbeats 800000 in
-- Elaborating the sectionwise tensor normalization requires additional heartbeats.
/-- The ordinary sequential colimit of a scalar sequence of complexes.
Source: Stacks Project, algebra.tex, Tag 00CM; sites-modules.tex, Tags 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-complex-colimit).

Proof: on each object V and degree i, send the stage-n element x to t^(-n) tensor x.
For any compatible family, send a fraction x/t^n to the stage-n image of x.
If two fractions agree, a power of t kills their cross difference; passing to the
common stage n+m+k makes their images equal. This proves well-definedness even
with t-torsion. Common stages prove additivity and linearity; all fractions prove
uniqueness. These maps commute with restriction. Module sheafification gives the
universal property for sheaf modules, and tensor--Hom adjunction extends it from
R to every module. Apply it degreewise. The maps commute with differentials by
linearity, as do their inverses. Thus the termwise restricted scalar extension is
isomorphic to the sequential colimit complex. The displayed normalization is the
fraction formula, using the section normalization of the zeroth leg. -/
theorem scalarLocalization_complexColimit
    (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))]
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))
    (hE : ∀ M, E.obj M =
      SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t)) M)
    (_hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom (ringedLocalizationRingUnit R (a t)) M f ≫
        eqToHom (hE N).symm)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U₀ : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hU₀ : U₀ = SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R (a t))))
    [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (unitComplex : ∀ (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      K ⟶ (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (unitSections : ∀ (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (i : ℤ),
      scalarLocalizationTelescopeUnitSections (ringedLocalizationRingUnit R (a t))
        (K.X i) (E.obj (K.X i)) (hE (K.X i))
        ((unitComplex K).f i ≫
          eqToHom (congrArg (fun T ↦ T.obj (E.obj (K.X i))) hU₀)))
 :
    (fun [_source : Linear A (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
      [_target : Linear (Localization.Away t) (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t))))] ↦
      ∀ (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      ∃ (c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K))),
        Nonempty (IsColimit c) ∧
        ∃ β : c.pt ≅ (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
          ∀ n : ℕ, (show K ⟶ c.pt from c.ι.app n) ≫ β.hom = (unitComplex K) ≫
            (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
                𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
      (_source := scalarLocalizationCoefficientLinear A R a)
      (_target := scalarLocalizationCoefficientLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t))   := by
  let B := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let B' := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
    (ringedLocalizationRing R (a t)))
  let : Linear A B := scalarLocalizationCoefficientLinear A R a
  let : Linear (Localization.Away t) B' :=
    scalarLocalizationCoefficientLinear (Localization.Away t)
      (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)
  dsimp only
  intro K
  let T := (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let l (n : ℕ) : K ⟶ T := unitComplex K ≫
    (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
        𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  have hdegree (i : ℤ) := scalarLocalization_moduleColimit A R a t
    (K.X i) (E.obj (K.X i)) (hE (K.X i)) U₀ hU₀
    ((unitComplex K).f i) (unitSections K i)
  have hstep (n : ℕ) : (t • 𝟙 K) ≫ l (n + 1) = l n := by
    apply HomologicalComplex.hom_ext
    intro i
    obtain ⟨c, ⟨hc⟩, β, hβ⟩ := hdegree i
    change (t • 𝟙 (K.X i)) ≫ (l (n + 1)).f i = (l n).f i
    change (t • 𝟙 (K.X i)) ≫ ((unitComplex K).f i ≫ U₀.map
      (((IsLocalization.Away.invSelf t : Localization.Away t) ^ (n + 1)) •
        𝟙 (E.obj (K.X i)))) = _
    rw [← hβ (n + 1)]
    change (t • 𝟙 (K.X i)) ≫ (c.ι.app (n + 1) ≫ β.hom) =
      (unitComplex K).f i ≫ U₀.map
        (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
          𝟙 (E.obj (K.X i)))
    rw [← hβ n, ← Category.assoc]
    congr 1
    simpa only [Functor.ofSequence_map_homOfLE_succ] using
      c.w (homOfLE (Nat.le_succ n))
  let c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)) :=
    { pt := T
      ι := NatTrans.ofSequence l (by
        intro n
        rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        change (t • 𝟙 K) ≫ l (n + 1) = l n ≫ 𝟙 T
        rw [Category.comp_id]
        exact hstep n) }
  refine ⟨c, ?_, Iso.refl T, ?_⟩
  · suffices h : ∀ i : ℤ, Nonempty (IsColimit
        ((HomologicalComplex.eval B (.up ℤ) i).mapCocone c)) by
      exact ⟨HomologicalComplex.isColimitOfEval _ _ (fun i ↦ Classical.choice (h i))⟩
    intro i
    obtain ⟨d, ⟨hd⟩, β, hβ⟩ := hdegree i
    let V := HomologicalComplex.eval B (.up ℤ) i
    let S := Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)
    let D := Functor.ofSequence (X := fun _n : ℕ ↦ K.X i)
      (fun _n ↦ t • 𝟙 (K.X i))
    let τ : D ⟶ S ⋙ V := NatTrans.ofSequence (fun _n ↦ 𝟙 (K.X i)) (by
      intro n
      simp only [D, S, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      change (t • 𝟙 (K.X i)) ≫ 𝟙 _ = 𝟙 _ ≫ (t • 𝟙 (K.X i))
      simp only [Category.comp_id, Category.id_comp])
    let e : D ≅ S ⋙ V := NatIso.ofComponents (fun _n ↦ Iso.refl _) (by
      intro n m f
      exact τ.naturality f)
    apply Nonempty.intro
    apply (IsColimit.precomposeHomEquiv e (V.mapCocone c)).toFun
    apply IsColimit.ofIsoColimit hd
    refine Cocone.ext β ?_
    intro n
    change d.ι.app n ≫ β.hom = (𝟙 (K.X i)) ≫ (l n).f i
    rw [Category.id_comp]
    exact hβ n
  · intro n
    exact Category.comp_id _

end CategoryTheory
