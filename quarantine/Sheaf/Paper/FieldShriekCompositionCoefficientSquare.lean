/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.FieldShriekCompositionNormalization
public import Sheaf.Paper.CompactSupportCoefficientAction
import Sheaf.Paper.IntegralCompositionCoefficientSquare

/-! # Coefficient compatibility of normalized compact-support compositors

The scalar square in step 7 of the field shriek composition argument, before descent.
Source: Stacks 0F7J and Bhatt--Scholze, Definition 6.7.6.
(blueprint: lem-zl-field-shriek-composition-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
open PurCompactSupport GeneralAlgebraicallyClosedCoefficients

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem comp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl

private theorem app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem relabel_heq {C D : Type*} [Category C] [Category D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G') (a : F' ≅ G') (K : C) :
    HEq ((eqToIso hF ≪≫ a ≪≫ (eqToIso hG).symm).hom.app K) (a.hom.app K) := by
  subst F'
  subst G'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.trans_refl, Iso.refl_trans]
  rfl

private theorem scalar_obj (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (K : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K.obj⟩ :=
  (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K

private theorem scalar_map (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    {K K' : sfIntegralConstructibleCategory l E W} (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((sfRationalConstructibleLocalization l E W).map f))
      ((sfRationalConstructibleLocalization l L W).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map f)) := by
  simpa only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, map_one] using
    (sfRationalScalarExtension_existsUnique l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K K' f 1

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

private theorem finite_map
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {K K' : sfIntegralConstructibleCategory l E Y} (v : K ⟶ K') :
    (sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg E).map
        ((sfRationalConstructibleLocalization l E Y).map v) =
      (sfRationalConstructibleLocalization l E Z).map
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          cg E).map v) := by
  let F := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E
  let R := Padic.coefficientExtensionIntegers l E
  let S := Localization.Away (Padic.coefficientExtensionUniformizer l E)
  have := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cg E).1
  have := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cg E).2
  change (F.mapLinearMap R).baseChange S (1 ⊗ₜ[R] v) = 1 ⊗ₜ[R] F.map v
  exact LinearMap.baseChange_tmul _ _ _

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Sf : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cf)
  (Sg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cg)
  (Sfg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cfg)
  (B : ∀ E₀ : Padic.FiniteCoefficientFields l Ω,
    sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cf
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) ⋙
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) ≅
    sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cfg
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀))

/-- Relabel a finite compositor along the action's literal finite-functor equalities.
Source: the fixed finite actions in the common-stage construction
(blueprint: lem-zl-field-shriek-composition-coefficient-square). -/
def sfCompositionOnCoefficientStage (E₀ : Padic.FiniteCoefficientFields l Ω) :
    (Sf.system.comp Sg.system).Φ E₀ ≅ Sfg.system.Φ E₀ :=
  eqToIso (congrArg₂ (fun F G ↦ F ⋙ G) (Sf.finite_eq E₀) (Sg.finite_eq E₀)) ≪≫
    B E₀ ≪≫ (eqToIso (Sfg.finite_eq E₀)).symm

/-- The scalar square for a family normalized by the integral proper/open formula.
Only coefficient compatibility is asserted here: existence, naturality at each finite
stage, invertibility and the eventual descent are supplied separately.

Source: Stacks 0F7J, proper/open formula and independence of compactifications;
Bhatt--Scholze, Definition 6.7.6, with the operation-reduction scalar mates
(blueprint: lem-zl-field-shriek-composition-coefficient-square).

Proof: choose a common compatible compactification tower for cf, cg, cfg. Write each
integral component by its assumed normalization. The open adjunction determines the
proper/open map from inverse restriction exchange. Coefficient extension preserves
this unit/counit composite: its scalar comparisons are the tensor-unit mates fixed
by integralBeta_spec. The scalar associator identifies the two successive extensions.
Paste these squares with the proper and open composition squares and with the
projection-normalized qcqs realizations. The normalized refinement squares commute
with coefficient extension, so the common-refinement maps cancel. This gives the
integral scalar square for the supplied family A. Localize this equality on Hom
groups. The hypothesis hB identifies its three compositor components; rationalBeta
identifies the scalar comparisons. Relabel by finite_eq to obtain the displayed
square for the actual stage systems. The argument is an equality of actual maps
before reduction; it does not use faithfulness of the finite evaluation functors. -/
theorem sfCompositionOnCoefficientStage_comm
    (A : ∀ E₀ : Padic.FiniteCoefficientFields l Ω,
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀))
    (hA : ∀ E₀, SfIntegralCompositionSpec l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)
      D.k (coefficientPrimeUnit l D hl) cf cg cfg (A E₀))
    (hB : ∀ (E₀ : Padic.FiniteCoefficientFields l Ω) (K : Stage l Ω X E₀),
      HEq ((B E₀).hom.app K)
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) Z).map
            ((A E₀).hom.app K.obj)))
    {E₀ L₀ : Padic.FiniteCoefficientFields l Ω} (h : E₀ ≤ L₀)
    (K : Stage l Ω X E₀) :
    ((stageSystem l Ω Z).T h).map
        ((sfCompositionOnCoefficientStage D l hl cf cg cfg Ω Sf Sg Sfg B E₀).hom.app K) ≫
      (Sfg.system.β h).hom.app K =
    ((Sf.system.comp Sg.system).β h).hom.app K ≫
      (sfCompositionOnCoefficientStage D l hl cf cg cfg Ω Sf Sg Sfg B L₀).hom.app
        (((stageSystem l Ω X).T h).obj K) := by
  let E := AlgebraicallyClosedCoefficients.Coefficient l Ω E₀
  let L := AlgebraicallyClosedCoefficients.Coefficient l Ω L₀
  let ι := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E₀ L₀ h
  have ht (W : Scheme.{u}) : (stageSystem l Ω W).T h = transition l Ω W E₀ L₀ h :=
    (stageSystem_existsUnique l Ω W).exists.choose_spec.1 E₀ L₀ h
  have tobj (W : Scheme.{u}) (P : Stage l Ω W E₀) :
      ((stageSystem l Ω W).T h).obj P =
        ⟨(integralTransition l Ω W E₀ L₀ h).obj P.obj⟩ := by
    rw [ht]
    exact scalar_obj l E L ι W P
  have tmap (W : Scheme.{u}) {P Q : sfIntegralConstructibleCategory l E W}
      (v : P ⟶ Q) :
      HEq (((stageSystem l Ω W).T h).map
        ((sfRationalConstructibleLocalization l E W).map v))
        ((sfRationalConstructibleLocalization l L W).map
          ((integralTransition l Ω W E₀ L₀ h).map v)) := by
    rw [ht]
    exact scalar_map l E L ι W v
  have he (M : Padic.FiniteCoefficientFields l Ω) (P : Stage l Ω X M) :
      HEq ((sfCompositionOnCoefficientStage D l hl cf cg cfg Ω Sf Sg Sfg B M).hom.app P)
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient l Ω M) Z).map
            ((A M).hom.app P.obj)) :=
    (relabel_heq
      (congrArg₂ (fun F G ↦ F ⋙ G) (Sf.finite_eq M) (Sg.finite_eq M))
      (Sfg.finite_eq M) (B M) P).trans (hB M P)
  have hm := map_heq ((stageSystem l Ω Z).T h)
    (by simp only [Functor.comp_obj, StageSystem.Morphism.comp_Φ, Sf.finite_eq,
      Sg.finite_eq, sfCompactSupportFiniteFunctor, sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (by simp only [Sfg.finite_eq, sfCompactSupportFiniteFunctor,
      sfRationalConstructibleLocalization, ScalarLocalization.localization]) (he E₀ K)
  have hleft := comp_heq
    (by simp only [L, Functor.comp_obj, StageSystem.Morphism.comp_Φ, Sf.finite_eq,
      Sg.finite_eq, sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [L, Sfg.finite_eq, sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, Sfg.finite_eq, sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (hm.trans (tmap Z ((A E₀).hom.app K.obj))) (Sfg.rationalBeta h K)
  have hg : HEq ((Sg.system.β h).hom.app ((Sf.system.Φ E₀).obj K))
      ((sfRationalConstructibleLocalization l L Z).map
        ((Sg.integralBeta h).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
            cf E).obj K.obj))) :=
    (app_heq (Sg.system.β h).hom
      (by simp only [E, Sf.finite_eq, sfCompactSupportFiniteFunctor])).trans
      (Sg.rationalBeta h
        ⟨(sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          cf E).obj K.obj⟩)
  have hfm := map_heq (Sg.system.Φ L₀)
    (by simp only [Functor.comp_obj, Sf.finite_eq, sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, Sf.finite_eq, sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (Sf.rationalBeta h K)
  have hfm' : HEq ((Sg.system.Φ L₀).map ((Sf.system.β h).hom.app K))
      ((sfRationalConstructibleLocalization l L Z).map
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          cg L).map ((Sf.integralBeta h).hom.app K.obj))) := by
    refine hfm.trans ?_
    rw [Sg.finite_eq L₀]
    exact heq_of_eq (finite_map D l hl cg L ((Sf.integralBeta h).hom.app K.obj))
  have hcomp := comp_heq
    (by simp only [E, L, Functor.comp_obj, Sf.finite_eq, Sg.finite_eq,
      sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [E, L, Functor.comp_obj, Sf.finite_eq, Sg.finite_eq,
      sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [L, Functor.comp_obj, Sf.finite_eq, Sg.finite_eq,
      sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization]) hg hfm'
  have hal : HEq
      ((sfCompositionOnCoefficientStage D l hl cf cg cfg Ω Sf Sg Sfg B L₀).hom.app
        (((stageSystem l Ω X).T h).obj K))
      ((sfRationalConstructibleLocalization l L Z).map
        ((A L₀).hom.app ((integralTransition l Ω X E₀ L₀ h).obj K.obj))) :=
    (app_heq
      (sfCompositionOnCoefficientStage D l hl cf cg cfg Ω Sf Sg Sfg B L₀).hom
      (tobj X K)).trans
      (he L₀ ⟨(integralTransition l Ω X E₀ L₀ h).obj K.obj⟩)
  rw [StageSystem.Morphism.comp_β_hom_app]
  have hright := comp_heq
    (by simp only [E, L, Functor.comp_obj, Sf.finite_eq, Sg.finite_eq,
      sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [L, Functor.comp_obj, Sf.finite_eq, Sg.finite_eq,
      sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [L, Sfg.finite_eq, sfCompactSupportFiniteFunctor, tobj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization]) hcomp hal
  have hi := congrArg (fun v ↦ (sfRationalConstructibleLocalization l L Z).map v)
    (sfIntegralComposition_coefficient_comm D l hl cf cg cfg E L ι
      (A E₀) (A L₀) (hA E₀) (hA L₀)
      (Sf.integralBeta h) (Sg.integralBeta h) (Sfg.integralBeta h)
      (Sf.integralBeta_spec h) (Sg.integralBeta_spec h) (Sfg.integralBeta_spec h) K.obj)
  simp only [Functor.map_comp, ← Category.assoc] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

end WeilConjectures
