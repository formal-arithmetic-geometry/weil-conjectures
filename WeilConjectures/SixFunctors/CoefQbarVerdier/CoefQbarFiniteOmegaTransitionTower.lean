/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionComposition
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierIntegralCompNormalization

/-! # Rational transition omega tower

(blueprint: lem-coef-qbar-finite-omega-transition-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem localize_triangle
    {C₀ C₁ C₂ R₀ R₁ R₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category R₀] [Category R₁] [Category R₂]
    (T : C₀ ⥤ C₁) (U : C₁ ⥤ C₂) (V : C₀ ⥤ C₂)
    (Q₀ : C₀ ⥤ R₀) (Q₁ : C₁ ⥤ R₁) (Q₂ : C₂ ⥤ R₂)
    (R : R₀ ⥤ R₁) (S : R₁ ⥤ R₂) (W : R₀ ⥤ R₂)
    (eT : ∀ K, R.obj (Q₀.obj K) = Q₁.obj (T.obj K))
    (eU : ∀ K, S.obj (Q₁.obj K) = Q₂.obj (U.obj K))
    (eV : ∀ K, W.obj (Q₀.obj K) = Q₂.obj (V.obj K))
    (mU : ∀ {K K'} (f : K ⟶ K'),
      HEq (S.map (Q₁.map f)) (Q₂.map (U.map f)))
    (A : R ⋙ S ≅ W) (x : C₀) (y : C₁) (z : C₂)
    (aI : T.obj x ⟶ y) (bI : U.obj y ⟶ z) (cI : V.obj x ⟶ z)
    (dI : U.obj (T.obj x) ⟶ V.obj x)
    (a : R.obj (Q₀.obj x) ⟶ Q₁.obj y)
    (b : S.obj (Q₁.obj y) ⟶ Q₂.obj z)
    (c : W.obj (Q₀.obj x) ⟶ Q₂.obj z)
    (ha : HEq a (Q₁.map aI)) (hb : HEq b (Q₂.map bI))
    (hc : HEq c (Q₂.map cI))
    (hd : HEq (A.hom.app (Q₀.obj x)) (Q₂.map dI))
    (hi : U.map aI ≫ bI = dI ≫ cI) :
    S.map a ≫ b = A.hom.app (Q₀.obj x) ≫ c := by
  have hx := (congrArg S.obj (eT x)).trans (eU (T.obj x))
  have ha' := (map_heq S (eT x) rfl ha).trans (mU aI)
  have hleft := heq_comp hx (eU y) rfl ha' hb
  have hright := heq_comp hx (eV x) rfl hd hc
  have hmid : Q₂.map (U.map aI) ≫ Q₂.map bI =
      Q₂.map dI ≫ Q₂.map cI := by
    rw [← Q₂.map_comp, hi, Q₂.map_comp]
  exact eq_of_heq (hleft.trans ((heq_of_eq hmid).trans hright.symm))

private theorem rational_map_localization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    {K K' : sfIntegralConstructibleCategory l E X} (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).map
        ((sfRationalConstructibleLocalization l E X).map f))
      ((sfRationalConstructibleLocalization l L X).map
        ((RationalVerdier.integralScalar l X E L i).map f)) := by
  have h := sfRationalScalarExtension_map_tmul l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i K K' f 1
  simp only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
    map_one] at h
  convert h using 1
  rfl

private theorem rational_omega_composition
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (q : E →ₐ[Padic l] M)
    (hq : j.comp i = q)
    (A : RationalVerdier.scalar l X E L i ⋙ RationalVerdier.scalar l X L M j ≅
      RationalVerdier.scalar l X E M q)
    (hA : A = GeneralAlgebraicallyClosedCoefficients.scalarAssociator l E L M i j q hq X)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (wM : IntegralFiniteExtension.DualizingDatum l X D hl M)
    (a : (RationalVerdier.scalar l X E L i).obj
      ((sfRationalConstructibleLocalization l E X).obj wE.omega) ⟶
        (sfRationalConstructibleLocalization l L X).obj wL.omega)
    (b : (RationalVerdier.scalar l X L M j).obj
      ((sfRationalConstructibleLocalization l L X).obj wL.omega) ⟶
        (sfRationalConstructibleLocalization l M X).obj wM.omega)
    (c : (RationalVerdier.scalar l X E M q).obj
      ((sfRationalConstructibleLocalization l E X).obj wE.omega) ⟶
        (sfRationalConstructibleLocalization l M X).obj wM.omega)
    (ha : HEq a ((sfRationalConstructibleLocalization l L X).map
      (ObjectProperty.homMk
        (X := (RationalVerdier.integralScalar l X E L i).obj wE.omega)
        (Y := wL.omega) (IntegralFiniteExtension.u l E L i X D hl wE wL))))
    (hb : HEq b ((sfRationalConstructibleLocalization l M X).map
      (ObjectProperty.homMk
        (X := (RationalVerdier.integralScalar l X L M j).obj wL.omega)
        (Y := wM.omega) (IntegralFiniteExtension.u l L M j X D hl wL wM))))
    (hc : HEq c ((sfRationalConstructibleLocalization l M X).map
      (ObjectProperty.homMk
        (X := (RationalVerdier.integralScalar l X E M q).obj wE.omega)
        (Y := wM.omega) (IntegralFiniteExtension.u l E M q X D hl wE wM))))
    (hi : (integralScalarExtensionOfUniverses l L M j X).map
        (IntegralFiniteExtension.u l E L i X D hl wE wL) ≫
      IntegralFiniteExtension.u l L M j X D hl wL wM =
        (IntegralFiniteExtension.comp l E L i X M j
          wE.omega.obj wE.omega.property.1).hom ≫
        IntegralFiniteExtension.u l E M (j.comp i) X D hl wE wM) :
    (RationalVerdier.scalar l X L M j).map a ≫ b =
      A.hom.app ((sfRationalConstructibleLocalization l E X).obj wE.omega) ≫ c := by
  subst A
  subst q
  simp only [GeneralAlgebraicallyClosedCoefficients.scalarAssociator, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  apply localize_triangle
    (RationalVerdier.integralScalar l X E L i)
    (RationalVerdier.integralScalar l X L M j)
    (RationalVerdier.integralScalar l X E M (j.comp i))
    (sfRationalConstructibleLocalization l E X)
    (sfRationalConstructibleLocalization l L X)
    (sfRationalConstructibleLocalization l M X)
    (RationalVerdier.scalar l X E L i)
    (RationalVerdier.scalar l X L M j)
    (RationalVerdier.scalar l X E M (j.comp i))
    (fun K ↦ sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i _)
    (fun K ↦ sfRationalScalarExtension_obj l L X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j _)
    (fun K ↦ sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M (j.comp i) _)
    (fun f ↦ rational_map_localization l L M j X f)
    (sfRationalScalarComp l E L i X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j)
    wE.omega wL.omega wM.omega
    (ObjectProperty.homMk (IntegralFiniteExtension.u l E L i X D hl wE wL))
    (ObjectProperty.homMk (IntegralFiniteExtension.u l L M j X D hl wL wM))
    (ObjectProperty.homMk (IntegralFiniteExtension.u l E M (j.comp i) X D hl wE wM))
    ((sfIntegralScalarComp l E L i X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app wE.omega)
    a b c ha hb hc
    ((sfRationalScalarComp_existsUnique l E L i X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec _)
  rw [RationalVerdier.integral_comp_normalization_bridge]
  apply ObjectProperty.hom_ext
  exact hi

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem stageSystem_existsUnique)

/-- The rational transition omega maps obey the scalar associator tower equation.
Source: the composition component of `lem-sf-integral-finite-extension-composition`,
localized through `RationalVerdier.ExtensionProperties`.
(blueprint: lem-coef-qbar-finite-omega-transition-tower). -/
theorem finiteOmegaTransition_tower (F : Finite D l hl Ω X)
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    (sfRationalScalarExtension l (Coefficient.{u} l Ω L) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k)).map ((F.scalar E L h).omega.hom) ≫
        (F.scalar L M k).omega.hom =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (F.omega E).omega) ≫
        (F.scalar E M (h.trans k)).omega.hom := by
  have hcomp := IntegralFiniteExtension.comparison_composition
    l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) X D hl (F.omega E) (F.omega L)
    (F.datum E).ordinary (F.datum L).ordinary
    (fun K K' N f ↦ IntegralHom.evaluation_naturality X _
      (F.datum E).ordinary K K' N f)
    (fun K K' N f ↦ IntegralHom.evaluation_naturality X _
      (F.datum L).ordinary K K' N f)
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k)
    (F.omega M) (F.datum M).ordinary
    (fun K K' N f ↦ IntegralHom.evaluation_naturality X _
      (F.datum M).ordinary K K' N f)
  have hA := (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
    l Ω X E L M h k).exists.choose_spec
  change HEq _ _ at hA
  delta GeneralAlgebraicallyClosedCoefficients.stageCategory at hA
  have hA' := eq_of_heq hA
  exact rational_omega_composition D l hl X
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
    (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k)
    (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k)
    (by with_unfolding_all exact hA')
    (F.omega E) (F.omega L) (F.omega M)
    (F.scalar E L h).omega.hom (F.scalar L M k).omega.hom
    (F.scalar E M (h.trans k)).omega.hom
    (F.normalized E L h).1 (F.normalized L M k).1
    (F.normalized E M (h.trans k)).1 hcomp.2.2.1

end WeilConjectures.CoefQbarVerdier
