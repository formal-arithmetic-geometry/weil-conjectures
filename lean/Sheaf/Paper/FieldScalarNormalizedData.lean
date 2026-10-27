/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.Paper.FieldScalarReductionData

public import Sheaf.Paper.SmoothPurityReductionTowerNormalized
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Data for normalized field scalar systems

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1)
(blueprint: def-sp-field-scalar-normalized-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

/-- Scalar associativity is specified as a natural comparison of ordinary and derived
functors, with its cochain counit equation. Source: paragraph (1), successive extensions
(blueprint: def-sp-field-scalar-normalized-data). -/
structure Compositor
    {A B C DA DB DC : Type a} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Category.{w} DA] [Category.{w} DB] [Category.{w} DC]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (Q₁ : CochainComplex A ℤ ⥤ DA) (Q₂ : CochainComplex B ℤ ⥤ DB)
    (Q₃ : CochainComplex C ℤ ⥤ DC)
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    (f : DA ⥤ DB) (g : DB ⥤ DC) (h : DA ⥤ DC)
    (εF : Q₁ ⋙ f ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ Q₂)
    (εG : Q₂ ⋙ g ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ Q₃)
    (εH : Q₁ ⋙ h ⟶ H.mapHomologicalComplex (.up ℤ) ⋙ Q₃) where
  ordinary : F ⋙ G ≅ H
  derived : f ⋙ g ≅ h
  representative : ∀ P : CochainComplex A ℤ,
    derived.hom.app (Q₁.obj P) ≫ εH.app P =
      g.map (εF.app P) ≫ εG.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        Q₃.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)

end AlgebraicGeometry.ProEtale.FieldScalar

namespace AlgebraicGeometry.ProEtale.FieldScalar

variable {l : ℕ} [Fact l.Prime] {E F L : Type u} [Field E] [Field F] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  [FiniteDimensional (Padic l) L]
  {ι : E →ₐ[Padic l] F} {κ : F →ₐ[Padic l] L} {T : Scheme.{u}}
  {DA : SpCoefficientTowersAbelian.{u, u} l E T}
  {DB : SpCoefficientTowersAbelian.{u, u} l F T}
  {DC : SpCoefficientTowersAbelian.{u, u} l L T}
  {RA : SpReductionTower l E T DA} {RB : SpReductionTower l F T DB}
  {RC : SpReductionTower l L T DC}

/-- All conclusions for one inclusion, including the normalization of the canonical
comparison. Source: paragraph (1) (blueprint: def-sp-field-scalar-normalized-data). -/
structure ScalarData (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (T : Scheme.{u})
    (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (DB : SpCoefficientTowersAbelian.{u, u} l F T)
    (RA : SpReductionTower l E T DA) (RB : SpReductionTower l F T DB) where
  coefficients : Coefficients l E F ι T DA DB RA RB
  extension : ExactExtension DA DB RA RB coefficients
  coordinates : Coordinates.{u} coefficients extension
  comparison : ReductionComparison coefficients extension

/-- The ordinary-derived compositor for the completed coefficient rings, with the
existing universal scalar counits. Source: paragraph (1), successive field extensions
(blueprint: def-sp-field-scalar-normalized-data). -/
abbrev IntegralCompositor
    (D₁ : ScalarData l E F ι T DA DB RA RB)
    (D₂ : ScalarData l F L κ T DB DC RB RC)
    (D₃ : ScalarData l E L (κ.comp ι) T DA DC RA RC) :=
  Compositor (A := spIntegralSectionModules l E T) (B := spIntegralSectionModules l F T)
    (C := spIntegralSectionModules l L T)
    (DA := DerivedCategory (spIntegralSectionModules l E T))
    (DB := DerivedCategory (spIntegralSectionModules l F T))
    (DC := DerivedCategory (spIntegralSectionModules l L T))
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (integralScalar D₁.coefficients).model.E (integralScalar D₂.coefficients).model.E
    (integralScalar D₃.coefficients).model.E
    (integralScalar D₁.coefficients).model.T (integralScalar D₂.coefficients).model.T
    (integralScalar D₃.coefficients).model.T
    (integralScalar D₁.coefficients).model.ε (integralScalar D₂.coefficients).model.ε
    (integralScalar D₃.coefficients).model.ε

/-- The ordinary-derived compositor for exact scalar extension of whole towers.
Source: paragraph (1), successive extensions
(blueprint: def-sp-field-scalar-normalized-data). -/
abbrev SystemCompositor
    (D₁ : ScalarData l E F ι T DA DB RA RB)
    (D₂ : ScalarData l F L κ T DB DC RB RC)
    (D₃ : ScalarData l E L (κ.comp ι) T DA DC RA RC) :=
  letI := D₁.extension.additive
  letI := D₂.extension.additive
  letI := D₃.extension.additive
  Compositor (spTowerLocalization l E T DA) (spTowerLocalization l F T DB)
    (spTowerLocalization l L T DC)
    D₁.extension.ordinary D₂.extension.ordinary D₃.extension.ordinary
    D₁.extension.derived D₂.extension.derived D₃.extension.derived
    D₁.extension.counit D₂.extension.counit D₃.extension.counit

/-- Tensor associativity and the reduction square for three successive coefficient
fields. Both ordinary compositors are fixed by multiplication on local generators;
their derived versions are fixed by their cochain counit equations, not arbitrary isos.
Source: paragraph (1), successive field extensions
(blueprint: def-sp-field-scalar-normalized-data). -/
structure Successive
    (D₁ : ScalarData l E F ι T DA DB RA RB)
    (D₂ : ScalarData l F L κ T DB DC RB RC)
    (D₃ : ScalarData l E L (κ.comp ι) T DA DC RA RC) where
  integral : IntegralCompositor D₁ D₂ D₃
  system : SystemCompositor D₁ D₂ D₃
  integral_tmul : ∀ (M : spIntegralSectionModules l E T) (U : T.ProEtᵒᵖ)
    (s : (spIntegralSectionRing l F T).obj.obj U)
    (t : (spIntegralSectionRing l L T).obj.obj U) (x : M.val.obj U),
    (integral.ordinary.hom.app M).val.app U
      (systemModelTmul (integralScalar D₂.coefficients).model _ U t
        (systemModelTmul (integralScalar D₁.coefficients).model M U s x)) =
    systemModelTmul (integralScalar D₃.coefficients).model M U
      ((D₂.coefficients.integral.hom.app U s) * t) x
  system_tmul : ∀ (M : spCoefficientTowers.{u, u} l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (s : ((spCoefficientCommRings.{u, u} l F T).obj (op n)).obj.obj U)
    (t : ((spCoefficientCommRings.{u, u} l L T).obj (op n)).obj.obj U)
    (x : ((DA.equivalence.functor.obj M).level n).val.obj U),
    ((spCoefficientEvaluation.{u, u} l L T DC.equivalence n).map
      (system.ordinary.hom.app M)).val.app U
        (((D₂.extension.level n).inv.app (D₁.extension.ordinary.obj M)).val.app U
          (systemModelTmul (DB.scalar (D₂.coefficients.tower.app (op n))).model _ U t
            (((D₁.extension.level n).inv.app M).val.app U
              (systemModelTmul (DA.scalar (D₁.coefficients.tower.app (op n))).model
                _ U s x)))) =
    ((D₃.extension.level n).inv.app M).val.app U
      (systemModelTmul (DA.scalar (D₃.coefficients.tower.app (op n))).model _ U
        (((D₂.coefficients.tower.app (op n)).hom.app U s) * t) x)
  square : ∀ K : DerivedCategory (spIntegralSectionModules l E T),
    RC.red.map (integral.derived.hom.app K) ≫ D₃.comparison.isoDerived.hom.app K =
      D₂.comparison.isoDerived.hom.app ((integralScalar D₁.coefficients).model.T.obj K) ≫
        D₂.extension.derived.map (D₁.comparison.isoDerived.hom.app K) ≫
        system.derived.hom.app (RA.red.obj K)

/-- Identity scalar extension is multiplication, on both completed coefficients and
whole towers, and the reduction comparison respects these unitors. Derived unitors
are specified by the ordinary cochain comparisons and universal derived counits.
Source: paragraph (1), identity extension
(blueprint: def-sp-field-scalar-normalized-data). -/
structure Identity (D : ScalarData l E E (AlgHom.id (Padic l) E) T DA DA RA RA) where
  integral : (integralScalar D.coefficients).model.E ≅ 𝟭 (spIntegralSectionModules l E T)
  system : D.extension.ordinary ≅ 𝟭 (spCoefficientTowers.{u, u} l E T)
  integral_tmul : ∀ (M : spIntegralSectionModules l E T) (U : T.ProEtᵒᵖ)
    (r : (spIntegralSectionRing l E T).obj.obj U) (x : M.val.obj U),
    (integral.hom.app M).val.app U
      (systemModelTmul (integralScalar D.coefficients).model M U r x) = r • x
  system_tmul : ∀ (M : spCoefficientTowers.{u, u} l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (r : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U)
    (x : ((DA.equivalence.functor.obj M).level n).val.obj U),
    ((spCoefficientEvaluation.{u, u} l E T DA.equivalence n).map
      (system.hom.app M)).val.app U
      (((D.extension.level n).inv.app M).val.app U
        (systemModelTmul (DA.scalar (D.coefficients.tower.app (op n))).model _ U r x)) =
      r • x
  integralDerived : (integralScalar D.coefficients).model.T ≅
    𝟭 (DerivedCategory (spIntegralSectionModules l E T))
  systemDerived : D.extension.derived ≅ 𝟭 (spDerivedCoefficientTowers l E T DA)
  integral_rep : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
    integralDerived.hom.app (DerivedCategory.Q.obj P) =
      (integralScalar D.coefficients).model.ε.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex integral.hom (.up ℤ)).app P)
  system_rep : ∀ P : CochainComplex (spCoefficientTowers.{u, u} l E T) ℤ,
    systemDerived.hom.app ((spTowerLocalization l E T DA).obj P) =
      D.extension.counit.app P ≫ (spTowerLocalization l E T DA).map
        ((NatTrans.mapHomologicalComplex system.hom (.up ℤ)).app P)
  square : ∀ K : DerivedCategory (spIntegralSectionModules l E T),
    D.comparison.isoDerived.hom.app K ≫ systemDerived.hom.app (RA.red.obj K) =
      RA.red.map (integralDerived.hom.app K)

end AlgebraicGeometry.ProEtale.FieldScalar

namespace AlgebraicGeometry.ProEtale.FieldScalar

/-- A simultaneous choice of normalized scalar functors, with their canonical identity
and successive-extension constraints. The choices of bases need not be compositional;
the canonical tensor comparisons are compositional. Source: paragraph (1)
(blueprint: def-sp-field-scalar-normalized-data). -/
structure Family (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) where
  data : ∀ (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (DB : SpCoefficientTowersAbelian.{u, u} l F T)
    (RA : SpReductionTower l E T DA) (RB : SpReductionTower l F T DB),
    ScalarData l E F ι T DA DB RA RB
  identity : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (DA : SpCoefficientTowersAbelian.{u, u} l E T) (RA : SpReductionTower l E T DA),
    Nonempty (Identity (data E E (AlgHom.id (Padic l) E) DA DA RA RA))
  successive : ∀ (E F L : Type u) [Field E] [Field F] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] F) (κ : F →ₐ[Padic l] L)
    (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (DB : SpCoefficientTowersAbelian.{u, u} l F T)
    (DC : SpCoefficientTowersAbelian.{u, u} l L T)
    (RA : SpReductionTower l E T DA) (RB : SpReductionTower l F T DB)
    (RC : SpReductionTower l L T DC),
    Nonempty (Successive (data E F ι DA DB RA RB) (data F L κ DB DC RB RC)
      (data E L (κ.comp ι) DA DC RA RC))
  cofinal : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E],
    ∃ (h : ℕ) (a : (Padic.coefficientExtensionIntegers l E)ˣ), 0 < h ∧
      (l : Padic.coefficientExtensionIntegers l E) =
        a * Padic.coefficientExtensionUniformizer l E ^ h ∧
      ∀ n : ℕ, spEllIdeal l E ^ n =
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ (h * n)

end AlgebraicGeometry.ProEtale.FieldScalar
