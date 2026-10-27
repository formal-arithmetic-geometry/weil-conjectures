/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.AdicNormalizedFibrePullback
public import Sheaf.Paper.PerAdicNormalizedFibreComparisons

/-! # Objectwise scalar fibre maps before naturality and coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- Restriction of the specified raw scalar unitor to the full heart.
Source: BS 6.8.14--6.8.15 (blueprint: def-per-scalar-fibre-component-data). -/
def scalarHeartUnit (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k) :
    heartScalar l A A (AlgHom.id ℚ_[l] A) X ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    ((pbcRationalScalarUnit l A X.scheme (base l X).dimension
      (base l X).prime_unit).app F.obj)) (by
    intro F G f
    apply InducedCategory.hom_ext
    exact (pbcRationalScalarUnit l A X.scheme (base l X).dimension
      (base l X).prime_unit).hom.naturality f.hom)

/-- Restriction of the specified raw scalar associator to the full heart.
Source: BS 6.8.14--6.8.15 (blueprint: def-per-scalar-fibre-component-data). -/
def scalarHeartComp (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C] (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C)
    (X : FiniteTypeBase k) :
    heartScalar l A B i X ⋙ heartScalar l B C j X ≅
      heartScalar l A C (j.comp i) X :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    ((pbcRationalScalarComp l A B C i j X.scheme (base l X).dimension
      (base l X).prime_unit).app F.obj)) (by
    intro F G f
    apply InducedCategory.hom_ext
    exact (pbcRationalScalarComp l A B C i j X.scheme (base l X).dimension
      (base l X).prime_unit).hom.naturality f.hom)

/-- Restriction of the family's specified raw mixed comparison to the full heart.
Source: BS 6.8.15 (blueprint: def-per-scalar-fibre-component-data). -/
def scalarHeartMixed (A B : Type u) [Field A] [Field B]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme) :
    heartScalar l A B i X ⋙ heartPull l B R g ≅
      heartPull l A R g ⋙ heartScalar l A B i Y :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    ((R.mixed A B i (X := base l Y) (Y := base l X) g).raw.app F.obj)) (by
    intro F G f
    apply InducedCategory.hom_ext
    exact (R.mixed A B i (X := base l Y) (Y := base l X) g).raw.hom.naturality f.hom)

/-- Objectwise balanced scalar comparisons with their germ and reduction-cone formulas.
No naturality in heart morphisms or identity, composition or mixed equation is assumed.
These are construction data, without any assertion that they exist.
Source: BS 6.8.4(1),(4), 6.8.14--6.8.15
(blueprint: def-per-scalar-fibre-component-data). -/
structure ScalarFibreComponents (ω : Fibres (k := k) l R) where
  component : ∀ (A B : Type u) [Field A] [Field B]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    ∀ F : NormalizedFibre.Heart l A (base l X),
      ((ω B X).point κ x).functor.obj ((heartScalar l A B i X).obj F) ≅
        (ModuleCat.extendScalars i.toRingHom).obj (((ω A X).point κ x).functor.obj F)

  unit_normalization : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l A (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme A))
    (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M),
    ∃ e' : (R.realization B (base l X)).J.obj ((heartScalar l A B i X).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((pbcExtend (R.fieldChange A B i (base l X)).coefficient).obj M),
      e'.hom = scalarModelMap l R A B i X F M e ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (U : X.scheme.ProEt)
        (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange x).obj U)
        (m : M.val.obj (op U)),
        ∀ b : B,
        (presentedFibre l R B ω X ((heartScalar l A B i X).obj F) _ e' κ x).hom
          (((component A B i X κ x F).inv)
            (b ⊗ₜ[A, i.toRingHom] (presentedFibre l R A ω X F M e κ x).inv
              (germ l A M κ x U q m))) =
          b • germ l B _ κ x U q
            (pbcTensorSection (R.fieldChange A B i (base l X)).coefficient M (op U) 1 m)

  local_normalization :
    ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
      (F : NormalizedFibre.Heart l A (base l X)) (C : NormalizedFibre.Chart l (base l X))
      (hA : C.Adapted l A (R.realization A (base l X)) F)
      (N : NormalizedFibre.Lattice l A C.scheme)
      (φ : (C.restrict l A (R.realization A (base l X))).obj F ≅ N.rational l A),
      ∃ (hB : C.Adapted l B (R.realization B (base l X))
        ((heartScalar l A B i X).obj F))
        (M : NormalizedFibre.Lattice l B C.scheme)
        (ψ : (C.restrict l B (R.realization B (base l X))).obj
          ((heartScalar l A B i X).obj F) ≅ M.rational l B)
        (r : rationalCoefficientSheaf l C.scheme A ⟶ rationalCoefficientSheaf l C.scheme B)
        (q : (C.restrict l B (R.realization B (base l X))).obj
          ((heartScalar l A B i X).obj F) ≅
            (pbcExtend r).obj ((C.restrict l A (R.realization A (base l X))).obj F))
        (η : (pbcExtend r).obj (N.rational l A) ≅ M.rational l B)
        (τ : ∀ n : ℕ, finiteScalarLevel l A B i C.scheme (N.system.obj (op n)) n ≅
          M.system.obj (op n)),
        IsScalarChartMap l R A B i X F C r q ∧ IsScalarLattice l A B i C.scheme N M r η τ ∧
        ψ.hom = q.hom ≫ (pbcExtend r).map φ.hom ≫ η.hom ∧
        ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
        ∃ (e : scalarQuotients l A B i (N.fiber l A κ t) ≅
          M.system ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l B)))
          (a : (ModuleCat.extendScalars.{u, u, u + 1}
            (WeilConjectures.integralScalarIntegerInclusion l A B i)).obj
              (N.fiber l A κ t) ≅ M.fiber l B κ t),
          (∀ (n : ℕ) (w : N.fiber l A κ t) (b : Padic.coefficientExtensionIntegers l B)
            (U : C.scheme.Etale) (x : (pointSmallEtale t).ulift.{u + 1}.fiber.obj U)
            (m : (N.system.obj (op n)).obj.obj (op U)),
            limit.π (N.system ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber
              (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A))) (op n) w =
                (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U x
                  (N.system.obj (op n)).obj m →
            (e.hom.app (op n))
              ((Padic.coefficientExtensionIdeal l B 1 ^ (n + 1) • ⊤ :
                Submodule (Padic.coefficientExtensionIntegers l B)
                  ((ModuleCat.extendScalars.{u, u, u + 1}
                    (WeilConjectures.integralScalarIntegerInclusion l A B i)).obj
                      (N.fiber l A κ t))).mkQ
                (b ⊗ₜ[Padic.coefficientExtensionIntegers l A,
                  WeilConjectures.integralScalarIntegerInclusion l A B i] w)) =
              b • (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U x
                (M.system.obj (op n)).obj
                  ((τ n).hom.hom.app (op U)
                    ((finiteScalarUnit l A B i C.scheme (N.system.obj (op n)) n).hom.app
                      (op U) m))) ∧
          a.hom ≫ limMap (J := ℕᵒᵖ)
              (C := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l B)) e.inv =
            scalarCompletionMap l A B i (N.fiber l A κ t) ∧
          ∀ (b : B) (a₀ : A) (n : N.fiber l A κ t),
            ((ω B X).normalization C ((heartScalar l A B i X).obj F) hB M ψ κ t).hom
              (((component A B i X κ (t ≫ C.map) F).inv)
                (b ⊗ₜ[A, i.toRingHom]
                  ((ω A X).normalization C F hA N φ κ t).inv
                    (a₀ ⊗ₜ[Padic.coefficientExtensionIntegers l A,
                      (Padic.coefficientExtensionIntegers l A).subtype] n))) =
              (b * i a₀) •
                ((1 : B) ⊗ₜ[Padic.coefficientExtensionIntegers l B,
                  (Padic.coefficientExtensionIntegers l B).subtype]
                  (a.hom ((1 : Padic.coefficientExtensionIntegers l B) ⊗ₜ[
                    Padic.coefficientExtensionIntegers l A,
                    WeilConjectures.integralScalarIntegerInclusion l A B i] n)))

/-- Tensor unit, tensor composition and mixed equations for objectwise scalar maps.
This is a property of specified components, and asserts no existence of such components.
Source: BS 6.8.14--6.8.15 (blueprint: def-per-scalar-fibre-component-data). -/
structure ScalarFibreCoherence (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω) (d : ScalarFibreComponents l R ω) : Prop where
  scalar_id : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k),
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        (d.component A A (AlgHom.id ℚ_[l] A) X κ x F).hom ≫
          (ModuleCat.extendScalarsId.{u, u + 1} A).hom.app
            (((ω A X).point κ x).functor.obj F) =
          ((ω A X).point κ x).functor.map ((scalarHeartUnit l A X).hom.app F)
  scalar_comp : ∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C] (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C)
    (X : FiniteTypeBase k),
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((ω C X).point κ x).functor.map ((scalarHeartComp l A B C i j X).hom.app F) ≫
          (d.component A C (j.comp i) X κ x F).hom ≫
            (ModuleCat.extendScalarsComp.{u, u + 1} i.toRingHom j.toRingHom).hom.app
              (((ω A X).point κ x).functor.obj F) =
          (d.component B C j X κ x ((heartScalar l A B i X).obj F)).hom ≫
            (ModuleCat.extendScalars.{u, u, u + 1} j.toRingHom).map
              ((d.component A B i X κ x F).hom)
  mixed : ∀ (A B : Type u) [Field A] [Field B]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme),
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((ω B Y).point κ y).functor.map ((scalarHeartMixed l R A B i X Y g).hom.app F) ≫
          (d.component A B i Y κ y ((heartPull l A R g).obj F)).hom ≫
            (ModuleCat.extendScalars i.toRingHom).map ((α.pull A g κ y).hom.app F) =
          (α.pull B g κ y).hom.app ((heartScalar l A B i X).obj F) ≫
            (d.component A B i X κ (y ≫ g) F).hom


end AlgebraicGeometry.Scheme.AdicFibreComparison
