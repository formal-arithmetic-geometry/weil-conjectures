/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Normalized geometric fibres of the rational heart

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 6.8.5 and Lemma 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The localized heart, with its already recorded raw category and standard t-structure.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
abbrev Heart (X : Base.{u} l) := (localizedT l E X).heart.FullSubcategory

attribute [instance] Chart.affine Chart.isEtale

/-- A system map induces its actual inverse-limit stalk map followed by balanced localization.
Source: BS 6.8.4(1),(4) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def rationalLimitMap {T : Scheme.{u}} (N M : Lattice l E T)
    (uN : N.system ⟶ M.system) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ T) : N.rationalFiber l E κ x ⟶ M.rationalFiber l E κ x :=
  (ModuleCat.extendScalars (Padic.coefficientExtensionIntegers l E).subtype).map
    (limMap (Functor.whiskerRight uN ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))))

attribute [instance] Point.additive Point.linear

/-- All normalized local lattice comparisons and joint detection assertions, for one E-stage.
The chart and presentation are universally quantified, so the same fibre is used for every
choice of stratification, etale chart, lattice and fractional representative.
Source: BS 6.8.4(1),(4),(6), 6.8.5 and 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Assertions (X : Base.{u} l) (a : At l E X) where
  point : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    Point l E X a κ x
  local_chart : ∀ (F : Heart l E X) (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme),
    ∃ (C : Chart l X) (t : Spec (.of κ) ⟶ C.scheme) (N : Lattice l E C.scheme),
      t ≫ C.map = x ∧ C.Adapted l E a F ∧
        Nonempty ((C.restrict l E a).obj F ≅ N.rational l E)
  integral_finite_free : ∀ (C : Chart l X) (N : Lattice l E C.scheme)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    Module.Finite (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ t) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ t)
  normalization : ∀ (C : Chart l X) (F : Heart l E X) (_hF : C.Adapted l E a F)
      (N : Lattice l E C.scheme) (_φ : (C.restrict l E a).obj F ≅ N.rational l E)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    (point κ (t ≫ C.map)).functor.obj F ≅ N.rationalFiber l E κ t
  fractions : ∀ (C : Chart l X) (F G : Heart l E X)
      (hF : C.Adapted l E a F) (hG : C.Adapted l E a G)
      (N M : Lattice l E C.scheme)
      (φ : (C.restrict l E a).obj F ≅ N.rational l E)
      (ψ : (C.restrict l E a).obj G ≅ M.rational l E)
      (f : F ⟶ G) (u : N.integral ⟶ M.integral) (uN : N.system ⟶ M.system)
      (_hu : Represents l E N M u uN) (b : ℕ)
      (_hf : (C.restrict l E a).map f ≫ ψ.hom = φ.hom ≫
        (((Padic.coefficientExtensionUniformizer l E : E) ^ b)⁻¹ •
          (pbcExtend (integralRationalCoefficientMap l E C.scheme)).map u))
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    (point κ (t ≫ C.map)).functor.map f ≫ (normalization C G hG M ψ κ t).hom =
      (normalization C F hF N φ κ t).hom ≫
        (((Padic.coefficientExtensionUniformizer l E : E) ^ b)⁻¹ •
          rationalLimitMap l E N M uN κ t)
  detects_zero : ∀ F : Heart l E X,
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsZero ((point κ x).functor.obj F)) → IsZero F
  detects_iso : ∀ (F G : Heart l E X) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsIso ((point κ x).functor.map f)) → IsIso f
  detects_zero_map : ∀ (F G : Heart l E X) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      (point κ x).functor.map f = 0) → f = 0
  detects_exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).Exact ↔
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        (S.map (point κ x).functor).Exact
  detects_short_exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).ShortExact ↔
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        (S.map (point κ x).functor).ShortExact

/-- An index for all geometric points, retaining the actual field and its structures.
Source: the geometric-point definition; BS 6.8.6.
(blueprint: def-per-adic-normalized-fibre-data). -/
structure GeometricPoint (X : Scheme.{u}) where
  field : Type u
  [fieldStructure : Field field]
  [closed : IsAlgClosed field]
  map : Spec (.of field) ⟶ X

attribute [instance] GeometricPoint.fieldStructure GeometricPoint.closed

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
