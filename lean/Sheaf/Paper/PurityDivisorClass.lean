/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
public import Sheaf.CategoryTheory.Sites.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import Sheaf.Paper.SupportedCupFunctoriality
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.SmoothCodimensionOneCartier
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import Sheaf.Paper.NormalizedCartierLocalEquation
import Sheaf.Paper.NormalizedCartierSum
public import Sheaf.Paper.NormalizedCartierForget

/-!
# The canonical Kummer class of a Cartier divisor

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-divisor-class (blueprint: lem-pur-divisor-class).

The relative normalization is the published torsor-extension specification, including
its specified section off the divisor. Classes are represented by Ext, then transported
by the published supported-Hom site comparison. Heterogeneous equalities identify
the identical representations without asking the kernel to renormalize the full
localization data. The singleton range in the frame clause is equal to {f} by
Set.range_const; HEq therefore also expresses that exact support-index transport.
This is the supported cohomology of
`def-pur-support-cohomology`, via `supported_cohomology_hom`. No module structure on
G_m is used. The coefficient exponent is ell^n for every positive coefficient level n.

## Main definitions and statement

* `DivisorEtaleClasses` and `DivisorEtaleNormalized` record the relative construction.
* `DivisorLocalEquations`, `DivisorAdditive`, and `DivisorChern` spell out its compatibilities.
* `divisor_class` asserts that construction and every compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u vH vK

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupHasDerived functorialCupAbelian functorialCupCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Abelian.Ext.homEquiv
  functorialCupOrdinaryCompare functorialCupCompare functorialCupForget
  functorialCupChangeSupport functorialCupPullback

/-- The etale representatives of divisor classes on T, indexed by actual Cartier
immersions. Source: blueprint lem-pur-divisor-class, global relative construction
(blueprint: lem-pur-divisor-class). -/
structure DivisorEtaleClasses (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) where
  /-- The etale class of each Cartier immersion. Source: blueprint relative construction
  (blueprint: lem-pur-divisor-class). -/
  classOf : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
    i.ker.IsInvertible → Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2
  /-- The same class in the published supported-Hom interface. Source: blueprint comparison
  (blueprint: lem-pur-divisor-class). -/
  homClassOf : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
    i.ker.IsInvertible → P.FunctorialCupH false i 2 1
  /-- Exact identity of the two realizations. Source: Mathlib Ext.hom and blueprint comparison
  (blueprint: lem-pur-divisor-class). -/
  realizes : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible), HEq (classOf i hI).hom (homClassOf i hI)

/-- The relative torsor Kummer normalization, in the existing extension model.
In particular the divisor section, rather than an arbitrary lift of the Picard class,
is retained. Source: blueprint lem-pur-divisor-class, second sentence
(blueprint: lem-pur-divisor-class). -/
def DivisorEtaleNormalized (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T) : Prop :=
  ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible),
    Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a) (C.classOf i hI)

/-- The actual site-comparison image of a supported etale Hom representative.
Source: blueprint lem-pur-divisor-class, coefficient map
(blueprint: lem-pur-divisor-class). -/
def divisorProEtale (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (c : P.FunctorialCupH false i 2 1) :
    P.FunctorialCupH true i 2 1 := P.functorialCupCompare i 2 1 c

/-- Both local descriptions of the fixed global relative class, for every etale
principal presentation of its support, with minus the frame boundary in the Yoneda
normalization of SupportedKummerBoundary. Source: blueprint lem-pur-divisor-class,
clause (a) and frame comparison (blueprint: lem-pur-divisor-class). -/
def DivisorLocalEquations (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  ∀ (U : Scheme.{u}) (e : U ⟶ T) [Etale e] (f : Γ(U, ⊤))
  (t : U.zeroLocusSubscheme {f} ⟶ D)
  (sq : ChosenCartesianSquare t (U.zeroLocusSubschemeι {f}) i e),
  HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (-(P.frameBoundary U (e ≫ a) f)) ∧
  HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (-(P.frameBoundaryProduct U (e ≫ a) 1 (fun _ : Fin 1 ↦ f)))

/-- Product-ideal addition in the common union support. The quantified support
inclusions are unique because s is monic. Source: blueprint lem-pur-divisor-class,
clause (b) (blueprint: lem-pur-divisor-class). -/
def DivisorAdditive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (C : P.DivisorEtaleClasses T) : Prop :=
  ∀ {D₁ D₂ Z : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (s : Z ⟶ T)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion s]
  (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
  (_hs : s.ker = i₁.ker * i₂.ker),
  ∃ (hsum : s.ker.IsInvertible) (a₁ : D₁ ⟶ Z) (a₂ : D₂ ⟶ Z)
    (ha₁ : a₁ ≫ s = i₁) (ha₂ : a₂ ≫ s = i₂),
    P.divisorProEtale s (C.homClassOf s hsum) =
      P.functorialCupChangeSupport true s i₁ a₁ ha₁ 2 1
          (P.divisorProEtale i₁ (C.homClassOf i₁ h₁)) +
        P.functorialCupChangeSupport true s i₂ a₂ ha₂ 2 1
          (P.divisorProEtale i₂ (C.homClassOf i₂ h₂))

/-- Ordinary Kummer normalization and its equality with forgetting the supported
class, through the identical site comparison. Source: blueprint lem-pur-divisor-class,
final paragraph (blueprint: lem-pur-divisor-class). -/
def DivisorChern (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  divisorChernSpecification
    (P.divisorOrdinaryHom T)
    (P.divisorOrdinaryRealization T)
    (Etale.supportedKummerChern P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a))
    (P.functorialCupForget true i 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (P.functorialCupOrdinaryCompare T 2 1)

private theorem divisor_classes_ext {P : PurityFiniteSetting.{u}} {T : Scheme.{u}}
    {C C' : P.DivisorEtaleClasses T} (h : @C.classOf = @C'.classOf) : C = C' := by
  cases C with
  | mk c g hg =>
    cases C' with
    | mk c' g' hg' =>
      dsimp only at h
      cases h
      have hh : @g = @g' := by
        funext D i inst hI
        exact eq_of_heq ((hg i hI).symm.trans (hg' i hI))
      cases hh
      rfl


private theorem normalized_boundary_unique (P : PurityFiniteSetting.{u})
    {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃! κ : Abelian.Ext ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale D)) (P.frameTwistEtale T 1) 2,
      Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a) κ :=
  Etale.ordinary_supported_kummer_uniqueBoundary T P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates (P.diagonalExponent_isUnit a) i hI

private theorem classes_exists (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (c : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
      i.ker.IsInvertible → Abelian.Ext
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
        (P.frameTwistEtale T 1) 2) :
    ∃ C : P.DivisorEtaleClasses T, @C.classOf = @c := by
  refine ⟨{ classOf := @c
            homClassOf := fun i _ hI ↦ (c i hI).hom
            realizes := fun i _ hI ↦ HEq.rfl }, rfl⟩

/-- The relative construction exists uniquely for every Cartier divisor on T.
Source: lem-pur-divisor-class, second paragraph (blueprint: lem-pur-divisor-class).
Proof: for each Cartier immersion apply ordinary_supported_kummer at ell^n and A.
Its SupportedKummerBoundary specifies the frame torsor of the dual Cartier ideal,
with the canonical frame off the divisor sent to zero. Its uniqueness gives a
unique Ext class. Take its canonical Ext.hom as the Hom realization. Ext.hom is
injective, and HEq with that realization determines homClassOf, so these classes
assemble to a unique DivisorEtaleClasses. No smoothness is needed. -/
theorem existsUnique_generalDivisorEtaleClasses (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃! C : P.DivisorEtaleClasses T, P.DivisorEtaleNormalized T a C := by
  classical
  have hκ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
      (hI : i.ker.IsInvertible) := normalized_boundary_unique P a i hI
  obtain ⟨C, hc⟩ := classes_exists P T (fun i _ hI ↦ (hκ i hI).choose)
  refine ⟨C, ?_, ?_⟩
  · intro D i _ hI
    simpa only [hc] using (hκ i hI).choose_spec.1
  · intro C' hC'
    have hclass : @C'.classOf = @C.classOf := by
      funext D i inst hI
      rw [hc]
      change C'.classOf i hI = (hκ i hI).choose
      exact (hκ i hI).choose_spec.2 _ (hC' i hI)
    exact divisor_classes_ext hclass

/-- The unique normalized etale family, retaining the relative trivialization.
Source: lem-pur-divisor-class, general construction (blueprint: lem-pur-divisor-class).
-/
def generalDivisorEtaleClasses (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] : P.DivisorEtaleClasses T :=
  (P.existsUnique_generalDivisorEtaleClasses T a).choose

/-- The general divisor class in the recorded supported-Hom realization.
This is the existing divisorProEtale construction on the uniquely normalized family.
Source: lem-pur-divisor-class, general construction (blueprint: lem-pur-divisor-class).
-/
def generalDivisorClass (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : P.FunctorialCupH true i 2 1 :=
  P.divisorProEtale i ((P.generalDivisorEtaleClasses T a).homClassOf i hI)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DivisorChern DivisorLocalEquations DivisorAdditive


private theorem divisor_chern (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (hC : P.DivisorEtaleNormalized T a C)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    P.DivisorChern a C i hI := by
  unfold DivisorChern divisorProEtale
  exact P.normalizedCartier_forget a i hI (C.classOf i hI)
    (C.homClassOf i hI) (C.realizes i hI) (hC i hI)

/-- The canonical divisor class, its local equation, addition, and ordinary Chern class.

The existential family is uniquely fixed by the relative normalization. Its pro-etale
image is divisorProEtale, not an unspecified class or comparison. The Cartier condition
on the smooth divisor is a conclusion. The local neighbourhood is arbitrary etale,
without a quasi-compactness or open-immersion restriction. For addition, s has the
product Cartier ideal; a1 and a2 are its uniquely determined closed-support inclusions.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-divisor-class, clauses (a), (b), and final paragraph
(blueprint: lem-pur-divisor-class).

Proof: take the existing unique normalized family for every Cartier immersion.
The smooth codimension-one Cartier theorem supplies the required invertible ideal.
Apply normalizedCartier_localEquation to its representative and realization witness.
For the addition clause, invertibility of the product ideal supplies hsum, and the
closed-immersion lifting property supplies both support inclusions from the ideal
inequalities. Apply normalizedCartier_sum to the three normalized representatives.
For the Chern clause, normalizedCartier_forget gives the ordinary Ext representative,
its Hom identity and its ordinary Chern normalization. The forget_support clause
of supportedCupFunctoriality commutes forgetting support with site comparison.
These are global class comparisons, not an argument from equality on a cover. -/
theorem divisor_class (P : PurityFiniteSetting.{u}) {B T D : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) [IsSeparated b] [LocallyOfFiniteType b]
    [QuasiCompact b] (v : T ⟶ B) (d : ℕ) [SmoothOfRelativeDimension d v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ T) [IsClosedImmersion i] [Smooth (i ≫ v)]
    (hcodim : ∀ z : D, ringKrullDim (T.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞)) :
    ∃ C : P.DivisorEtaleClasses T,
      P.DivisorEtaleNormalized T (v ≫ b) C ∧
      (∀ C' : P.DivisorEtaleClasses T,
        P.DivisorEtaleNormalized T (v ≫ b) C' → C' = C) ∧
      ∃ hI : i.ker.IsInvertible,
        P.DivisorLocalEquations (v ≫ b) C i hI ∧
        P.DivisorAdditive T C ∧ P.DivisorChern (v ≫ b) C i hI := by
  obtain ⟨C, hC, huniq⟩ := P.existsUnique_generalDivisorEtaleClasses T (v ≫ b)
  let : Smooth v := SmoothOfRelativeDimension.smooth d v
  have hgeom := Scheme.Hom.exists_regular_equation_and_isEffectiveCartierCenter_of_smooth
    P.field.k b (v ≫ b) (i ≫ v ≫ b) v i hcodim
  have hI : i.ker.IsInvertible :=
    isEffectiveCartierCenter_iff_isInvertible_ker.mp hgeom.2
  refine ⟨C, hC, huniq, hI, ?_, ?_, divisor_chern P (v ≫ b) C hC i hI⟩
  · unfold DivisorLocalEquations
    intro U e inst f t sq
    unfold divisorProEtale
    exact P.normalizedCartier_localEquation (v ≫ b) i hI
      (C.classOf i hI) (C.homClassOf i hI) (C.realizes i hI) (hC i hI) U e f t sq
  · unfold DivisorAdditive
    intro D₁ D₂ Z i₁ i₂ s inst₁ inst₂ instZ h₁ h₂ hs
    have hsum : s.ker.IsInvertible := by
      rw [hs]
      exact h₁.mul_effectiveCartier h₂
    have hk₁ : s.ker ≤ i₁.ker := by
      rw [hs]
      intro U
      exact Ideal.mul_le_left
    have hk₂ : s.ker ≤ i₂.ker := by
      rw [hs]
      intro U
      exact Ideal.mul_le_right
    let a₁ := IsClosedImmersion.lift s i₁ hk₁
    let a₂ := IsClosedImmersion.lift s i₂ hk₂
    have ha₁ : a₁ ≫ s = i₁ := IsClosedImmersion.lift_fac s i₁ hk₁
    have ha₂ : a₂ ≫ s = i₂ := IsClosedImmersion.lift_fac s i₂ hk₂
    refine ⟨hsum, a₁, a₂, ha₁, ha₂, ?_⟩
    unfold divisorProEtale
    exact P.normalizedCartier_sum (v ≫ b) i₁ i₂ s h₁ h₂ hs hsum a₁ a₂ ha₁ ha₂
      (C.classOf i₁ h₁) (C.classOf i₂ h₂) (C.classOf s hsum)
      (C.homClassOf i₁ h₁) (C.homClassOf i₂ h₂) (C.homClassOf s hsum)
      (C.realizes i₁ h₁) (C.realizes i₂ h₂) (C.realizes s hsum)
      (hC i₁ h₁) (hC i₂ h₂) (hC s hsum)

end WeilConjectures.PurityFiniteSetting
