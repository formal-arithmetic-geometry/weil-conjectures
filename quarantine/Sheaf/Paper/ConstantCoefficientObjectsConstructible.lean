/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.RationalizationKaroubi
public import Sheaf.Paper.IntegralScalarExtension
public import Sheaf.Paper.AlgebraicallyClosedCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Constant coefficient objects are bounded constructible

Source: Weil blueprint, ordinary and compactly supported cohomology, order 1510;
Bhatt--Scholze, Sections 3.5, 6.5 and Definition 6.8.1, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
The finite and completed coefficient objects are the regular module sheaves in degree zero.
All positive levels are indexed by n : ℕ, denoting exponent n+1. Rationalization is raw,
and algebraically closed coefficients use the recorded small finite-field models.
-/

@[expose] public section
set_option autoImplicit false

universe d u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The finite constant ring sheaf, as its regular module in degree zero.
Source: blueprint order 1510; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def finiteConstantCoefficientObject (n : ℕ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

/-- The completed coefficient ring, as its regular module in degree zero.
Source: Bhatt--Scholze, Definition 6.8.1, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def integralConstantCoefficientObject :
    DerivedCategory (scalarReductionSource l E Y) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- The completed-ring projection as a linear map into the restricted quotient module.
The image of 1 is the compatible section 1, so its sectionwise formula is precisely π_n.
Source: Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def constantCoefficientProjection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (scalarReductionRestriction l E Y n).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E Y n).obj.obj U))
      (fun {_ _} f ↦ map_one ((integralCoefficientSheaf l E Y n).obj.map f).hom))

/-- The canonical derived reduction map: transpose the actual coefficient projection
through the normalized derived tensor/restriction adjunction. Exact restriction commutes
with placing a sheaf in degree zero via Mathlib's specified single-functor comparison.
Source: Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def constantCoefficientReductionMap (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        (integralConstantCoefficientObject l E Y) ⟶ finiteConstantCoefficientObject l E Y n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map (constantCoefficientProjection l E Y n) ≫
      ((scalarReductionRestriction l E Y n).mapDerivedCategorySingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)))

/-- Part 1: the finite constant object is bounded constructible, and its underlying
sheaf is locally constant on Y itself, with finite stalks isomorphic to A_{E,n+1}.
Source: blueprint order 1510; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the integer ring is a DVR with finite residue field, so all its positive-power
quotients are finite (lem-weil-valued-dvr-finite-quotients). Use the single stratum Y,
with identity immersion; Y is locally closed and constructible in itself. The identity
cover trivializes the constant regular module. The constant germ calculation
(lem-weil-proetale-constant-sheaf-stalk) identifies each geometric stalk with the
coefficient ring, hence makes it finite. A single complex has this constructible sheaf
as H^0 and zero cohomology in every other degree. This is exactly the finite-torsion
constructibility condition. The empty scheme has no geometric points and is allowed. -/
theorem finiteConstantCoefficient_constructible (n : ℕ) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y
        (finiteConstantCoefficientObject l E Y n) ∧
      IsLocallyConstantProEtaleModuleSheaf Y (Padic.coefficientExtensionRing l E (n + 1))
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : AlgebraicGeometry.Spec (.of Ω) ⟶ Y),
        (∃ e : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) ≃+
            proEtaleGeometricModuleStalk y
              (integralCoefficientCommRingSheaf l E Y n)
              (SheafOfModules.unit (integralCoefficientSheaf l E Y n)),
          ∀ a b : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
            e (a * b) = proEtaleConstantRingGerm y
              (Padic.coefficientExtensionRing l E (n + 1)) a • e b) ∧
        Finite (proEtaleGeometricModuleStalk y
          (integralCoefficientCommRingSheaf l E Y n)
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))) := by
  sorry

/-- Part 2, with the same integral membership in both recorded presentations.
Source: blueprint order 1510; Bhatt--Scholze, Definition 3.5.2, Section 6.5,
Definition 6.8.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the regular module in degree zero is K-flat, since tensoring with it is the
identity on complexes. Compute each reduction by this representative: multiplication
R_n tensor_R R → R_n is the unit isomorphism and is the transpose of π_n. Thus the
specified reduction map is invertible. Its target is the finite constant object of
Part 1; all reductions have cohomology supported in [0,0]. Their transition maps are
the quotient reductions and are surjective: locally lift a constant quotient section
from the integer ring. Restriction of scalars leaves the underlying sheaf unchanged.
Their ordinary inverse limit is the completed coefficient sheaf by its construction.
Apply lem-weil-proetale-surjective-tower-derived-limit to obtain its Roos triangle
with the actual projections. These are exactly the canonical reduction units, so
both recorded completeness predicates hold. Together with Part 1 and the common
interval [0,0], this proves membership in both recorded integral full subcategories.
This does not assert uniqueness of an arbitrary lift to a triangulated homotopy limit. -/
theorem integralConstantCoefficient_constructible
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    boundedConstructibleDerivedCompleteIntegral D l hl E Y
        (integralConstantCoefficientObject l E Y) ∧
      sfIntegralConstructible l E Y (integralConstantCoefficientObject l E Y) ∧
      IsDerivedCompleteUnrestricted l E Y (integralConstantCoefficientObject l E Y) ∧
      ∀ n : ℕ, IsIso (constantCoefficientReductionMap l E Y n) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E Y n).obj
            (integralConstantCoefficientObject l E Y)) ⊆ Set.Icc 0 0 := by
  sorry

/-- The actual integral coefficient object in the full constructible subcategory.
Only its membership proof is postponed; its underlying object is explicitly the
completed regular module in degree zero.
Source: blueprint order 1510; Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def constructibleIntegralConstantCoefficient
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y :=
  ⟨integralConstantCoefficientObject l E Y,
    (integralConstantCoefficient_constructible l E Y D hl).1⟩

/-- E_Y is the image of the specified integral coefficient object under raw
rationalization. No idempotent is adjoined.
Source: blueprint order 1510; Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def rationalConstantCoefficientObject
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) : rationalConstructibleCategory D l hl E Y :=
  (rationalConstructibleLocalization D l hl E Y).obj
    (constructibleIntegralConstantCoefficient l E Y D hl)

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Part 3, integral scalar extension of the coefficient object.
Source: blueprint order 1510; Bhatt--Scholze, Lemma 6.8.2(1)-(2)
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: use the K-flat regular module representative. Its scalar tower at level m is
canonically the constant A_{L,m+1} regular module, since multiplication identifies
the tensor with the target regular module. The transition maps are quotient maps.
They are surjective, and their ordinary inverse limit is the recorded completed
L-coefficient sheaf. The surjective-tower derived-limit theorem identifies the
specified Roos construction of integralScalarExtension with that completion in degree
zero, compatibly with every finite quotient projection. This also covers ι = id. -/
theorem integralConstantCoefficient_scalarExtension :
    Nonempty ((integralScalarExtension l E L ι Y).obj
      (integralConstantCoefficientObject l E Y) ≅ integralConstantCoefficientObject l L Y) := by
  sorry

/-- Rational scalar extension carries E_Y to L_Y.
Source: blueprint order 1510; Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the integral scalar-extension isomorphism is between objects of the full
constructible subcategory by Part 2. Lift it to that full subcategory, then apply
raw rationalization, which preserves isomorphisms. The specified object formula for
rationalScalarExtension identifies its source with the scalar extension of E_Y. -/
theorem rationalConstantCoefficient_scalarExtension
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    Nonempty ((rationalScalarExtension D l hl E Y L ι).obj
      (rationalConstantCoefficientObject l E Y D hl) ≅
        rationalConstantCoefficientObject l L Y D hl) := by
  sorry

namespace AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The algebraically closed coefficient object is the literal pair (E,E_Y), using
exactly the small field model of the recorded common-stage category.
Source: blueprint order 1510; Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def constantCoefficientPair (E : Index l Ω) : Pair D l hl Ω Y :=
  ⟨E, rationalConstantCoefficientObject l (Coefficient.{u} l Ω E) Y D hl⟩

/-- The class of the scalar-extension isomorphism at the common stage L is invertible.
The associator and the self-transition supply exactly the identity-stage normalization
needed to represent a map between the literal pairs at stage L.
Source: blueprint order 1510; Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: rational scalar extension identifies the coefficient objects by the preceding
part. The defining equality for stageSystem identifies its transition with that same
rational scalar functor, giving φ. Represent φ at L, correcting the target self-extension
by the canonical associator. The inverse is represented at L by the inverse corrected
map. Composition of representatives is composition at a common stage; both composites
are identities and remain identities after every further extension. Hence its class
is an isomorphism. Repeated stages and identity inclusions are included. -/
theorem constantCoefficientPair_stageIndependent (E L : Index l Ω) (h : E ≤ L) :
    ∃ φ : (stageTransition D l hl Ω Y E L h).obj
        (rationalConstantCoefficientObject l (Coefficient.{u} l Ω E) Y D hl) ≅
          rationalConstantCoefficientObject l (Coefficient.{u} l Ω L) Y D hl,
      IsIso (ofHom (constantCoefficientPair D l hl Ω Y E)
        (constantCoefficientPair D l hl Ω Y L) L h le_rfl
        (((stageSystem D l hl Ω Y).assoc h le_rfl).inv.app
            (rationalConstantCoefficientObject l (Coefficient.{u} l Ω E) Y D hl) ≫
          (stageTransition D l hl Ω Y L L le_rfl).map φ.hom)) := by
  sorry

end AlgebraicallyClosedCoefficients
end WeilConjectures
