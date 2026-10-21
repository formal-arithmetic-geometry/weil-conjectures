/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Normalized tensor presentation of completed coefficient rings

Source: main-20261015, smooth-purity, Cartesian coefficients and twists,
integral twist paragraph; Stacks 03EK and 03EL
(blueprint: lem-pur-completed-coefficient-tensor-normalization).

The pushout in commutative ring sheaves is the sheafified balanced ring tensor.
Its two inclusions express a pure tensor as the product of their images.
All maps in the conclusion are fixed by quotient projections or by these inclusions.
Site and coefficient universes are independent; level n always means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientNormalization

/-- The existing ring-sheaf category, retaining commutativity for its pushouts.
Source: Stacks 03EK (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev Rings (T : Scheme.{t}) := Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}

/-- A ring homomorphism transported through the common coefficient lift.
Source: Stacks 0H7J (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def liftHom {A : Type u} {B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{t + 1} A →+* ULift.{t + 1} B :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

/-- Constant integral scalars for the base field, with their discrete meaning.
Source: Stacks 0H7J (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev discrete (l : ℕ) [Fact l.Prime] (T : Scheme.{t}) : Rings.{t, u} T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l)))

/-- The actual constant finite base quotient, starting at exponent one.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev baseLevel (l : ℕ) (T : Scheme.{t}) (n : ℕ) : Rings.{t, u} T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))))

/-- Reduction in the base quotient tower, followed by constant sheafification.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def baseTransition (l : ℕ) (T : Scheme.{t}) (n : ℕ) :
    baseLevel.{t, u} l T (n + 1) ⟶ baseLevel.{t, u} l T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom)))

/-- The base inverse sequence, using the existing sequence construction.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def baseTower (l : ℕ) (T : Scheme.{t}) : ℕᵒᵖ ⥤ Rings.{t, u} T :=
  Functor.ofOpSequence (baseTransition l T)

/-- A_T is the existing categorical inverse limit, not the discrete constant ring.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev baseCompletion (l : ℕ) (T : Scheme.{t}) : Rings.{t, u} T :=
  limit (baseTower l T)

/-- The base projections are the coordinate maps of that limit.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev baseProjection (l : ℕ) (T : Scheme.{t}) (n : ℕ) :=
  limit.π (baseTower.{t, u} l T) (op n)

/-- Constant sheafification of the actual l-adic residue homomorphism.
Source: PadicInt.toZModPow (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def baseResidue (l : ℕ) [Fact l.Prime] (T : Scheme.{t}) (n : ℕ) :
    discrete.{t, u} l T ⟶ baseLevel l T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (p := l) (n + 1)).comp ULift.ringEquiv.toRingHom)))

/-- The existing pointwise Kan extension, using colimits only in the actual
site indexing sizes. This is a size specialization of Mathlib's construction.
Source: Stacks 00VC (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev kan {T' T : Scheme.{t}} (h : T' ⟶ T)
    (P : T.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) :
    (proEtaleBaseChange h).op.HasLeftKanExtension P :=
  letI : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  letI : (proEtaleBaseChange h).op.HasPointwiseLeftKanExtension P :=
    fun _ ↦ HasColimitsOfShape.has_colimit _
  Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (proEtaleBaseChange h).op P)

/-- The same left-Kan-extension/sheafification inverse image as the recorded
pro-etale inverse image, at the common coefficient universe.
Source: Stacks 00VC, 00YV (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev inverse {T' T : Scheme.{t}} (h : T' ⟶ T) : Rings.{t, u} T ⥤ Rings.{t, u} T' :=
  letI := kan.{t, u} h
  Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange h)
    CommRingCat.{max u (t + 1)} (ProEt.topology T) (ProEt.topology T')

/-- The constant comparison is the adjoint of the map preserving constant sections.
It uses exactly the construction of proEtaleConstantInverseImageMap, at general size.
Source: Stacks 0H7J (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def delta {T' T : Scheme.{t}} (h : T' ⟶ T) (C : CommRingCat.{max u (t + 1)}) :
    (inverse.{t, u} h).obj ((constantSheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}).obj C) ⟶
      (constantSheaf (ProEt.topology T') CommRingCat.{max u (t + 1)}).obj C :=
  letI : HasColimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, u, u} _
  letI := kan.{t, u} h
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (proEtaleBaseChange h)
    CommRingCat.{max u (t + 1)} (ProEt.topology T) (ProEt.topology T')).homEquiv _ _).symm
      (((sheafificationAdjunction (ProEt.topology T) CommRingCat.{max u (t + 1)}).homEquiv _ _).symm
        (Functor.whiskerLeft (proEtaleBaseChange h).op
          (toSheafify (ProEt.topology T') ((Functor.const T'.ProEtᵒᵖ).obj C))))

variable (l : ℕ) [Fact l.Prime]

/-- Epsilon is specified by every residue, hence uniquely by the limit property.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure BaseData where
  epsilon : ∀ T : Scheme.{t}, discrete.{t, u} l T ⟶ baseCompletion l T
  residue : ∀ (T : Scheme.{t}) (n : ℕ),
    epsilon T ≫ baseProjection l T n = baseResidue l T n

variable (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]

/-- The existing discrete coefficient sheaf, with commutativity retained.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev integralDiscrete (T : Scheme.{t}) : Rings.{t, u} T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H)))

/-- Constant sheafification of the actual integral residue, retaining commutativity.
This is integralConstantQuotientOfUniverses before forgetting commutativity.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def integralResidue (T : Scheme.{t}) (n : ℕ) :
    integralDiscrete l H T ⟶ integralCoefficientCommRingSheaf l H T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1))).comp
        ULift.ringEquiv.toRingHom)))

/-- The constant scalar inclusion attached to a specified integral restriction.
The accompanying theorem fixes that restriction by the inclusion into H.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def scalar (f : PadicInt l →+* Padic.coefficientExtensionIntegers l H) (T : Scheme.{t}) :
    discrete.{t, u} l T ⟶ integralDiscrete l H T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)))

/-- The ring-sheaf tensor: the pushout of the two specified scalar maps.
CommRingCat pushouts are balanced ring tensors, and sheaf colimits are their
sheafifications; its pure tensors are products of the images of the two inclusions.
Source: Stacks 03EK (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev tensor (d : BaseData.{t, u} l)
    (f : PadicInt l →+* Padic.coefficientExtensionIntegers l H) (T : Scheme.{t}) :=
  pushout (d.epsilon T) (scalar l H f T)

/-- The constant map from an admissible base quotient to an integral quotient.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def residueFromBase (T : Scheme.{t}) (n k : ℕ)
    (j : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l H (n + 1)) :
    baseLevel.{t, u} l T k ⟶ integralCoefficientCommRingSheaf l H T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (j.comp ULift.ringEquiv.toRingHom)))

/-- The coefficient tensor presentation with its full quotient normalization.
The formula quantifies over every admissible k, so also asserts independence of k.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure Presentation (d : BaseData.{t, u} l) where
  integers : PadicInt l →+* Padic.coefficientExtensionIntegers l H
  integers_spec : ∀ a : PadicInt l, (integers a : H) = algebraMap (Padic l) H (a : Padic l)
  beta : ∀ T : Scheme.{t}, tensor l H d integers T ≅
    completedIntegralCommRingSheafUnrestricted l H T
  projection : ∀ (T : Scheme.{t}) (n k : ℕ),
    Ideal.span ({(l : Padic.coefficientExtensionIntegers l H) ^ (k + 1)} :
      Set (Padic.coefficientExtensionIntegers l H)) ≤
        Padic.coefficientExtensionIdeal l H (n + 1) →
    ∃ j : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l H (n + 1),
      (∀ a : PadicInt l, j (PadicInt.toZModPow (k + 1) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1)) (integers a)) ∧
      ∀ (U : T.ProEtᵒᵖ) (x : (baseCompletion.{t, u} l T).obj.obj U)
        (b : (integralDiscrete l H T).obj.obj U),
        (((beta T).hom ≫ completedIntegralCommRingProjectionUnrestricted l H T n).hom.app U)
          ((pushout.inl (d.epsilon T) (scalar l H integers T)).hom.app U x *
            (pushout.inr (d.epsilon T) (scalar l H integers T)).hom.app U b) =
          ((residueFromBase l H T n k j).hom.app U
            ((baseProjection l T k).hom.app U x)) * (integralResidue l H T n).hom.app U b

/-- Base inverse image, specified by all finite projections and the epsilon square.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure BasePullback (d : BaseData.{t, u} l) {T' T : Scheme.{t}} (h : T' ⟶ T) where
  alpha : (inverse.{t, u} h).obj (baseCompletion.{t, u} l T) ⟶ baseCompletion l T'
  projection : ∀ n : ℕ,
    alpha ≫ baseProjection l T' n = (inverse.{t, u} h).map (baseProjection l T n) ≫
      delta.{t, u} h (CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))))
  epsilon_square : (inverse.{t, u} h).map (d.epsilon T) ≫ alpha =
    delta.{t, u} h (CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l))) ≫ d.epsilon T'
  constant_iso : ∀ C : CommRingCat.{max u (t + 1)}, IsIso (delta.{t, u} h C)

/-- The actual tensor of the two inverse-image rings over the inverse-image base.
Source: Stacks 03EL (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev pulledTensor (d : BaseData.{t, u} l) (p : Presentation l H d)
    {T' T : Scheme.{t}} (h : T' ⟶ T) :=
  pushout ((inverse.{t, u} h).map (d.epsilon T))
    ((inverse.{t, u} h).map (scalar l H p.integers T))

/-- The inverse-image tensor comparison and all scalar structures, normalized on
both tensor inclusions. Multiplicativity then gives its pure-tensor normalization.
Source: Stacks 03EL and the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure Pullback (d : BaseData.{t, u} l) (p : Presentation l H d)
    {T' T : Scheme.{t}} (h : T' ⟶ T) (a : BasePullback l d h) where
  alpha : (inverse.{t, u} h).obj (completedIntegralCommRingSheafUnrestricted l H T) ⟶
    completedIntegralCommRingSheafUnrestricted l H T'
  projection : ∀ n : ℕ,
    alpha ≫ completedIntegralCommRingProjectionUnrestricted l H T' n =
      (inverse.{t, u} h).map (completedIntegralCommRingProjectionUnrestricted l H T n) ≫
        delta.{t, u} h (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l H (n + 1))))
  scalar_square : (inverse.{t, u} h).map (scalar l H p.integers T) ≫
      delta.{t, u} h (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H))) =
    delta.{t, u} h (CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l))) ≫
      scalar l H p.integers T'
  sigma : (inverse.{t, u} h).obj (tensor l H d p.integers T) ≅ pulledTensor l H d p h
  sigma_left : (inverse.{t, u} h).map (pushout.inl (d.epsilon T) (scalar l H p.integers T)) ≫
    sigma.hom = pushout.inl _ _
  sigma_right : (inverse.{t, u} h).map (pushout.inr (d.epsilon T) (scalar l H p.integers T)) ≫
    sigma.hom = pushout.inr _ _
  change : pulledTensor l H d p h ⟶ tensor l H d p.integers T'
  change_left : pushout.inl _ _ ≫ change = a.alpha ≫
    pushout.inl (d.epsilon T') (scalar l H p.integers T')
  change_right : pushout.inr _ _ ≫ change =
    delta.{t, u} h
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H))) ≫
      pushout.inr (d.epsilon T') (scalar l H p.integers T')
  beta_square : (inverse.{t, u} h).map (p.beta T).hom ≫ alpha =
    sigma.hom ≫ change ≫ (p.beta T').hom

variable (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]

/-- The discrete coefficient inclusion is constant sheafification of its restriction.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def constantInclusion (f : Padic.coefficientExtensionIntegers l H →+*
    Padic.coefficientExtensionIntegers l F) (T : Scheme.{t}) :
    integralDiscrete l H T ⟶ integralDiscrete l F T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom (liftHom f))

/-- Every admissible ramified quotient map is the quotient of the actual inclusion.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def quotientInclusion (f : Padic.coefficientExtensionIntegers l H →+*
    Padic.coefficientExtensionIntegers l F) (T : Scheme.{t}) (k n : ℕ)
    (hk : Padic.coefficientExtensionIdeal l H (k + 1) ≤
      (Padic.coefficientExtensionIdeal l F (n + 1)).comap f) :
    integralCoefficientCommRingSheaf l H T k ⟶ integralCoefficientCommRingSheaf l F T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (liftHom (Ideal.quotientMap (Padic.coefficientExtensionIdeal l F (n + 1)) f hk)))

/-- The coefficient-field compatibility, including the full ramified projection
formula defining i_EF and the two factor equations defining 1 tensor q_EF.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure Extension (iota : H →ₐ[Padic l] F) (d : BaseData.{t, u} l)
    (p : Presentation l H d) (q : Presentation l F d) where
  integers : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F
  integers_spec : ∀ x, (integers x : F) = iota (x : H)
  admissible : ∀ n : ℕ, ∃ k : ℕ, Padic.coefficientExtensionIdeal l H (k + 1) ≤
    (Padic.coefficientExtensionIdeal l F (n + 1)).comap integers
  inclusion : ∀ T : Scheme.{t}, completedIntegralCommRingSheafUnrestricted l H T ⟶
    completedIntegralCommRingSheafUnrestricted l F T
  projection : ∀ (T : Scheme.{t}) (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l H (k + 1) ≤
      (Padic.coefficientExtensionIdeal l F (n + 1)).comap integers),
    inclusion T ≫ completedIntegralCommRingProjectionUnrestricted l F T n =
      completedIntegralCommRingProjectionUnrestricted l H T k ≫
        quotientInclusion l H F integers T k n hk
  tensorMap : ∀ T : Scheme.{t}, tensor l H d p.integers T ⟶ tensor l F d q.integers T
  tensor_left : ∀ T : Scheme.{t},
    pushout.inl (d.epsilon T) (scalar l H p.integers T) ≫ tensorMap T =
      pushout.inl (d.epsilon T) (scalar l F q.integers T)
  tensor_right : ∀ T : Scheme.{t},
    pushout.inr (d.epsilon T) (scalar l H p.integers T) ≫ tensorMap T =
      constantInclusion l H F integers T ≫ pushout.inr (d.epsilon T) (scalar l F q.integers T)
  beta_square : ∀ T : Scheme.{t}, (p.beta T).hom ≫ inclusion T =
    tensorMap T ≫ (q.beta T).hom

/-- The normalized completed coefficient tensor isomorphisms exist and commute
with arbitrary scheme inverse image and finite extensions of coefficient fields.
There is no characteristic, finite-field, dimension, or invertibility restriction.

Source: main-20261015, smooth-purity, Cartesian coefficients and twists,
integral twist paragraph (blueprint: lem-pur-completed-coefficient-tensor-normalization).

Proof (the ten steps of the node):
1. Use lem-sfb-local-field-integral-basis over Q_l and
   lem-pur-local-field-coefficient-stages to choose an integral basis and write
   l = u varpi^e; the l-power and uniformizer-power filtrations are cofinal.
2. Sheafify the basis coordinate maps and their finite reductions. Finite-product
   preservation of sheafification makes these inverse constant-module isomorphisms.
3. In compatible tuples, pass to the cofinal indices er. The coordinate maps give
   A_T^d isomorphic to R_H,T, sectionwise and compatibly with restrictions.
4. The balanced tensor universal property identifies A_T tensor B_H,T with A_T^d.
   The composite gives beta and its projection formula for every admissible k.
5. Compute products and units under all quotient projections. Thus beta and its
   inverse are ring maps. The projection formula uniquely determines beta.
6. Constant comparisons are the adjoints of constant-section maps. Sheafification
   uniqueness shows their naturality for all residue and inclusion ring maps.
7. Define alpha_0 and alpha_H by their quotient cones. Naturality from step 6
   proves the epsilon square after each base projection.
8. Inverse image of the universal balanced pairing induces the tensor comparison.
   The finite basis proves invertibility. Its two inclusion equations fix sigma;
   the epsilon and scalar squares define the displayed change-of-scalars map.
9. Project the beta inverse-image square to n and use an admissible k. Step 6
   identifies the pulled-back residue pairing with the pairing over T'. Joint
   detection by projections gives equality of the ring-sheaf maps.
10. Define the coefficient inclusion by all admissible ramified quotient maps;
    compare two choices after a common larger index. The beta extension square
    follows on pure tensors. Project the inverse-image inclusion square and use
    step 6 for each quotient map. Naturality also gives the discrete q square. -/
theorem completed_coefficient_tensor_normalization (iota : H →ₐ[Padic l] F) :
    ∃ (d : BaseData.{t, u} l) (p : Presentation l H d) (q : Presentation l F d)
      (e : Extension l H F iota d p q),
      ∀ (T' T : Scheme.{t}) (h : T' ⟶ T),
        ∃ (a : BasePullback l d h) (b : Pullback l H d p h a) (c : Pullback l F d q h a),
          (inverse.{t, u} h).map (e.inclusion T) ≫ c.alpha = b.alpha ≫ e.inclusion T' ∧
          (inverse.{t, u} h).map (constantInclusion l H F e.integers T) ≫
              delta.{t, u} h
                (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l F))) =
            delta.{t, u} h
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H))) ≫
              constantInclusion l H F e.integers T' := by
  sorry

end WeilConjectures.CompletedCoefficientNormalization
