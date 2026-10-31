/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Intrinsic scalar normalization formulas

Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact derived scalar
composition; `SfScalarExtensionComposition.lean`, intrinsic normalization, and
`GeneralAlgebraicallyClosedCoefficientStages.lean`, normalized shifts and associators
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).

The coefficient models and all three comparisons are the published constructions.
`integralOrdinaryDerivedScalar` is the exact termwise induced functor, and
`integralOrdinaryDerivedScalarComp` is the inverse exact-derived composition comparison
followed by the derived image of `integralOrdinaryScalarComp`. The latter's section
normalization is stated below. The integral compositor b is written inline as
`sfIntegralScalarComp` followed by `eqToIso` of the coefficient-inclusion composition law
(the construction `SfStrictDirectImageScalar.integralAssociator` names; it is not
redefined here). Heterogeneous equalities retain the actual coefficient composition
transport, including repeated indices. No idempotent completion is used.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
set_option Elab.async false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  integralScalarExtension integralOrdinaryScalar integralCompletedScalarMap
  sfIntegralOrdinaryComparison integralOrdinaryDerivedScalarComp


open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- Ordinary coefficient extension is additive and exact on all module sheaves.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact scalar extension
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).
Proof: the completed coefficient map commutes with every finite quotient projection.
`lem-weil-completed-integral-finite-free` identifies its target, after restriction,
with a finite power of the source. Sheaf tensor (`def-pur-sheaf-tensor-product`)
therefore becomes a finite direct sum after restriction. Finite direct sums preserve
kernels and cokernels, proving additivity and exactness. The exact-derived factorization
`lem-weil-pbc-exact-functor-derived-factorization` then applies termwise without a
boundedness condition or a resolution. -/
theorem intrinsicOrdinaryScalar_exact (E L : Index l Ω) (h : E ≤ L) :
    (integralOrdinaryScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y).Additive ∧
    PreservesFiniteLimits
      (integralOrdinaryScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) Y) ∧
    PreservesFiniteColimits
      (integralOrdinaryScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) Y) := by
  exact ⟨inferInstance, WeilConjectures.integralOrdinaryScalar_exact l
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y⟩

/-- The ordinary associator is balanced multiplication on every local tensor generator.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, tensor composition
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).
Proof: send c tensor (b tensor x) to c*j(b) tensor x and send c tensor x back to
c tensor (1 tensor x). The balancing relation proves the inverse equations. These
formulas commute with restrictions and module maps; sheafification gives inverse natural
maps (`def-pur-sheaf-tensor-product`). Apply them termwise and localize. The uniqueness
clause of `lem-weil-pbc-localization-universal-property` identifies the derived map with
the inverse exact-derived composition comparison followed by this derived multiplication
(`lem-weil-pbc-exact-functor-derived-factorization`). -/
theorem intrinsicOrdinaryScalarComp_tensor
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (N : integralTowerModules.{u, u} l (Coefficient.{u} l Ω E) Y) (V : Y.ProEtᵒᵖ)
    (c : (completedIntegralCommRingSheafUnrestricted l (Coefficient.{u} l Ω M) Y).obj.obj V)
    (b : (completedIntegralCommRingSheafUnrestricted l (Coefficient.{u} l Ω L) Y).obj.obj V)
    (x : N.val.obj V) :
    ((integralOrdinaryScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k)).hom.app N).val.app V
        (integralOrdinaryTensorSection l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k) Y _ V c
          (integralOrdinaryTensorSection l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y N V b x)) =
      integralOrdinaryTensorSection l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M)
        ((coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h)) Y N V
        (c * (integralCompletedScalarMap l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k) Y).hom.app V b) x := by
  exact (integralOrdinaryScalarComp_existsUnique l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k)).exists.choose_spec N V c b x

private theorem index_integral_transport
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (κ : Coefficient.{u} l Ω E →ₐ[Padic l] Coefficient.{u} l Ω M)
    (e : (coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h) = κ)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      ((sfIntegralConstructible l (Coefficient.{u} l Ω M) Y).ι.map
        ((sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
          eqToIso (congrArg
            (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω M) i Y)
            e)).hom.app K))
      ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k) Y).inv.app
            ((integralTransition l Ω Y E L h).obj K) ≫
        (integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k) Y).map
            ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
              (coefficientInclusion l Ω E L h) Y).inv.app K) ≫
        (integralOrdinaryDerivedScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k)).hom.app K.obj ≫
        (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M)
          ((coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h)) Y).hom.app
            K) := by
  subst κ
  simp only [eqToIso_refl, Iso.trans_refl, ObjectProperty.ι_map]
  exact heq_of_eq ((sfIntegralScalarComp_existsUnique l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k)).exists.choose_spec K)

/-- The ambient image of the actual integral compositor is the normalized ordinary word.
The right side uses the composed coefficient homomorphism; HEq includes its endpoint cast.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, intrinsic composition
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).
Proof: retain the specified ordinary-to-completed comparisons. Compose their inverses,
ordinary extension of the first inverse, ordinary derived associativity, and the final
comparison. By `lem-sfb-fully-faithful-cancel-iso-components`, the compositor lifted
through the full intrinsic inclusion has exactly this image. Faithfulness makes the
component unique. Finally eliminate the coefficient-inclusion composition equality
(`lem-route-coefficient-inclusion-laws`); its reflexive case has identity transports.
This includes repeated indices and the zero object without a hypothesis on Y. -/
theorem intrinsicIntegralScalarAssociator_image
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      ((sfIntegralConstructible l (Coefficient.{u} l Ω M) Y).ι.map
        ((sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
          eqToIso (congrArg
            (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω M) i Y)
            ((coefficientInclusion_laws l Ω).2 E L M h k))).hom.app K))
      ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k) Y).inv.app
            ((integralTransition l Ω Y E L h).obj K) ≫
        (integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k) Y).map
            ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
              (coefficientInclusion l Ω E L h) Y).inv.app K) ≫
        (integralOrdinaryDerivedScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k)).hom.app K.obj ≫
        (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M)
          ((coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h)) Y).hom.app
            K) := by
  exact index_integral_transport l Ω Y E L M h k
    (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k) K

/-- The prescribed integral shift has its ordinary-to-completed normalized ambient image.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, intrinsic shift normalization
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).
Proof: apply `lem-pur-fully-faithful-composite-shift` to the integral transition, target
inclusion, ordinary derived extension after source inclusion, and the inverse comparison.
The inclusion shift is the inherited beta (`lem-weil-integral-constructible-triangulated`)
and the composite ordinary comparison is h. The generic formula specifies exactly the
chosen `integralTransitionCommShift`. Compose with beta. Faithfulness proves uniqueness
of these components. All integer shifts, including zero and negative integers, are covered. -/
theorem intrinsicIntegralTransition_shift
    (E L : Index l Ω) (h : E ≤ L) (n : ℤ)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      ((sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.map
          (((integralTransition l Ω Y E L h).commShiftIso n).hom.app K) ≫
        ((sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.commShiftIso n).hom.app
          ((integralTransition l Ω Y E L h).obj K))
      ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) Y).inv.app
            ((shiftFunctor (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) n).obj
              K) ≫
        (Functor.commShiftIso
          ((sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
            integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
              (coefficientInclusion l Ω E L h) Y) n).hom.app K ≫
        (shiftFunctor
          (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω L) Y)) n).map
          ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y).hom.app K)) := by
  exact (integralScalarCommShift_existsUnique l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).exists.choose_spec n K

private theorem index_rational_transport
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (κ : Coefficient.{u} l Ω E →ₐ[Padic l] Coefficient.{u} l Ω M)
    (e : (coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h) = κ)
    (a : transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
      sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M) κ)
    (ha : HEq a (scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
      (coefficientInclusion l Ω L M k) κ e Y))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      (a.hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω M) Y).map
        ((sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
          eqToIso (congrArg
            (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω M) i Y)
            e)).hom.app K)) := by
  obtain rfl := eq_of_heq ha
  subst κ
  simpa only [scalarAssociator, eqToIso_refl, Iso.trans_refl, sfRationalScalarComp,
    sfRationalConstructibleLocalization, ScalarLocalization.localization] using
    (sfRationalScalarComp_existsUnique l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k)).exists.choose_spec
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K)

/-- The actual rational associator is the rationalization image of the integral one.
HEq retains the specified endpoint equalities of the rational scalar functors.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, rational scalar composition
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).
Proof: rationalization has unchanged objects. Localize the integral compositor and its
inverse componentwise. On a pure tensor arrow, naturality is integral naturality tensored
with the image of the coefficient. Bilinearity extends this to every arrow
(`def-weil-linear-scalar-localization`, `def-weil-rationalization-karoubi`). Localization
preserves the inverse equations. Every rational object is an integral representative,
so this component prescription uniquely determines `sfRationalScalarComp`. The stage
associator follows it by the coefficient-inclusion equality, hence has the stated image
(`lem-general-algebraically-closed-coefficient-stages`). Equality elimination applies
the same endpoint transport on both sides. Repeated indices need no strict identity
of tensor functors, and primality alone supplies the proof parameter l ≠ 0. -/
theorem intrinsicRationalScalarAssociator_image
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      ((associator l Ω Y E L M h k).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω M) Y).map
        ((sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
          eqToIso (congrArg
            (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω M) i Y)
            ((coefficientInclusion_laws l Ω).2 E L M h k))).hom.app K)) := by
  exact index_rational_transport l Ω Y E L M h k
    (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k) (associator l Ω Y E L M h k)
    ((associator_existsUnique l Ω Y E L M h k).exists.choose_spec) K

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures
