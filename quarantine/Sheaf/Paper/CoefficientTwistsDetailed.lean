/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24, Q25
-/
module

public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralConstructibleLinear
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Paper.RationalizationKaroubi
public import Sheaf.Paper.AlgebraicallyClosedCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Coefficient Tate twists

Source: blueprint `sec-smooth-purity/sk-def-sf-admissible/def-coefficient-twists-detailed.md`,
order 1505; current main-20261015 source: `sec-proetale-coefficients/sk-def-sp-tate-twist/`,
order 1864 (blueprint: def-coefficient-twists-detailed).

## Main definitions and statements

- `WeilConjectures.coefficientTateTwists`
- `WeilConjectures.coefficientTwistPower`
- `WeilConjectures.coefficientTwistLine`
- `WeilConjectures.coefficientTwistLine_exact`
- `WeilConjectures.IsCanonicalTwistScalarMaps`
- `WeilConjectures.twistSheafScalarComparison`
- `WeilConjectures.rationalTwistScalarComparison`
- `WeilConjectures.rationalComplexTwistFunctor`
- `WeilConjectures.algebraicClosureComplexTwistFunctor`

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d u v
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (X : Scheme.{u})

/-- Tensor powers of the coefficient line, with the unit at exponent zero.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientTwistPower {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℕ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | 0 => SheafOfModules.unit.{u, u + 1, u + 1} _
  | 1 => L
  | n + 2 => (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L).obj
      (coefficientTwistPower L (n + 1))

/-- Positive powers and internal duals of the coefficient line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientTwistLine {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℤ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | Int.ofNat n => coefficientTwistPower X L n
  | Int.negSucc n => SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
      (coefficientTwistPower X L (n + 1)) (SheafOfModules.unit.{u, u + 1, u + 1} _)

/-- Tensor with an integer power or dual of a rank-one line is exact and additive.
Source: blueprint order 1505; Stacks Tags 03EK and 03RV
(blueprint: def-coefficient-twists-detailed).
Proof: on a cover trivializing L, each positive tensor power is the unit module,
and internal Hom into the unit is also the unit. Thus tensor with every integer
power is locally the identity. Exactness can be checked locally; additivity follows
on sectionwise tensor generators and passes through sheafification. -/
theorem coefficientTwistLine_exact
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)).Additive ∧
    PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)) ∧
    PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)) := by
  sorry

variable (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E] (S : Scheme.{u})
  [∀ x : S, Invertible (ℓ : S.residueField x)]

/-- The published integral first line has rank one; reuse its recorded theorem.
Source: blueprint order 1505; Stacks 03PK
(blueprint: def-coefficient-twists-detailed). -/
instance coefficientTwistIntegralRank :
    (purTwistIntegralModule S ℓ E).IsFiniteLocallyFreeOfRank 1 :=
  (pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.1

/-- The published ordinary finite reduction has rank one.
Source: blueprint order 1505; Stacks 03PK
(blueprint: def-coefficient-twists-detailed). -/
instance coefficientTwistFiniteRank (n : ℕ) :
    (purTwistFiniteOne S ℓ E n).IsFiniteLocallyFreeOfRank 1 :=
  ((pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.2 n).2.1

/-- The finite coefficient twist at quotient exponent n+1.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev finiteCoefficientTwist (n : ℕ) (m : ℤ) :
    SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S n) :=
  coefficientTwistLine S (purTwistFiniteOne S ℓ E n) m

/-- Derived tensor by the finite twisting line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def finiteComplexTwist (n : ℕ) (m : ℤ) :
    proEtaleDerivedCategory S (Padic.coefficientExtensionRing ℓ E (n + 1)) ⥤
      proEtaleDerivedCategory S (Padic.coefficientExtensionRing ℓ E (n + 1)) := by
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).1
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).2.1
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).2.2
  exact (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (A := integralCoefficientCommRingSheaf ℓ E S n)
    (finiteCoefficientTwist ℓ E S n m)).mapDerivedCategory

/-- Tensor by the completed integral line on module sheaves.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def integralSheafTwist (m : ℤ) : integralTowerModules ℓ E S ⥤ integralTowerModules ℓ E S :=
  SheafOfModules.siteSheafTensorRight
    (A := completedIntegralCommRingSheafUnrestricted ℓ E S)
    (coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m)

/-- Additivity of tensor with the integral line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
instance integralSheafTwist_additive (m : ℤ) : (integralSheafTwist ℓ E S m).Additive :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).1

/-- Tensor with the integral line preserves finite limits.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
instance integralSheafTwist_finiteLimits (m : ℤ) :
    PreservesFiniteLimits (integralSheafTwist ℓ E S m) :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).2.1

/-- Tensor with the integral line preserves finite colimits.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
instance integralSheafTwist_finiteColimits (m : ℤ) :
    PreservesFiniteColimits (integralSheafTwist ℓ E S m) :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).2.2

/-- Derived tensor by the completed integral twisting line. Since the line is flat,
termwise tensor already computes derived tensor for every unbounded complex.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def integralComplexTwist (m : ℤ) :
    completedIntegralDerivedCategory ℓ E S D hℓ ⥤
      completedIntegralDerivedCategory ℓ E S D hℓ :=
  (integralSheafTwist ℓ E S m).mapDerivedCategory

/-- The canonical linear structure on the completed integral derived category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable instance completedIntegralLinear :
    Linear (Padic.coefficientExtensionIntegers ℓ E)
      (completedIntegralDerivedCategory ℓ E S D hℓ) := by
  exact integralCoefficientLinear ℓ E S

/-- The completed tensor twist is linear for the canonical coefficient action.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the coefficient action is the recorded constant-section action
integralCoefficientLinear. On local pure tensors, applying a coefficient to the
first factor before or after the tensor map gives the same balanced tensor.
Sheafification preserves this equality. The termwise identity descends through
the quasi-isomorphism localization, proving linearity on every derived arrow. -/
theorem integralComplexTwist_linear_statement (m : ℤ) :
    (integralComplexTwist D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) := by
  sorry

/-- The integral twist placed in degree zero.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def integralCoefficientTwist (m : ℤ) :
    completedIntegralDerivedCategory ℓ E S D hℓ :=
  (DerivedCategory.singleFunctor _ 0).obj
    (coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m)

/-- Every integral twist is bounded constructible and derived complete.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: trivialize on a primitive-root pro-etale cover. Powers and duals are again
rank-one lines, and their finite reductions are finite locally constant with common
support interval [0,0]. The compatible finite reductions recover the completed line,
so its canonical derived-completeness comparison is invertible. -/
theorem integralCoefficientTwist_constructible (m : ℤ) :
    boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S
      (integralCoefficientTwist D ℓ hℓ E S m) := by
  sorry

/-- The rational twist is the image in the raw scalar localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def rationalCoefficientTwist (m : ℤ) :
    rationalConstructibleCategory D ℓ hℓ E S :=
  (rationalConstructibleLocalization D ℓ hℓ E S).obj
    ⟨integralCoefficientTwist D ℓ hℓ E S m,
      integralCoefficientTwist_constructible D ℓ hℓ E S m⟩

/-- Tensor by an integral twisting line preserves the complete constructible category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: locally trivialize the rank-one twisting line. Tensor is then the identity
on the completed-coefficient category and its finite reductions. Derived completeness,
constructibility and the common bounded cohomological interval are local properties,
so the same properties hold after gluing. -/
theorem integralComplexTwist_constructible (m : ℤ)
    (K : boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S) :
    boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S
      ((integralComplexTwist D ℓ hℓ E S m).obj K.obj) := by
  sorry

/-- Rational twisting is integral tensor on the integral representative, then localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def rationalComplexTwist (m : ℤ) (K : rationalConstructibleCategory D ℓ hℓ E S) :
    rationalConstructibleCategory D ℓ hℓ E S :=
  (rationalConstructibleLocalization D ℓ hℓ E S).obj
    ⟨(integralComplexTwist D ℓ hℓ E S m).obj K.obj.obj,
      integralComplexTwist_constructible D ℓ hℓ E S m K.obj⟩

/-- The canonical endofunctor on the bounded integral constructible category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
The object map is the completed integral tensor functor restricted by its
constructibility theorem, and the arrow map is the same derived tensor map.
-/
noncomputable def integralConstructibleComplexTwistFunctor (m : ℤ) :
    boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S :=
  ObjectProperty.lift _
    ((boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S).ι ⋙
      integralComplexTwist D ℓ hℓ E S m)
    (fun K => integralComplexTwist_constructible D ℓ hℓ E S m K)

/-- The restricted integral twist is linear on the full constructible subcategory.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: integralComplexTwist_linear_statement gives the equality on all ambient
arrows. The full subcategory inherits that action by integralConstructibleLinear.
Its faithful inclusion gives the same equality for restricted arrows. -/
theorem integralConstructibleComplexTwistFunctor_linear_statement (m : ℤ) :
    (integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) := by
  sorry

/-- The restricted integral twist is additive on the full constructible subcategory.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: exact sheaf tensor is additive, and its derived functor retains additivity.
The full subcategory's arrow addition is ambient addition, so restriction
preserves the additive identity. -/
theorem integralConstructibleComplexTwistFunctor_additive_statement (m : ℤ) :
    (integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).Additive := by
  sorry

/-- The canonical rational Tate-twist endofunctor, obtained by extending the
integral tensor functor through the raw scalar localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def rationalComplexTwistFunctor (m : ℤ) :
    rationalConstructibleCategory D ℓ hℓ E S ⥤
      rationalConstructibleCategory D ℓ hℓ E S := by
  letI : Linear (Padic.coefficientExtensionIntegers ℓ E)
      (completedIntegralDerivedCategory ℓ E S D hℓ) :=
    completedIntegralLinear D ℓ hℓ E S
  letI : (integralComplexTwist D ℓ hℓ E S m).Additive := by
    dsimp [integralComplexTwist]
    infer_instance
  letI : (integralComplexTwist D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) :=
    integralComplexTwist_linear_statement D ℓ hℓ E S m
  let F := integralConstructibleComplexTwistFunctor D ℓ hℓ E S m
  letI : F.Additive := integralConstructibleComplexTwistFunctor_additive_statement D ℓ hℓ E S m
  letI : F.Linear (Padic.coefficientExtensionIntegers ℓ E) :=
    integralConstructibleComplexTwistFunctor_linear_statement D ℓ hℓ E S m
  exact CategoryTheory.ScalarLocalization.map
    (Padic.coefficientExtensionIntegers ℓ E)
    (boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S)
    (Padic.coefficientExtensionUniformizer ℓ E) F

/-- Its object map is the displayed integral-representative construction.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: ScalarLocalization.map applies the integral functor to the same integral
object. ObjectProperty.lift uses the displayed ambient tensor object and its
constructibility proof. Membership proofs agree by proof irrelevance. -/
theorem rationalComplexTwistFunctor_obj (m : ℤ)
    (K : rationalConstructibleCategory D ℓ hℓ E S) :
    (rationalComplexTwistFunctor D ℓ hℓ E S m).obj K =
      rationalComplexTwist D ℓ hℓ E S m K := by
  sorry

/-- The rational functor's action on every localized pure tensor.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: ScalarLocalization.map uses TensorProduct.map with the identity on the
localized scalar factor and the integral functor's linear Hom map. Evaluating
this map on a pure tensor gives the displayed formula. The endpoint casts
are the same object assignments, so the formula is recorded as HEq. -/
theorem rationalComplexTwistFunctor_map
    (m : ℤ)
    (K M : boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer ℓ E))
    (f : K ⟶ M) :
    HEq
      ((rationalComplexTwistFunctor D ℓ hℓ E S m).map
        (a ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E] f :
          (rationalConstructibleLocalization D ℓ hℓ E S).obj K ⟶
            (rationalConstructibleLocalization D ℓ hℓ E S).obj M))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E]
        (integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).map f :
        (rationalConstructibleLocalization D ℓ hℓ E S).obj
              ((integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).obj K) ⟶
          (rationalConstructibleLocalization D ℓ hℓ E S).obj
              ((integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).obj M)) := by
  sorry

/-- The coefficient line as a module sheaf, for every integer exponent.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev integralTwistLine (m : ℤ) : integralTowerModules ℓ E S :=
  coefficientTwistLine S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m

section ScalarComparison

variable (L : Type u) [Field L] [Algebra (Padic ℓ) L]
  [FiniteDimensional (Padic ℓ) L] (ι : E →ₐ[Padic ℓ] L)

/-- The constant integer inclusion induced by the specified coefficient embedding.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistConstantIntegerMap : purTwistIntegralConstant S ℓ E ⟶
    purTwistIntegralConstant S ℓ L :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((integralScalarIntegerInclusion ℓ E L ι).comp ULift.ringEquiv.toRingHom)))

/-- Semilinear maps from the E-lines to the L-lines, before scalar extension.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev TwistScalarMaps := ∀ m : ℤ,
  integralTwistLine ℓ E S m ⟶
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap ℓ E L ι S))).obj (integralTwistLine ℓ L S m)

/-- The roots-of-unity, unit, tensor-power and dual-evaluation normalization.
These equations specify maps, rather than merely coherent isomorphisms.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def IsCanonicalTwistScalarMaps (c : TwistScalarMaps ℓ E S L ι) : Prop :=
  (∀ (U : S.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted ℓ E S).obj.obj U),
    (c 0).val.app U a = (integralCompletedScalarMap ℓ E L ι S).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S ℓ E).obj.obj U)
      (x : (purTwistZlModule S ℓ).val.obj U),
    (c 1).val.app U (purTwistIntegralTensor S ℓ E U b x) =
      purTwistIntegralTensor S ℓ L U ((twistConstantIntegerMap ℓ E S L ι).hom.app U b) x) ∧
  (∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) (n + 1)).val.obj U)
      (y : (purTwistIntegralModule S ℓ E).val.obj U),
    (c (Int.ofNat (n + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul
          (A := completedIntegralCommRingSheafUnrestricted ℓ E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U
        ((c (Int.ofNat (n + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine ℓ E S (Int.negSucc n)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) (n + 1)).val.obj U),
    (((c (Int.negSucc n)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (n + 1))).val.app U x) =
      (integralCompletedScalarMap ℓ E L ι S).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

/-- There is exactly one normalized semilinear family on the signed Tate lines.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: at zero take the completed coefficient inclusion. At one send the root
limit tensor b to the same root limit tensor its integer image. The balanced
relations agree by the finite residue characterizations of the completed actions.
For positive powers tensor these maps recursively. For negative powers use the
unique dual map whose evaluation is the image of the original evaluation.
On a cover trivializing the root line these maps are the coefficient inclusion,
so the positive maps generate the target line and the dual map is unique.
The formulas commute with restrictions and glue; tensor sheafification and the
local generation of each positive line prove uniqueness in every degree. -/
theorem twistScalarMaps_existsUnique :
    ∃! c : TwistScalarMaps ℓ E S L ι, IsCanonicalTwistScalarMaps ℓ E S L ι c := by
  sorry

/-- The signed scalar maps fixed by root tensors, powers and dual evaluation.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistScalarMaps : TwistScalarMaps ℓ E S L ι :=
  (twistScalarMaps_existsUnique ℓ E S L ι).exists.choose

/-- Scalar extension of each line is the target line, with the specified map.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: extend the semilinear map by balancing, sending s tensor x to s times c(x).
On a trivializing cover this is multiplication R_L tensor R_E to R_L and has
inverse z to z tensor one. Glue the local inverses. Pure tensors generate locally,
so the displayed formula uniquely determines the isomorphism, also at zero. -/
theorem twistLineScalarIso_existsUnique (m : ℤ) :
    ∃! c : (integralOrdinaryScalar ℓ E L ι S).obj (integralTwistLine ℓ E S m) ≅
        integralTwistLine ℓ L S m,
      ∀ (U : S.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
        (x : (integralTwistLine ℓ E S m).val.obj U),
        c.hom.val.app U
            (integralOrdinaryTensorSection ℓ E L ι S _ U s x) =
          s • (@id ((integralTwistLine ℓ L S m).val.obj U)
            ((twistScalarMaps ℓ E S L ι m).val.app U x)) := by
  sorry

/-- The canonical scalar-extension isomorphism for the signed line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistLineScalarIso (m : ℤ) :
    (integralOrdinaryScalar ℓ E L ι S).obj (integralTwistLine ℓ E S m) ≅
      integralTwistLine ℓ L S m :=
  (twistLineScalarIso_existsUnique ℓ E S L ι m).exists.choose

/-- Tensor and scalar extension commute by the normalized balanced map.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: send s tensor (x tensor y) to (s tensor x) tensor c(y), with c the
normalized semilinear line map. Its inverse is the ordinary tensor associator
followed by the inverse canonical line comparison. The balanced formulas commute
with restrictions and module maps. They sheafify to a natural isomorphism.
Local pure-tensor generation uniquely determines every component. -/
theorem twistSheafScalarComparison_existsUnique (m : ℤ) :
    ∃! b : integralSheafTwist ℓ E S m ⋙ integralOrdinaryScalar ℓ E L ι S ≅
        integralOrdinaryScalar ℓ E L ι S ⋙ integralSheafTwist ℓ L S m,
      ∀ (N : integralTowerModules ℓ E S) (U : S.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
        (x : N.val.obj U) (y : (integralTwistLine ℓ E S m).val.obj U),
        (b.hom.app N).val.app U
            (integralOrdinaryTensorSection ℓ E L ι S _ U s
              (SheafOfModules.siteSheafTensorTmul
                (A := completedIntegralCommRingSheafUnrestricted ℓ E S) N _ U x y)) =
          SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U
            (integralOrdinaryTensorSection ℓ E L ι S N U s x)
            ((twistScalarMaps ℓ E S L ι m).val.app U y) := by
  sorry

/-- The ordinary natural comparison fixed on local pure tensors.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistSheafScalarComparison (m : ℤ) :
    integralSheafTwist ℓ E S m ⋙ integralOrdinaryScalar ℓ E L ι S ≅
      integralOrdinaryScalar ℓ E L ι S ⋙ integralSheafTwist ℓ L S m :=
  (twistSheafScalarComparison_existsUnique ℓ E S L ι m).exists.choose

/-- Derive the fixed sheaf comparison through the canonical exact-functor calculus.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistDerivedScalarComparison (m : ℤ) :
    integralComplexTwist D ℓ hℓ E S m ⋙ integralOrdinaryDerivedScalar ℓ E L ι S ≅
      integralOrdinaryDerivedScalar ℓ E L ι S ⋙ integralComplexTwist D ℓ hℓ L S m :=
  (Functor.mapDerivedCategoryCompIso (integralSheafTwist ℓ E S m)
      (integralOrdinaryScalar ℓ E L ι S)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (twistSheafScalarComparison ℓ E S L ι m) ≪≫
    Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar ℓ E L ι S)
      (integralSheafTwist ℓ L S m)

/-- Restrict the normalized derived comparison to the full integral categories.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: both composites preserve the full subcategories. Their full inclusion
lifts the ambient comparison and inverse uniquely. Equality of the underlying
hom components fixes the lift, by faithfulness. -/
theorem twistIntegralScalarComparison_existsUnique (m : ℤ) :
    ∃! b : integralConstructibleComplexTwistFunctor D ℓ hℓ E S m ⋙
        integralConstructibleScalarExtension D ℓ hℓ E L ι S ≅
      integralConstructibleScalarExtension D ℓ hℓ E L ι S ⋙
        integralConstructibleComplexTwistFunctor D ℓ hℓ L S m,
      ∀ K, (b.hom.app K).hom =
        (twistDerivedScalarComparison D ℓ hℓ E S L ι m).hom.app K.obj := by
  sorry

/-- The restricted comparison, with its fixed ambient hom components.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistIntegralScalarComparison (m : ℤ) :=
  (twistIntegralScalarComparison_existsUnique D ℓ hℓ E S L ι m).exists.choose

/-- Localize the fixed integral comparison; every component is tensor with one.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: tensor each integral component and inverse with one. Integral naturality
is linear for the coefficient inclusion, so extends to localized pure tensors
and then sums. Inverse equations persist. Equality of components uniquely fixes
this natural isomorphism in the raw scalar-localized category. -/
theorem twistRationalOrdinaryComparison_existsUnique (m : ℤ) :
    ∃! b : rationalComplexTwistFunctor D ℓ hℓ E S m ⋙
        rationalOrdinaryScalarExtension D ℓ hℓ E S L ι ≅
      rationalOrdinaryScalarExtension D ℓ hℓ E S L ι ⋙
        rationalComplexTwistFunctor D ℓ hℓ L S m,
      ∀ K, HEq (b.hom.app K)
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer ℓ L)) ⊗ₜ[
          Padic.coefficientExtensionIntegers ℓ L]
          (twistIntegralScalarComparison D ℓ hℓ E S L ι m).hom.app K.obj) := by
  sorry

/-- The localized tensor comparison with its integral normalization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistRationalOrdinaryComparison (m : ℤ) :=
  (twistRationalOrdinaryComparison_existsUnique D ℓ hℓ E S L ι m).exists.choose

/-- The comparison with published completed scalar extension, obtained by conjugating
ordinary tensor comparison by the recorded completion comparison.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def rationalTwistScalarComparison (m : ℤ) :
    rationalComplexTwistFunctor D ℓ hℓ E S m ⋙ rationalScalarExtension D ℓ hℓ E S L ι ≅
      rationalScalarExtension D ℓ hℓ E S L ι ⋙ rationalComplexTwistFunctor D ℓ hℓ L S m :=
  Functor.isoWhiskerLeft _ (rationalOrdinaryComparison D ℓ hℓ E S L ι).symm ≪≫
    twistRationalOrdinaryComparison D ℓ hℓ E S L ι m ≪≫
    Functor.isoWhiskerRight (rationalOrdinaryComparison D ℓ hℓ E S L ι) _

end ScalarComparison

/-- Identity scalar extension gives the identity on every signed root line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the identity family satisfies the zero, root-tensor, positive tensor and
negative evaluation normalizations. The unique-family clause identifies it
with twistScalarMaps for the identity coefficient embedding. -/
theorem twistScalarMaps_identity (m : ℤ) (U : S.ProEtᵒᵖ)
    (x : (integralTwistLine ℓ E S m).val.obj U) :
    (twistScalarMaps ℓ E S E (AlgHom.id (Padic ℓ) E) m).val.app U x = x := by
  sorry

/-- The semilinear signed-line maps compose along every coefficient tower.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the completed and constant integer maps compose by their residue formulas.
The composite families therefore have the same zero and root-tensor formulas.
Tensor recursion propagates this to positive powers. Evaluating on the images
of positive-line sections gives the same negative evaluation formula. Uniqueness
of the normalized family identifies the composite with the direct map. -/
theorem twistScalarMaps_composition
    (L : Type u) [Field L] [Algebra (Padic ℓ) L] [FiniteDimensional (Padic ℓ) L]
    (ι : E →ₐ[Padic ℓ] L)
    (M : Type u) [Field M] [Algebra (Padic ℓ) M] [FiniteDimensional (Padic ℓ) M]
    (κ : L →ₐ[Padic ℓ] M) (m : ℤ) (U : S.ProEtᵒᵖ)
    (x : (integralTwistLine ℓ E S m).val.obj U) :
    (twistScalarMaps ℓ E S M (κ.comp ι) m).val.app U x =
      (twistScalarMaps ℓ L S M κ m).val.app U
        ((twistScalarMaps ℓ E S L ι m).val.app U x) := by
  sorry

/-- The identity rational comparison is normalized by the published scalar unit.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the identity semilinear map is the identity on every signed line. The
ordinary tensor comparison consequently sends s tensor (x tensor y) to
(s tensor x) tensor y. The multiplication scalar unit turns both sides into
s*x tensor y. Derivation, full restriction and Hom localization preserve the
equation; conjugation by the completion comparisons gives the displayed unit. -/
theorem rationalTwistScalarComparison_unit (m : ℤ)
    (K : rationalConstructibleCategory D ℓ hℓ E S) :
    (rationalTwistScalarComparison D ℓ hℓ E S E (AlgHom.id (Padic ℓ) E) m).hom.app K =
      (rationalConstructibleScalarUnit ℓ E S D hℓ).hom.app
          ((rationalComplexTwistFunctor D ℓ hℓ E S m).obj K) ≫
        (rationalComplexTwistFunctor D ℓ hℓ E S m).map
          ((rationalConstructibleScalarUnit ℓ E S D hℓ).inv.app K) := by
  sorry

/-- The rational Tate line is compatible with every finite coefficient extension.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the integer Tate line is the same roots-of-unity limit for both fields.
Associativity of sheafified tensor identifies extension of its O_E tensor with its
O_L tensor, and likewise their tensor powers. Duals commute with scalar extension
because the lines are finite locally free. On the complete rank-one objects the
completed scalar extension is ordinary tensor. Apply rationalization to these
canonical comparisons, including at exponent zero. -/
theorem rationalCoefficientTwist_scalarExtension
    (L : Type u) [Field L] [Algebra (Padic ℓ) L]
    [FiniteDimensional (Padic ℓ) L] (ι : E →ₐ[Padic ℓ] L) (m : ℤ) :
    Nonempty
      ((rationalScalarExtension D ℓ hℓ E S L ι).obj
        (rationalCoefficientTwist D ℓ hℓ E S m) ≅
          rationalCoefficientTwist D ℓ hℓ L S m) := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω]
  [IsAlgClosure (Padic ℓ) Ω]

/-- The algebraically closed twist at a finite coefficient stage.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def algebraicClosureCoefficientTwist
    (F : Padic.FiniteCoefficientFields ℓ Ω) (m : ℤ) :
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S :=
  ⟨F, rationalCoefficientTwist D ℓ hℓ (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω F) S m⟩

/-- Twist an algebraically closed coefficient object on its displayed finite stage.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def algebraicClosureComplexTwist (m : ℤ)
    (K : algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S) :
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S :=
  ⟨K.stage, rationalComplexTwist D ℓ hℓ (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω K.stage)
    S m K.obj⟩

/-- The canonical stagewise twist functors used by the common-stage category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def coefficientTwistStageFunctor (m : ℤ)
    (F : Padic.FiniteCoefficientFields ℓ Ω) :
    AlgebraicallyClosedCoefficients.Stage D ℓ hℓ Ω S F ⥤
      AlgebraicallyClosedCoefficients.Stage D ℓ hℓ Ω S F :=
  rationalComplexTwistFunctor D ℓ hℓ
    (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω F) S m

/-- Scalar-extension comparisons are the canonical rational tensor comparisons,
transported to the named stage transitions.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def coefficientTwistStageComparison (m : ℤ) :
    ∀ {F G : AlgebraicallyClosedCoefficients.Index ℓ Ω} (h : F ≤ G),
      coefficientTwistStageFunctor D ℓ hℓ S Ω m F ⋙
          AlgebraicallyClosedCoefficients.stageTransition D ℓ hℓ Ω S F G h ≅
        AlgebraicallyClosedCoefficients.stageTransition D ℓ hℓ Ω S F G h ⋙
          coefficientTwistStageFunctor D ℓ hℓ S Ω m G :=
  fun {F G} h ↦
    Functor.isoWhiskerLeft _
      (eqToIso ((AlgebraicallyClosedCoefficients.stageSystem_existsUnique
        D ℓ hℓ Ω S).exists.choose_spec.1 F G h)) ≪≫
    rationalTwistScalarComparison D ℓ hℓ
      (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω F) S
      (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω G)
      (AlgebraicallyClosedCoefficients.coefficientInclusion ℓ Ω F G h) m ≪≫
    Functor.isoWhiskerRight
      (eqToIso ((AlgebraicallyClosedCoefficients.stageSystem_existsUnique
        D ℓ hℓ Ω S).exists.choose_spec.1 F G h)).symm _

/-- The fixed stage comparisons satisfy the common-stage tower equation.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the normalized signed-line maps compose by twistScalarMaps_composition.
On an iterated local scalar tensor both comparison paths send
b tensor (a tensor (x tensor y)) to (b*ι(a) tensor x) tensor c(y).
Local tensor generation gives the ordinary square with the published scalar
associator. Exact derivation, full restriction and rationalization preserve it.
Expand rationalOrdinaryComparison conjugations and cancel adjacent inverses
by naturality. Transport along stageSystem_existsUnique to obtain the displayed
equation for the actual stage system. Repeated stages are included; the scalar
unit normalization is rationalTwistScalarComparison_unit. -/
theorem coefficientTwistStageComparison_coherent (m : ℤ) :
    CategoryTheory.StageSystem.pairFunctorCoherent
      (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
      (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
      (fun F => coefficientTwistStageFunctor D ℓ hℓ S Ω m F)
      (coefficientTwistStageComparison D ℓ hℓ S Ω m) := by
  sorry

/-- The canonical common-stage Tate-twist endofunctor.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def algebraicClosureComplexTwistFunctor (m : ℤ) :
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S ⥤
      algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S :=
  (CategoryTheory.StageSystem.coefficientPairFunctor_exists
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (fun F => coefficientTwistStageFunctor D ℓ hℓ S Ω m F)
    (coefficientTwistStageComparison D ℓ hℓ S Ω m)
    (coefficientTwistStageComparison_coherent D ℓ hℓ S Ω m)).exists.choose

/-- The common-stage functor has the displayed object assignment.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the object clause of coefficientPairFunctor_exists keeps the source
stage and applies its rational twist. rationalComplexTwistFunctor_obj identifies
this object with the integral-representative formula at that same stage. -/
theorem algebraicClosureComplexTwistFunctor_obj (m : ℤ)
    (K : algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S) :
    (algebraicClosureComplexTwistFunctor D ℓ hℓ S Ω m).obj K =
      algebraicClosureComplexTwist D ℓ hℓ S Ω m K := by
  sorry

/-- The representative formula is part of the descended functor datum: it fixes
the morphism action, rather than specifying objects alone.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: apply the representative clause of coefficientPairFunctor_exists to
the chosen functor. Its formula conjugates the stagewise map by the fixed
source and target comparisons. The preceding coherence theorem makes this
independent of subsequent common-stage enlargement. Every arrow is represented,
so the formula specifies the entire descended morphism action. -/
theorem algebraicClosureComplexTwistFunctor_map_exists (m : ℤ) :
    ∀ {P Q : algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S}
      (M : AlgebraicallyClosedCoefficients.Index ℓ Ω)
      (hP : P.stage ≤ M) (hQ : Q.stage ≤ M)
      (f : P.toStage hP ⟶ Q.toStage hQ),
      HEq ((algebraicClosureComplexTwistFunctor D ℓ hℓ S Ω m).map
        (CategoryTheory.StageSystem.PairCategory.mkHom M hP hQ f))
        (CategoryTheory.StageSystem.PairCategory.mkHom
          (X := ⟨P.stage,
            (coefficientTwistStageFunctor D ℓ hℓ S Ω m P.stage).obj P.obj⟩)
          (Y := ⟨Q.stage,
            (coefficientTwistStageFunctor D ℓ hℓ S Ω m Q.stage).obj Q.obj⟩)
          M hP hQ
          ((coefficientTwistStageComparison D ℓ hℓ S Ω m hP).hom.app P.obj ≫
            (coefficientTwistStageFunctor D ℓ hℓ S Ω m M).map f ≫
            (coefficientTwistStageComparison D ℓ hℓ S Ω m hQ).inv.app Q.obj)) := by
  sorry

/-- The four coefficient lines for all integer twists.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
structure CoefficientTateTwistData (n : ℕ) where
  finite : ℤ → SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S (n - 1))
  integral : ℤ → SheafOfModules.{u + 1}
    (completedIntegralCoefficientSheafUnrestricted ℓ E S)
  rational : ℤ → rationalConstructibleCategory D ℓ hℓ E S
  algebraic : ∀ _F : Padic.FiniteCoefficientFields ℓ Ω, ℤ →
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S

/-- Assemble finite, integral, rational, and common-stage Tate twists.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientTateTwists (n : ℕ) (_hn : 1 ≤ n) :
    CoefficientTateTwistData D ℓ hℓ E S Ω n :=
  { finite := fun m => coefficientTwistLine S (purTwistFiniteOne S ℓ E (n - 1)) m
    integral := fun m => coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m
    rational := fun m => rationalCoefficientTwist D ℓ hℓ E S m
    algebraic := fun F m => algebraicClosureCoefficientTwist D ℓ hℓ S Ω F m }

end WeilConjectures
