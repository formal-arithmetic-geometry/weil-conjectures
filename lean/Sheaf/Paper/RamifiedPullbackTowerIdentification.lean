/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison

/-! # Ramified identification of finite pullback towers

Source: Stacks Project, Tags 093M, 03EK and 03EL; Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: lem-weil-ramified-pullback-tower-identification).

Level n means positive exponent n+1. All scalar extensions below are the existing
sheafified balanced tensor, applied termwise, without a flatness hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

namespace WeilConjectures.RamifiedPullback

/-- The existing ring-sheaf forgetful operation at the actual site sizes.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev ring {W : Scheme.{t}} (R : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R

/-- Module sheaves in the common coefficient universe; the site is unchanged.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev Mod {W : Scheme.{t}} (R : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) := SheafOfModules.{max u (t + 1)} (ring.{t, u} R)

set_option linter.defProp false in
/-- The existing canonical tensor witness, with standard derived localizations.
Only its ordinary functor is used here.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def scalarWitness {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :=
  letI := HasDerivedCategory.standard (Mod.{t, u} R)
  letI := HasDerivedCategory.standard (Mod.{t, u} S)
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{_, max u (t + 1), t + 1, t} c

/-- Ordinary scalar extension, with exactly the existing tensor objects and maps.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def scalar {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    Mod.{t, u} R ⥤ Mod.{t, u} S := (scalarWitness.{t, u} c).choose

/-- Additivity from the existing tensor witness.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
instance scalar_additive {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    (scalar.{t, u} c).Additive :=
  (scalarWitness.{t, u} c).choose_spec.choose_spec.choose_spec.choose

/-- Termwise ordinary scalar extension on all cochain complexes.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev scalarCx {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :=
  (scalar.{t, u} c).mapHomologicalComplex (.up ℤ)

/-- The local tensor s⊗x, with the target scalar written first as in Mathlib.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def tensor {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((scalar.{t, u} c).obj M).val.obj U :=
  (eqToHom ((scalarWitness.{t, u} c).choose_spec.choose M).symm).val.app U
    ((toSheafify (Scheme.ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))

/-- Constant sheafification of a quotient coefficient homomorphism.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def constantMap (W : Scheme.{t}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} A)) ⟶
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} B)) :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom.comp
      (f.comp (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom)))

/-- The zero-based index of the e-subsequence.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def index (e n : ℕ) : ℕ := e * (n + 1) - 1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A finite coefficient sheaf as a module over its actual completed ring.
Source: Stacks 093M (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev coefficientModule (W : Scheme.{t}) (n : ℕ) :
    integralTowerModules l E W :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n))).obj
        (SheafOfModules.unit (ring (integralCoefficientCommRingSheaf l E W n)))

/-- Composite transition in the specified pullback tower, including equal indices.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def transition {X Y : Scheme.{t}} (g : X ⟶ Y) (a b : ℕ) (h : a ≤ b)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralOperationsPullbackLevel l E g b).obj P ⟶
      (integralOperationsPullbackLevel l E g a).obj P :=
  ((integralOperationsPullbackTowerFunctor l E g).obj P).map (homOfLE h).op

/-- The local section ((g⁻¹(p⊗a))⊗b), using the actual pullback adjunction unit.
Source: Stacks 03EL (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def pullTensor {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)) :
    (((integralOperationsPullbackLevel l E g n).obj P).X i).val.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  b • @id (((integralOperationsLevelPullback l E g n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
    (integralOperationsPullbackGenerator l E g n
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The ramified quotient map on the already recorded coefficient sheaves.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def ramifiedMap (W : Scheme.{t}) (e n : ℕ)
    (j : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) :
    integralCoefficientCommRingSheaf l E W n ⟶
      integralCoefficientCommRingSheaf l L W (index e n) := constantMap W j

/-- Normalized coefficient identification on one of the two small pro-etale sites.
The maps are fixed by inclusion, the actual completed projections, and pure tensors.
Source: Stacks 093M and 03EK
(blueprint: lem-weil-ramified-pullback-tower-identification). -/
structure Coefficients (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) (W : Scheme.{t}) where
  completedMap : completedIntegralCommRingSheafUnrestricted l E W ⟶
    completedIntegralCommRingSheafUnrestricted l L W
  projection : ∀ n : ℕ,
    completedMap ≫ completedIntegralCommRingProjectionUnrestricted l L W n =
      integralScalarRho l E L ι W n
  ramified_projection : ∀ n : ℕ,
    completedMap ≫ completedIntegralCommRingProjectionUnrestricted l L W (index e n) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫ ramifiedMap l E L W e n (j n)
  coefficientIso : ∀ n : ℕ,
    (scalar.{t, u} completedMap).obj (coefficientModule l E W n) ≅
      coefficientModule l L W (index e n)
  coefficient_formula : ∀ (n : ℕ) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
    (coefficientIso n).hom.val.app U
      (tensor completedMap (coefficientModule l E W n) U s a) =
        (ramifiedMap l E L W e n (j n)).hom.app U a *
          (completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s
  coefficient_transitions : ∀ (a b : ℕ) (h : a ≤ b) (h' : index e a ≤ index e b)
    (U : W.ProEtᵒᵖ)
    (x : (integralCoefficientCommRingSheaf l E W b).obj.obj U)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
    (coefficientIso a).hom.val.app U
      (tensor completedMap (coefficientModule l E W a) U s
        ((((integralCoefficientSheafSystem l E W).map (homOfLE h).op).hom.app U) x)) =
      (((integralCoefficientSheafSystem l L W).map (homOfLE h').op).hom.app U)
        ((coefficientIso b).hom.val.app U
          (tensor completedMap (coefficientModule l E W b) U s x))

/-- The entire ramified identification, including its specified same-index map.
No auxiliary unit occurs in these data; all maps have their normalized formulas.
Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-ramified-pullback-tower-identification). -/
structure Identification {X Y : Scheme.{t}} (g : X ⟶ Y) where
  e : ℕ
  positive : 1 ≤ e
  ideal : Ideal.span ({integralScalarIntegerInclusion l E L ι
    (Padic.coefficientExtensionUniformizer l E)} : Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e}
  unique_index : ∀ k : ℕ, 1 ≤ k →
    Ideal.span ({integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ k} → k = e
  exponent : ∀ n : ℕ, index e n + 1 = e * (n + 1)
  monotone : Monotone (index e)
  same_le : ∀ n : ℕ, n ≤ index e n
  quotientMap : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
    Padic.coefficientExtensionRing l L (index e n + 1)
  quotient_formula : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
    quotientMap n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
        (integralScalarIntegerInclusion l E L ι a)
  source : Coefficients l E L ι e quotientMap Y
  target : Coefficients l E L ι e quotientMap X
  levelIso : ∀ n : ℕ,
    integralOperationsPullbackLevel l E g n ⋙ scalarCx.{t, u} target.completedMap ≅
      scalarCx.{t, u} source.completedMap ⋙
        integralOperationsPullbackLevel l L g (index e n)
  pullback_formula : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
    (((levelIso n).hom.app P).f i).val.app _
      (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
        _ s (pullTensor l E g n P i V a b p)) =
      pullTensor l L g (index e n) ((scalarCx.{t, u} source.completedMap).obj P) i V
        ((ramifiedMap l E L Y e n (quotientMap n)).hom.app (op V) a)
        ((ramifiedMap l E L X e n (quotientMap n)).hom.app _ b *
          (completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s)
        (tensor source.completedMap (P.X i) (op V) 1 p)
  transitions : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ),
    (scalarCx.{t, u} target.completedMap).map
        ((integralOperationsPullbackTransition l E g n).app P) ≫
          (levelIso n).hom.app P =
      (levelIso (n + 1)).hom.app P ≫
        transition l L g (index e n) (index e (n + 1)) (monotone (Nat.le_succ n))
          ((scalarCx.{t, u} source.completedMap).obj P)
  sameIndex : ∀ n : ℕ,
    integralOperationsPullbackLevel l E g n ⋙ scalarCx.{t, u} target.completedMap ⟶
      scalarCx.{t, u} source.completedMap ⋙ integralOperationsPullbackLevel l L g n
  same_formula : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
    (((sameIndex n).app P).f i).val.app _
      (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
        _ s (pullTensor l E g n P i V a b p)) =
      pullTensor l L g n ((scalarCx.{t, u} source.completedMap).obj P) i V
        ((integralScalarQuotientSheafMap l E L ι Y n).hom.app (op V) a)
        ((integralScalarQuotientSheafMap l E L ι X n).hom.app _ b *
          (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app _ s)
        (tensor source.completedMap (P.X i) (op V) 1 p)
  factorization : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ),
    (sameIndex n).app P = (levelIso n).hom.app P ≫
      transition l L g n (index e n) (same_le n)
        ((scalarCx.{t, u} source.completedMap).obj P)

/-- The scalar-extended finite E-pullback tower is canonically the ramified
subsequence of the L-pullback tower, with the specified same-index factorization.
Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-ramified-pullback-tower-identification).

Proof:
1. Use uniqueness of the extended absolute value and the local-field DVR factorization
   (lem-weil-l-adic-extension-absolute-value and -integers-dvr) to obtain the unique
   positive ramification exponent and equality of the principal-power ideals.
2. The same-index quotient maps give the completed map by its projections. At exponent
   em this factors through the E quotient of exponent m, giving j_m. Naturality of the
   constant coefficient maps gives compatibility with the geometric structure maps.
3. Apply the canonical quotient clause of lem-weil-pbc-constant-completion-equivalence
   (Stacks 093M) to both Noetherian valuation rings. The two ramified ideals agree.
4. The coefficient iso sends a⊗s to j_m(a)π_em(s); its inverse sends the residue of s
   to 1⊗s. Tensor balancing proves inverse identities locally, hence after sheafification.
5. Apply lem-weil-pbc-algebraic-inverse-image-tensor-comparison, with its adjunction
   and finite-limit hypotheses, to identify finite pullback with g⁻¹P⊗B_X.
6. Reassociate these balanced tensors on both sides, cancel the intermediate S_Y
   factor, and use Step 4. This gives the displayed pullback formula degreewise.
7. Quotient reduction commutes with j_m and with the actual limit projections.
   Apply those equations to the formula to prove the transition equation. Replacing
   p by f(p) proves naturality for every chain map.
8. Reduction from em to m sends j_m to iota_m and π_em to π_m, proving the specified
   same-index factorization. The subsequence is increasing and unbounded since e≥1.
9. No formula uses the unit in t=u*v^e; it is used only to prove equality of ideals.
   Thus the normalized maps are independent of that unit. -/
theorem identification {X Y : Scheme.{t}} (g : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Identification l E L ι g) := by
  sorry

end WeilConjectures.RamifiedPullback
