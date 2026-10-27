/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import all Sheaf.Paper.PurTwistRootLocalModels
import all Sheaf.Paper.PurTwistIntegralLocalModels
import all Sheaf.PoincareDuality.CompatiblePrimitiveRoots
import Sheaf.Paper.ScalarExtensionBinaryCoherence
import all Sheaf.Paper.PurInverseImageScalarComparison
import all Sheaf.Paper.ConnectedAdicIntegralBasis

/-! # Primitive-root coordinates for signed point Tate lines

Source: Deligne, La conjecture de Weil I, (2.2), pp. 280--281 and (2.13), p. 283
(blueprint: lem-pur-point-tate-root-coordinates).

The index n denotes the positive exponent n+1. All coordinates use the recorded root
kernel, sectionwise limits, completed integral coefficients and signed tensor/Hom lines.
The auxiliary predicates only spell out the normalization clauses of this lemma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] SheafOfModules.unit PresheafOfModules.unit
  AlgebraicGeometry.Scheme.purTwistRing sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

/-- A constant label, through the constant-presheaf sheafification unit.
Source: Deligne (2.13) (blueprint: lem-pur-point-tate-root-coordinates). -/
def purPointConstant (S : Scheme.{u}) (A : Type v) [CommRing A]
    (U : S.ProEtᵒᵖ) (a : A) :
    (((constantSheaf (ProEt.topology S) CommRingCat.{max v (u + 1)}).obj
      (.of (ULift.{u + 1} A))).obj.obj U) :=
  (toSheafify (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U (ULift.up a)

/-- The signed-coordinate clauses, using the existing tensor powers and internal Hom.
Degree zero is the coefficient unit; successive positive generators are pure tensors;
the negative inverse is evaluation on the corresponding positive generator.
Source: Deligne (2.2), pp. 280--281
(blueprint: lem-pur-point-tate-root-coordinates). -/
def IsPurPointSignedCoordinates (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing S R))
    (c : ∀ m : ℤ, SheafOfModules.unit (purTwistRing S R) ≅ coefficientTwistLine S L m) :
    Prop :=
  (∀ (U : S.ProEtᵒᵖ) (b : R.obj.obj U), (c 0).hom.val.app U b = b) ∧
  (∀ (r : ℕ) (U : S.ProEtᵒᵖ),
    (c (Int.ofNat (r + 2))).hom.val.app U (1 : R.obj.obj U) =
      SheafOfModules.siteSheafTensorTmul
        (coefficientTwistPower S L (r + 1)) L U
        ((c (Int.ofNat (r + 1))).hom.val.app U (1 : R.obj.obj U))
        ((c 1).hom.val.app U (1 : R.obj.obj U))) ∧
  (∀ (m : ℤ) (U : S.ProEtᵒᵖ) (b : R.obj.obj U),
    (c m).hom.val.app U b = b • (c m).hom.val.app U (1 : R.obj.obj U)) ∧
  (∀ (r : ℕ) (U : S.ProEtᵒᵖ) (b : R.obj.obj U),
    (c (Int.ofNat (r + 1))).inv.val.app U
      (b • (c (Int.ofNat (r + 1))).hom.val.app U (1 : R.obj.obj U)) = b) ∧
  (∀ (r : ℕ) (U : S.ProEtᵒᵖ)
      (φ : (coefficientTwistLine S L (Int.negSucc r)).val.obj U),
    (c (Int.negSucc r)).inv.val.app U φ =
      φ.app (op (Over.mk (𝟙 U.unop)))
        ((c (Int.ofNat (r + 1))).hom.val.app U (1 : R.obj.obj U))) ∧
  (∀ (r : ℕ) (U : S.ProEtᵒᵖ),
    ((c (Int.negSucc r)).hom.val.app U (1 : R.obj.obj U)).app (op (Over.mk (𝟙 U.unop)))
      ((c (Int.ofNat (r + 1))).hom.val.app U (1 : R.obj.obj U)) = (1 : R.obj.obj U))

/-- All finite, completed and signed coordinates associated to a prescribed root sequence.
This is a packaging of the conclusion, with no hypothesis on the sequence hidden in it.
Source: Deligne (2.2), (2.13)
(blueprint: lem-pur-point-tate-root-coordinates). -/
def HasPurPointRootCoordinates (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (ζ : ℕ → D.k) : Prop :=
  ∃ (f : ∀ n : ℕ,
      SheafOfModules.unit (purTwistRing (Spec (.of D.k))
        (purTwistFiniteRing (Spec (.of D.k)) l n)) ≅
          purTwistRootsModule (Spec (.of D.k)) l n)
    (g : SheafOfModules.unit (purTwistRing (Spec (.of D.k))
        (purTwistZlCompletion (Spec (.of D.k)) l)) ≅
          purTwistZlModule (Spec (.of D.k)) l)
    (c : ∀ m : ℤ,
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))) ≅
        integralTwistLine l E (Spec (.of D.k)) m)
    (d : ∀ (n : ℕ) (m : ℤ),
      SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) n) ≅
        coefficientTwistLine (Spec (.of D.k)) (purTwistFiniteOne (Spec (.of D.k)) l E n) m),
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) (j : ZMod (l ^ (n + 1))),
      ((proEtaleRootsOfUnitySections (Spec (.of D.k)) (l ^ (n + 1)) U)
        ((f n).hom.val.app U
          (purPointConstant (Spec (.of D.k)) (ZMod (l ^ (n + 1))) U j))).toMul.val.val =
        U.unop.hom.appTop ((Scheme.ΓSpecIso (.of D.k)).inv (ζ n ^ j.val))) ∧
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (a : (purTwistFiniteRing (Spec (.of D.k)) l (n + 1)).obj.obj U),
      (proEtaleRootsOfUnityTransition (Spec (.of D.k)) (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U ((f (n + 1)).hom.val.app U a) =
      (f n).hom.val.app U ((purTwistFiniteTransition (Spec (.of D.k)) l n).hom.app U a)) ∧
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (a : (purTwistZlCompletion (Spec (.of D.k)) l).obj.obj U),
      (limit.π (proEtaleRootsOfUnityTower (Spec (.of D.k)) l (Fact.out : l.Prime))
        (op n)).hom.app U (g.hom.val.app U a) =
      (f n).hom.val.app U ((purTwistZlProjection (Spec (.of D.k)) l n).hom.app U a)) ∧
    (∀ U : (Spec (.of D.k)).ProEtᵒᵖ,
      (c 1).hom.val.app U
        (1 : (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))).obj.obj U) =
        purTwistIntegralTensor (Spec (.of D.k)) l E U 1 (g.hom.val.app U
          (1 : (purTwistZlCompletion (Spec (.of D.k)) l).obj.obj U))) ∧
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ),
      (d n 1).hom.val.app U
        (1 : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj U) =
        SheafOfModules.scalarExtensionSection
          (purTwistIntegralQuotient (Spec (.of D.k)) l E n)
          (purTwistIntegralOne (Spec (.of D.k)) l E) U 1 ((c 1).hom.val.app U
        (1 : (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))).obj.obj U))) ∧
    IsPurPointSignedCoordinates (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))
      (purTwistIntegralModule (Spec (.of D.k)) l E) c ∧
    (∀ n : ℕ, IsPurPointSignedCoordinates (Spec (.of D.k))
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)
      (purTwistFiniteOne (Spec (.of D.k)) l E n) (d n)) ∧
    (∃ ι : Padic.coefficientExtensionIntegers l E ≃+*
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))).obj.obj
          (op (ProEt.mk (𝟙 (Spec (.of D.k))))),
      (∀ b, ι b = integralScalarConstant l E (Spec (.of D.k))
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) b) ∧
      ∀ m : ℤ, Function.Bijective (fun b : Padic.coefficientExtensionIntegers l E ↦
        (c m).hom.val.app (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (ι b))) ∧
    (∀ n : ℕ, ∃ ι : Padic.coefficientExtensionRing l E (n + 1) ≃+*
        (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj
          (op (ProEt.mk (𝟙 (Spec (.of D.k))))),
      (∀ b, ι b = purPointConstant (Spec (.of D.k))
        (Padic.coefficientExtensionRing l E (n + 1))
          (op (ProEt.mk (𝟙 (Spec (.of D.k))))) b) ∧
      ∀ m : ℤ, Function.Bijective (fun b : Padic.coefficientExtensionRing l E (n + 1) ↦
        (d n m).hom.val.app (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (ι b)))

private theorem pointIso_bijective {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (e : M ≅ N) (U : S.ProEtᵒᵖ) :
    Function.Bijective (e.hom.val.app U) := by
  constructor
  · intro x y h
    have hx := congrArg (fun f ↦ f.val.app U x) e.hom_inv_id
    have hy := congrArg (fun f ↦ f.val.app U y) e.hom_inv_id
    exact hx.symm.trans ((congrArg (e.inv.val.app U) h).trans hy)
  · intro y
    exact ⟨e.inv.val.app U y, congrArg (fun f ↦ f.val.app U y) e.inv_hom_id⟩

private def pointUnsliceIso {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (T : S.ProEt) (hT : IsTerminal T)
    (e : M.over T ≅ N.over T) : M ≅ N where
  hom.val :=
    { app := fun U ↦ e.hom.val.app (op (Over.mk (hT.from U.unop)))
      naturality := by
        intro U V f
        let i : Over.mk (hT.from V.unop) ⟶ Over.mk (hT.from U.unop) :=
          Over.homMk f.unop (hT.hom_ext _ _)
        exact e.hom.val.naturality i.op }
  inv.val :=
    { app := fun U ↦ e.inv.val.app (op (Over.mk (hT.from U.unop)))
      naturality := by
        intro U V f
        let i : Over.mk (hT.from V.unop) ⟶ Over.mk (hT.from U.unop) :=
          Over.homMk f.unop (hT.hom_ext _ _)
        exact e.inv.val.naturality i.op }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    exact congrArg (fun f ↦ f.val.app (op (Over.mk (hT.from U.unop)))) e.hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    exact congrArg (fun f ↦ f.val.app (op (Over.mk (hT.from U.unop)))) e.inv_hom_id

private def pointTensorSecondIso {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} (purTwistRing S R))
    {N P : SheafOfModules.{u + 1} (purTwistRing S R)} (e : N ≅ P) :
    (SheafOfModules.siteSheafTensorRight N).obj M ≅
      (SheafOfModules.siteSheafTensorRight P).obj M where
  hom := SheafOfModules.siteSheafTensorSecondMap M e.hom
  inv := SheafOfModules.siteSheafTensorSecondMap M e.inv
  hom_inv_id := by
    apply SheafOfModules.scalarTensor_hom_ext (R := R) M _
    intro U x y
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.scalarTensor_second_tmul (R := R)]
    have h := congrArg (fun f ↦ f.val.app U y) e.hom_inv_id
    change e.inv.val.app U (e.hom.val.app U y) = y at h
    rw [h]
    rfl
  inv_hom_id := by
    apply SheafOfModules.scalarTensor_hom_ext (R := R) M _
    intro U x y
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.scalarTensor_second_tmul (R := R)]
    have h := congrArg (fun f ↦ f.val.app U y) e.inv_hom_id
    change e.hom.val.app U (e.inv.val.app U y) = y at h
    rw [h]
    rfl

private def pointTensorChart {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : M ≅ SheafOfModules.unit (purTwistRing S R))
    (f : N ≅ SheafOfModules.unit (purTwistRing S R)) :
    (SheafOfModules.siteSheafTensorRight N).obj M ≅
      SheafOfModules.unit (purTwistRing S R) :=
  (SheafOfModules.siteSheafTensorRight N).mapIso e ≪≫
    pointTensorSecondIso _ f ≪≫ SheafOfModules.scalarTensorLeftUnitor R _

private theorem pointTensorChart_tmul {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : M ≅ SheafOfModules.unit (purTwistRing S R))
    (f : N ≅ SheafOfModules.unit (purTwistRing S R))
    (U : S.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (pointTensorChart e f).hom.val.app U (SheafOfModules.siteSheafTensorTmul M N U x y) =
      e.hom.val.app U x * f.hom.val.app U y := by
  change (SheafOfModules.scalarTensorLeftUnitor R _).hom.val.app U
    ((SheafOfModules.siteSheafTensorSecondMap _ f.hom).val.app U
      (((SheafOfModules.siteSheafTensorRight N).map e.hom).val.app U
        (SheafOfModules.siteSheafTensorTmul M N U x y))) = _
  have h₁ := SheafOfModules.scalarTensor_first_tmul (R := R) e.hom N U x y
  have h₂ := SheafOfModules.scalarTensor_second_tmul (R := R)
    (SheafOfModules.unit (purTwistRing S R)) f.hom U (e.hom.val.app U x) y
  have h₃ := SheafOfModules.scalarTensorLeftUnitor_tmul R
    (SheafOfModules.unit (purTwistRing S R)) U
      (e.hom.val.app U x) (f.hom.val.app U y)
  exact (congrArg (fun z ↦ (SheafOfModules.scalarTensorLeftUnitor R _).hom.val.app U
    ((SheafOfModules.siteSheafTensorSecondMap _ f.hom).val.app U z)) h₁).trans
    ((congrArg ((SheafOfModules.scalarTensorLeftUnitor R _).hom.val.app U) h₂).trans h₃)

private def pointPositiveCoordinates {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) :
    ∀ n : ℕ, SheafOfModules.unit (purTwistRing S R) ≅ coefficientTwistPower S L (n + 1)
  | 0 => e
  | n + 1 => (pointTensorChart
      (pointPositiveCoordinates e n).symm e.symm).symm

private theorem pointCoordinate_linear {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    {M : SheafOfModules.{u + 1} R} (e : SheafOfModules.unit R ≅ M)
    (U : S.ProEtᵒᵖ) (b : R.obj.obj U) :
    e.hom.val.app U b = b • e.hom.val.app U (1 : R.obj.obj U) := by
  have h := (e.hom.val.app U).hom.map_smul b (1 : R.obj.obj U)
  change e.hom.val.app U (b * 1) = _ at h
  simpa only [mul_one] using h

private theorem pointCoordinate_inverse {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    {M : SheafOfModules.{u + 1} R} (e : SheafOfModules.unit R ≅ M)
    (U : S.ProEtᵒᵖ) (b : R.obj.obj U) :
    e.inv.val.app U (b • e.hom.val.app U (1 : R.obj.obj U)) = b := by
  rw [← pointCoordinate_linear e U b]
  exact congrArg (fun f ↦ f.val.app U b) e.hom_inv_id

private theorem pointPositiveCoordinates_one {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) (n : ℕ) (U : S.ProEtᵒᵖ) :
    (pointPositiveCoordinates e (n + 1)).hom.val.app U (1 : R.obj.obj U) =
      SheafOfModules.siteSheafTensorTmul (coefficientTwistPower S L (n + 1)) L U
        ((pointPositiveCoordinates e n).hom.val.app U (1 : R.obj.obj U))
        (e.hom.val.app U (1 : R.obj.obj U)) := by
  let q := pointTensorChart (pointPositiveCoordinates e n).symm e.symm
  have hinj : Function.Injective (q.hom.val.app U) := by
    intro x y h
    have hx := congrArg (fun f ↦ f.val.app U x) q.hom_inv_id
    have hy := congrArg (fun f ↦ f.val.app U y) q.hom_inv_id
    exact hx.symm.trans ((congrArg (q.inv.val.app U) h).trans hy)
  apply hinj
  change q.hom.val.app U (q.inv.val.app U (1 : R.obj.obj U)) =
    q.hom.val.app U (SheafOfModules.siteSheafTensorTmul
      (coefficientTwistPower S L (n + 1)) L U
      ((pointPositiveCoordinates e n).hom.val.app U (1 : R.obj.obj U))
      (e.hom.val.app U (1 : R.obj.obj U)))
  rw [show q.hom.val.app U (q.inv.val.app U 1) = (1 : R.obj.obj U) from
    congrArg (fun f ↦ f.val.app U (1 : R.obj.obj U)) q.inv_hom_id]
  change (1 : R.obj.obj U) =
    (pointTensorChart (pointPositiveCoordinates e n).symm e.symm).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul
      (coefficientTwistPower S L (n + 1)) L U
      ((pointPositiveCoordinates e n).hom.val.app U (1 : R.obj.obj U))
      (e.hom.val.app U (1 : R.obj.obj U)))
  rw [pointTensorChart_tmul (R := R)]
  have hp := pointCoordinate_inverse (pointPositiveCoordinates e n) U (1 : R.obj.obj U)
  have he := pointCoordinate_inverse e U (1 : R.obj.obj U)
  simp only [one_smul] at hp he
  simp only [Iso.symm_hom, hp, he, one_mul]

private def pointDualGenerator {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) (U : S.ProEtᵒᵖ) :
    (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R) L
      (SheafOfModules.unit (purTwistRing S R))).val.obj U where
  app W := e.inv.val.app (op W.unop.left)
  naturality i := e.inv.val.naturality i.unop.left.op

private theorem pointDualGenerator_natural {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L)
    {U V : S.ProEtᵒᵖ} (f : U ⟶ V) :
    (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R) L
      (SheafOfModules.unit (purTwistRing S R))).val.map f
      (pointDualGenerator e U) = pointDualGenerator e V := rfl

private theorem pointDualGenerator_bijective {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) (U : S.ProEtᵒᵖ) :
    Function.Bijective (fun b : R.obj.obj U ↦ b • pointDualGenerator e U) := by
  let T := op (Over.mk (𝟙 U.unop))
  have hev (b : R.obj.obj U) :
      (b • pointDualGenerator e U).app T
        (e.hom.val.app U (1 : R.obj.obj U)) = b := by
    change R.obj.map (𝟙 U.unop).op b *
      (show R.obj.obj U from e.inv.val.app U (e.hom.val.app U (1 : R.obj.obj U))) = b
    erw [R.obj.map_id]
    rw [show e.inv.val.app U (e.hom.val.app U (1 : R.obj.obj U)) =
      (1 : R.obj.obj U) from
      congrArg (fun f ↦ f.val.app U (1 : R.obj.obj U)) e.hom_inv_id, mul_one]
    rfl
  constructor
  · intro a b h
    exact (hev a).symm.trans ((congrArg (fun φ ↦
      φ.app T (e.hom.val.app U (1 : R.obj.obj U))) h).trans (hev b))
  · intro φ
    refine ⟨φ.app T (e.hom.val.app U (1 : R.obj.obj U)), ?_⟩
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let V := op W.unop.left
    let i : W.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk W.unop.hom
    have hn := PresheafOfModules.naturality_apply φ i.op
      (e.hom.val.app U (1 : R.obj.obj U))
    have he := PresheafOfModules.naturality_apply e.hom.val W.unop.hom.op
      (1 : R.obj.obj U)
    change e.hom.val.app V (R.obj.map W.unop.hom.op (1 : R.obj.obj U)) = _ at he
    rw [map_one] at he
    change φ.app W (L.val.map W.unop.hom.op _) = _ at hn
    rw [← he] at hn
    have hx : e.inv.val.app V x • e.hom.val.app V (1 : R.obj.obj V) = x := by
      rw [← pointCoordinate_linear]
      exact congrArg (fun f ↦ f.val.app V x) e.inv_hom_id
    change R.obj.map W.unop.hom.op (φ.app T (e.hom.val.app U (1 : R.obj.obj U))) *
      (show R.obj.obj V from e.inv.val.app V x) = φ.app W x
    conv_rhs => rw [← hx]
    rw [map_smul, hn]
    exact mul_comm _ _

private def pointDualCoordinates {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) :
    SheafOfModules.unit (purTwistRing S R) ≅
      SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R) L
      (SheafOfModules.unit (purTwistRing S R)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ (LinearEquiv.ofBijective
        { toFun := fun b : R.obj.obj U ↦ b • pointDualGenerator e U
          map_add' := fun a b ↦ add_smul a b _
          map_smul' := fun a b ↦ mul_smul a b _ }
        (pointDualGenerator_bijective e U)).toModuleIso)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        change R.obj.map f b • pointDualGenerator e V =
          (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R) L
            (SheafOfModules.unit (purTwistRing S R))).val.map f
              (b • pointDualGenerator e U)
        rw [PresheafOfModules.map_smul, pointDualGenerator_natural]
        rfl))

private theorem pointDualCoordinates_inverse {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) (U : S.ProEtᵒᵖ)
    (φ : (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R) L
      (SheafOfModules.unit (purTwistRing S R))).val.obj U) :
    (pointDualCoordinates e).inv.val.app U φ =
      φ.app (op (Over.mk (𝟙 U.unop))) (e.hom.val.app U (1 : R.obj.obj U)) := by
  obtain ⟨b, rfl⟩ := (pointDualGenerator_bijective e U).surjective φ
  change (pointDualCoordinates e).inv.val.app U
    ((pointDualCoordinates e).hom.val.app U b) = _
  rw [show (pointDualCoordinates e).inv.val.app U
    ((pointDualCoordinates e).hom.val.app U b) = b from
      congrArg (fun f ↦ f.val.app U b) (pointDualCoordinates e).hom_inv_id]
  change b = (b • pointDualGenerator e U).app (op (Over.mk (𝟙 U.unop)))
    (e.hom.val.app U (1 : R.obj.obj U))
  change b = R.obj.map (𝟙 U.unop).op b *
    (show R.obj.obj U from e.inv.val.app U (e.hom.val.app U (1 : R.obj.obj U)))
  erw [R.obj.map_id]
  rw [show e.inv.val.app U (e.hom.val.app U (1 : R.obj.obj U)) =
    (1 : R.obj.obj U) from
      congrArg (fun f ↦ f.val.app U (1 : R.obj.obj U)) e.hom_inv_id, mul_one]
  rfl

private def pointSignedCoordinates {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) :
    ∀ m : ℤ, SheafOfModules.unit (purTwistRing S R) ≅ coefficientTwistLine S L m
  | .ofNat 0 => Iso.refl _
  | .ofNat (n + 1) => pointPositiveCoordinates e n
  | .negSucc n => pointDualCoordinates (pointPositiveCoordinates e n)

private theorem pointSignedCoordinates_spec {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {L : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ L) :
    IsPurPointSignedCoordinates S R L (pointSignedCoordinates e) := by
  refine ⟨fun _ _ ↦ rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact pointPositiveCoordinates_one e
  · intro m U b
    exact pointCoordinate_linear (pointSignedCoordinates e m) U b
  · intro r U b
    exact pointCoordinate_inverse (pointPositiveCoordinates e r) U b
  · intro r U φ
    exact pointDualCoordinates_inverse _ U φ
  · intro r U
    have h := pointDualCoordinates_inverse (pointPositiveCoordinates e r) U
      ((pointSignedCoordinates e (.negSucc r)).hom.val.app U (1 : R.obj.obj U))
    refine h.symm.trans ?_
    exact congrArg (fun f ↦ f.val.app U (1 : R.obj.obj U))
      (pointDualCoordinates (pointPositiveCoordinates e r)).hom_inv_id

private theorem pointRootTower (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) :
    ∃ ζ : ℕ → D.k,
      (∀ n : ℕ, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) ∧
      (∀ n : ℕ, ζ (n + 1) ^ l = ζ n) := by
  classical
  have hp : l.Prime := Fact.out
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : NeZero (l : D.k) := ⟨CharP.cast_ne_zero_of_ne_of_prime D.k hp hl.symm⟩
  obtain ⟨z, hz, _⟩ := (IsSepClosed.exists_isPrimitiveRoot.{u, u} D.k l).2.2
  choose step hstep using fun x : D.k ↦ IsAlgClosed.exists_pow_nat_eq x hp.pos
  let ζ : ℕ → D.k := fun n ↦ step^[n] z
  have hζ (n : ℕ) : ζ (n + 1) ^ l = ζ n := by
    change step^[n + 1] z ^ l = step^[n] z
    rw [Function.iterate_succ_apply']
    exact hstep _
  have hpow (n : ℕ) : ζ n ^ (l ^ n) = z := by
    induction n with
    | zero => simp [ζ]
    | succ n ih => rw [pow_succ', pow_mul, hζ, ih]
  refine ⟨ζ, ?_, hζ⟩
  intro n
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow
  · rw [hpow]
    exact hz.ne_one hp.one_lt
  · rw [pow_succ, pow_mul, hpow, hz.pow_eq_one]

private theorem pointConstantForget
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Category* B]
    [HasWeakSheafify J A] [HasWeakSheafify J B] (G : A ⥤ B)
    [J.PreservesSheafification G] [J.HasSheafCompose G] (X : A) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj X)) G ≫
      ((constantCommuteCompose J G).app X).hom.hom =
        (Functor.constComp Cᵒᵖ X G).hom ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj (G.obj X)) := by
  erw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]

private def pointRootUnit (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) (n : ℕ) :
    Γ(Spec (.of D.k), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of D.k)).inv.hom.toMonoidHom
    ((hζ n).isUnit (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).unit

private theorem pointRootUnit_val (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) (n : ℕ) :
    (pointRootUnit D l ζ hζ n : Γ(Spec (.of D.k), ⊤)) =
      (Scheme.ΓSpecIso (.of D.k)).inv (ζ n) := by
  simp only [pointRootUnit, Units.coe_map, IsUnit.unit_spec]
  rfl

private theorem pointRootUnit_pow (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) (n : ℕ) :
    pointRootUnit D l ζ hζ n ^ (l ^ (n + 1)) = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, pointRootUnit_val, Units.val_one]
  rw [← map_pow, (hζ n).pow_eq_one, map_one]

private theorem pointRootUnit_diff (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (n i : ℕ) (hi : i < l ^ (n + 1)) (j : ℕ) (hj : j < l ^ (n + 1)) (hij : i ≠ j) :
    IsUnit ((pointRootUnit D l ζ hζ n : Γ(Spec (.of D.k), ⊤)) ^ i -
      (pointRootUnit D l ζ hζ n : Γ(Spec (.of D.k), ⊤)) ^ j) := by
  simp only [pointRootUnit_val]
  rw [← map_pow, ← map_pow, ← map_sub]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr
    (fun h ↦ hij ((hζ n).pow_inj hi hj h)))).map (Scheme.ΓSpecIso (.of D.k)).inv.hom

private def pointRootUnitTower (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) :
    ℕ → Γ(Spec (.of D.k), ⊤)ˣ
  | 0 => 1
  | n + 1 => pointRootUnit D l ζ hζ n

private theorem pointRootUnitTower_pow (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) :
    ∀ n, pointRootUnitTower D l ζ hζ n ^ (l ^ n) = 1
  | 0 => by simp [pointRootUnitTower]
  | n + 1 => pointRootUnit_pow D l ζ hζ n

private theorem pointRootUnitTower_diff (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) :
    ∀ n i, i < l ^ n → ∀ j, j < l ^ n → i ≠ j →
      IsUnit ((pointRootUnitTower D l ζ hζ n : Γ(Spec (.of D.k), ⊤)) ^ i -
        (pointRootUnitTower D l ζ hζ n : Γ(Spec (.of D.k), ⊤)) ^ j)
  | 0, i, hi, j, hj, hij => by simp only [pow_zero] at hi hj; omega
  | n + 1, i, hi, j, hj, hij => pointRootUnit_diff D l ζ hζ n i hi j hj hij

private theorem pointRootUnitTower_step (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (hc : ∀ n, ζ (n + 1) ^ l = ζ n) :
    ∀ n, pointRootUnitTower D l ζ hζ (n + 1) ^ l = pointRootUnitTower D l ζ hζ n
  | 0 => by simpa [pointRootUnitTower] using pointRootUnit_pow D l ζ hζ 0
  | n + 1 => by
    apply Units.ext
    simp only [pointRootUnitTower, Units.val_pow_eq_pow_val, pointRootUnit_val]
    rw [← map_pow, hc]

private def pointRootTowerIso (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (hc : ∀ n, ζ (n + 1) ^ l = ζ n) :
    purTwistZlTower (Spec (.of D.k)) l ⋙ sheafCompose (ProEt.topology (Spec (.of D.k)))
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) ≅
      proEtaleRootsOfUnityTower (Spec (.of D.k)) l (Fact.out : l.Prime) :=
  coefficientTowerIso (Spec (.of D.k)) l ≪≫
    Functor.isoWhiskerLeft successorIndex
      (ProEtale.rootsBasisIso (Spec (.of D.k)) l (pointRootUnitTower D l ζ hζ)
        (pointRootUnitTower_pow D l ζ hζ) (pointRootUnitTower_step D l ζ hζ hc)
        (pointRootUnitTower_diff D l ζ hζ)) ≪≫
    (actualRootTowerIso (Spec (.of D.k)) l).symm

private noncomputable def pointFiniteCoordinates
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) (n : ℕ) :
    SheafOfModules.unit (purTwistRing (Spec (.of D.k))
      (purTwistFiniteRing (Spec (.of D.k)) l n)) ≅
        purTwistRootsModule (Spec (.of D.k)) l n := by
  let S := Spec (.of D.k)
  let N := l ^ (n + 1)
  let : NeZero N := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let z := pointRootUnit D l ζ hζ n
  have hz := pointRootUnit_pow D l ζ hζ n
  have hd := pointRootUnit_diff D l ζ hζ n
  let := forgetCommAbPreserves S
  let G := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let e := (constantCommuteCompose (ProEt.topology S) G).app
      (CommRingCat.of (ULift.{u + 1} (ZMod N))) ≪≫
    ProEtale.constantRootsIso N z hz hd ≪≫
    (rawRootIso S N).symm
  let a := Functor.whiskerRight (toSheafify (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod N)))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallySurjective (ProEt.topology S) a := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology S)
      (Functor.whiskerRight (toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} (ZMod N)))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  exact moduleIsoOfAddIso (ProEt.topology S) N
    (purTwistRing S (purTwistFiniteRing S l n)) a
    (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n)))
    (purTwistRootsModule S l n) e

private theorem pointFiniteCoordinates_formula
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) (j : ZMod (l ^ (n + 1))) :
    ((proEtaleRootsOfUnitySections (Spec (.of D.k)) (l ^ (n + 1)) U)
      ((pointFiniteCoordinates D l ζ hζ n).hom.val.app U
        (purPointConstant (Spec (.of D.k)) (ZMod (l ^ (n + 1))) U j))).toMul.val.val =
      U.unop.hom.appTop ((Scheme.ΓSpecIso (.of D.k)).inv (ζ n ^ j.val)) := by
  let S := Spec (.of D.k)
  let N := l ^ (n + 1)
  let : NeZero N := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let z := pointRootUnit D l ζ hζ n
  let hz := pointRootUnit_pow D l ζ hζ n
  let hd := pointRootUnit_diff D l ζ hζ n
  let G := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let := forgetCommAbPreserves S
  let c := (constantCommuteCompose (ProEt.topology S) G).app
    (CommRingCat.of (ULift.{u + 1} (ZMod N)))
  let t := ProEtale.zmodToRootsPresheaf S N z hz
  have hc := congrArg (fun f ↦ f.app U (ULift.up j))
    (pointConstantForget (ProEt.topology S) G (CommRingCat.of (ULift.{u + 1} (ZMod N))))
  change c.hom.hom.app U (purPointConstant S (ZMod N) U j) =
    (toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app U (ULift.up j) at hc
  have hn := congrArg (fun f ↦ f.app U (ULift.up j))
    (toSheafify_naturality (ProEt.topology S) t)
  have hr : (rawRootIso S N).hom.hom.app U
      ((pointFiniteCoordinates D l ζ hζ n).hom.val.app U
        (purPointConstant S (ZMod N) U j)) =
      (toSheafify (ProEt.topology S) (ProEtale.rootsOfUnityPresheaf S N)).app U
        (t.app U (ULift.up j)) := by
    change (rawRootIso S N).hom.hom.app U
      ((rawRootIso S N).inv.hom.app U
        ((ProEtale.constantRootsIso N z hz hd).hom.hom.app U
          (c.hom.hom.app U (purPointConstant S (ZMod N) U j)))) = _
    rw [show (rawRootIso S N).hom.hom.app U
      ((rawRootIso S N).inv.hom.app U _) = _ from
      congrArg (fun f ↦ f.hom.app U
        ((ProEtale.constantRootsIso N z hz hd).hom.hom.app U
          (c.hom.hom.app U (purPointConstant S (ZMod N) U j))))
        (rawRootIso S N).inv_hom_id]
    change (sheafifyMap (ProEt.topology S) t).app U
      (c.hom.hom.app U (purPointConstant S (ZMod N) U j)) = _
    rw [hc]
    exact hn.symm
  have ha : (rootRawPresheafIso S N).hom.app U
      ((pointFiniteCoordinates D l ζ hζ n).hom.val.app U
        (purPointConstant S (ZMod N) U j)) = t.app U (ULift.up j) := by
    have hs : Presheaf.IsSheaf (ProEt.topology S)
        (ProEtale.rootsOfUnityPresheaf S N) :=
      (Presheaf.isSheaf_of_iso_iff (rootRawPresheafIso S N)).mp
        (proEtaleRootsOfUnitySheaf S N).property
    apply ((ConcreteCategory.bijective_of_isIso
      ((isoSheafify (ProEt.topology S) hs).hom.app U)).injective)
    have hnat := congrArg (fun f ↦ f.app U
      ((pointFiniteCoordinates D l ζ hζ n).hom.val.app U
        (purPointConstant S (ZMod N) U j)))
      (toSheafify_naturality (ProEt.topology S) (rootRawPresheafIso S N).hom)
    exact hnat.trans hr
  have h := congrArg (fun x ↦ x.down.toMul.val.val) ha
  have ht := ProEtale.zmodToRootsPresheaf_app_natCast N z hz U j.val
  rw [ZMod.natCast_zmod_val] at ht
  refine h.trans (ht.trans ?_)
  change U.unop.hom.appTop (pointRootUnit D l ζ hζ n : Γ(S, ⊤)) ^ j.val = _
  rw [pointRootUnit_val]
  exact (U.unop.hom.appTop.hom.map_pow _ _).symm.trans
    (congrArg U.unop.hom.appTop
      ((Scheme.ΓSpecIso (.of D.k)).inv.hom.map_pow _ _).symm)

private theorem pointRootTowerIso_app (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (hc : ∀ n, ζ (n + 1) ^ l = ζ n) (n : ℕ) :
    (pointRootTowerIso D l ζ hζ hc).app (op n) =
      (SheafOfModules.toSheaf (purTwistRing (Spec (.of D.k))
        (purTwistFiniteRing (Spec (.of D.k)) l n))).mapIso
          (pointFiniteCoordinates D l ζ hζ n) := by
  let S := Spec (.of D.k)
  let N := l ^ (n + 1)
  let : NeZero N := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let := forgetCommAbPreserves S
  let c := (constantCommuteCompose (ProEt.topology S)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} (ZMod N)))
  let t := ProEtale.constantRootsIso N (pointRootUnit D l ζ hζ n)
    (pointRootUnit_pow D l ζ hζ n) (pointRootUnit_diff D l ζ hζ n)
  have hf : (SheafOfModules.toSheaf (purTwistRing S (purTwistFiniteRing S l n))).map
      (pointFiniteCoordinates D l ζ hζ n).hom =
      (c ≪≫ t ≪≫ (rawRootIso S N).symm).hom := by rfl
  have ha : (actualRootTowerIso S l).hom.app (op n) = (rawRootIso S N).hom := by
    simp [actualRootTowerIso, actualRawRootTowerIso, rawRootIso,
      ProEtale.rootsSheafificationIso, sheafificationNatIso]
    rfl
  dsimp only [S] at ha
  apply Iso.ext
  change (pointRootTowerIso D l ζ hζ hc).hom.app (op n) =
    (SheafOfModules.toSheaf (purTwistRing S (purTwistFiniteRing S l n))).map
      (pointFiniteCoordinates D l ζ hζ n).hom
  erw [hf]
  apply (cancel_mono (rawRootIso S N).hom).mp
  dsimp only [S]
  rw [← ha]
  simp only [pointRootTowerIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [ha]
  simp only [Iso.inv_hom_id, Category.comp_id]
  change _ = c.hom ≫ t.hom
  rfl

private def pointCompletedCoordinates
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (hc : ∀ n, ζ (n + 1) ^ l = ζ n) :
    SheafOfModules.unit (purTwistRing (Spec (.of D.k))
      (purTwistZlCompletion (Spec (.of D.k)) l)) ≅
        purTwistZlModule (Spec (.of D.k)) l :=
  pointUnsliceIso (ProEt.mk (𝟙 (Spec (.of D.k))))
    (ProEt.isTerminalMkId _) (completedBasis (Spec (.of D.k)) l
      (ProEt.mk (𝟙 (Spec (.of D.k))))
      (Functor.isoWhiskerRight (pointRootTowerIso D l ζ hζ hc).symm
        ((ProEt.topology (Spec (.of D.k))).overPullback AddCommGrpCat.{u + 1}
          (ProEt.mk (𝟙 (Spec (.of D.k))))))).symm

private theorem pointCompletedCoordinates_projection
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (hc : ∀ n, ζ (n + 1) ^ l = ζ n) (n : ℕ)
    (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a : (purTwistZlCompletion (Spec (.of D.k)) l).obj.obj U) :
    (limit.π (proEtaleRootsOfUnityTower (Spec (.of D.k)) l (Fact.out : l.Prime))
      (op n)).hom.app U ((pointCompletedCoordinates D l ζ hζ hc).hom.val.app U a) =
      (pointFiniteCoordinates D l ζ hζ n).hom.val.app U
        ((purTwistZlProjection (Spec (.of D.k)) l n).hom.app U a) := by
  let S := Spec (.of D.k)
  let T : S.ProEt := ProEt.mk (𝟙 S)
  let hT := ProEt.isTerminalMkId S
  let W : (Over T)ᵒᵖ := op (Over.mk (hT.from U.unop))
  let q := Functor.isoWhiskerRight (pointRootTowerIso D l ζ hζ hc).symm
    ((ProEt.topology S).overPullback AddCommGrpCat.{u + 1} T)
  let x := (pointCompletedCoordinates D l ζ hζ hc).hom.val.app U a
  have hp := completedBasis_projection S l T q n W x
  have hx : (completedBasis S l T q).hom.val.app W x = a :=
    congrArg (fun f ↦ f.val.app U a) (pointCompletedCoordinates D l ζ hζ hc).hom_inv_id
  rw [hx] at hp
  apply (pointIso_bijective (pointFiniteCoordinates D l ζ hζ n).symm U).injective
  simp only [Iso.symm_hom]
  change (pointFiniteCoordinates D l ζ hζ n).inv.val.app U
    ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))
      (op n)).hom.app U x) = _
  rw [show (pointFiniteCoordinates D l ζ hζ n).inv.val.app U
    ((pointFiniteCoordinates D l ζ hζ n).hom.val.app U _) = _ from
      congrArg (fun f ↦ f.val.app U
        ((purTwistZlProjection (Spec (.of D.k)) l n).hom.app U a))
        (pointFiniteCoordinates D l ζ hζ n).hom_inv_id]
  have hf := congrArg (fun e ↦ e.inv.hom.app U
    ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))
      (op n)).hom.app U x)) (pointRootTowerIso_app D l ζ hζ hc n)
  exact (hp.trans hf).symm

private theorem pointFiniteCoordinates_transition
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
    (hc : ∀ n, ζ (n + 1) ^ l = ζ n) (n : ℕ)
    (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a : (purTwistFiniteRing (Spec (.of D.k)) l (n + 1)).obj.obj U) :
    (proEtaleRootsOfUnityTransition (Spec (.of D.k)) (l ^ (n + 1)) (l ^ (n + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U
        ((pointFiniteCoordinates D l ζ hζ (n + 1)).hom.val.app U a) =
      (pointFiniteCoordinates D l ζ hζ n).hom.val.app U
        ((purTwistFiniteTransition (Spec (.of D.k)) l n).hom.app U a) := by
  have h := congrArg (fun f ↦ f.hom.app U a)
    ((pointRootTowerIso D l ζ hζ hc).hom.naturality (homOfLE (Nat.le_succ n)).op)
  have hf (k : ℕ) : (pointRootTowerIso D l ζ hζ hc).hom.app (op k) =
      (SheafOfModules.toSheaf (purTwistRing (Spec (.of D.k))
        (purTwistFiniteRing (Spec (.of D.k)) l k))).map
          (pointFiniteCoordinates D l ζ hζ k).hom :=
    congrArg Iso.hom (pointRootTowerIso_app D l ζ hζ hc k)
  rw [hf n, hf (n + 1)] at h
  simp only [Functor.comp_map, proEtaleRootsOfUnityTower,
    Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h.symm

private def pointExtendCoordinates {S : Scheme.{u}}
    {R B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (α : R ⟶ B)
    {M : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ M) :
    SheafOfModules.unit (purTwistRing S B) ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M :=
  (SheafOfModules.scalarExtensionUnitIso α).symm ≪≫ (PurScalar.tensorFunctor α).mapIso e

private theorem pointExtendCoordinates_one {S : Scheme.{u}}
    {R B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (α : R ⟶ B)
    {M : SheafOfModules.{u + 1} (purTwistRing S R)}
    (e : SheafOfModules.unit (purTwistRing S R) ≅ M) (U : S.ProEtᵒᵖ) :
    (pointExtendCoordinates α e).hom.val.app U (1 : B.obj.obj U) =
      SheafOfModules.scalarExtensionSection α M U 1
        (e.hom.val.app U (1 : R.obj.obj U)) := by
  let q := SheafOfModules.scalarExtensionUnitIso α
  have h : q.hom.val.app U
      (SheafOfModules.scalarExtensionSection α (SheafOfModules.unit (purTwistRing S R))
        U 1 (1 : R.obj.obj U)) = (1 : B.obj.obj U) := by
    have ht := SheafOfModules.scalarExtensionUnitIso_tmul α U
      (1 : B.obj.obj U) (1 : R.obj.obj U)
    exact ht.trans (by rw [map_one, one_mul])
  have hq := congrArg (q.inv.val.app U) h
  have hi := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.scalarExtensionSection α (SheafOfModules.unit (purTwistRing S R))
      U 1 (1 : R.obj.obj U))) q.hom_inv_id
  have hh : q.inv.val.app U (1 : B.obj.obj U) =
      SheafOfModules.scalarExtensionSection α (SheafOfModules.unit (purTwistRing S R))
        U 1 (1 : R.obj.obj U) := hq.symm.trans hi
  change (SheafOfModules.changeOfRingsHomOfUniverses α _ e.hom).val.app U
    (q.inv.val.app U (1 : B.obj.obj U)) = _
  rw [hh]
  exact SheafOfModules.scalarExtension_map_tmul α e.hom U
    (1 : B.obj.obj U) (1 : R.obj.obj U)

private def pointIntegralCoordinates (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (g : SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l)) ≅
      purTwistZlModule S l) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E S) ≅
      purTwistIntegralModule S l E := by
  letI := integralExtensionReverse_isIso S l E
  exact pointExtendCoordinates (purTwistCompletedScalarMap S l E) g ≪≫
    asIso (integralExtensionReverse S l E)

private theorem pointIntegralCoordinates_one (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (g : SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l)) ≅
      purTwistZlModule S l) (U : S.ProEtᵒᵖ) :
    (pointIntegralCoordinates S l E g).hom.val.app U
      (1 : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U) =
      purTwistIntegralTensor S l E U 1
        (g.hom.val.app U (1 : (purTwistZlCompletion S l).obj.obj U)) := by
  change (integralExtensionReverse S l E).val.app U
    ((pointExtendCoordinates (purTwistCompletedScalarMap S l E) g).hom.val.app U 1) = _
  rw [pointExtendCoordinates_one, integralExtensionReverse_section]
  exact (purTwistIntegralAction S l E U).one_smul _

private theorem pointIntegralFinite_one (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U) :
    (integralFiniteIso S l E n).hom.val.app U
      (SheafOfModules.scalarExtensionSection
        (completedIntegralCommRingProjectionUnrestricted l E S n)
        (purTwistIntegralModule S l E) U 1 x) =
      SheafOfModules.scalarExtensionSection (purTwistIntegralQuotient S l E n)
        (purTwistIntegralOne S l E) U 1 x := by
  let φ := purTwistIntegralCompletionMap S l E
  let q := purTwistIntegralQuotient S l E n
  let p := completedIntegralCommRingProjectionUnrestricted l E S n
  let h := (purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec n
  let hq := fun U ↦ (integralQuotient_sections S l E U n).1
  have hk (U : S.ProEtᵒᵖ) : RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _)) := by
    rw [← Ideal.map_span, Ideal.span_eq]
    exact integralProjection_kernel S l E U n
  let M := purTwistIntegralModule S l E
  let a := quotientTensorAdjunction φ q p h hq hk
  let b := PurScalar.tensorAdjunction p
  let e := quotientReductionIso φ q p h hq hk M
  have hu := congrArg (fun f ↦ f.val.app U x)
    (Adjunction.unit_leftAdjointUniq_hom_app a b M)
  have hb : (b.unit.app M).val.app U x =
      SheafOfModules.scalarExtensionSection p M U 1 x := by
    exact PurScalar.tensorUnit_section p M U.unop x
  have ha : (a.unit.app M).val.app U x =
      SheafOfModules.scalarExtensionSection q ((localRes φ).obj M) U 1 x := by
    unfold a quotientTensorAdjunction PurScalar.tensorHomEquiv
    rfl
  change e.hom.val.app U ((a.unit.app M).val.app U x) =
    (b.unit.app M).val.app U x at hu
  rw [ha, hb] at hu
  have hi := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.scalarExtensionSection q ((localRes φ).obj M) U 1 x)) e.hom_inv_id
  have he : e.inv.val.app U (SheafOfModules.scalarExtensionSection p M U 1 x) =
      SheafOfModules.scalarExtensionSection q ((localRes φ).obj M) U 1 x :=
    (congrArg (e.inv.val.app U) hu).symm.trans hi
  change (SheafOfModules.changeOfRingsHomOfUniverses q _
    (integralForgetIso S l E).hom).val.app U
      (e.inv.val.app U (SheafOfModules.scalarExtensionSection p M U 1 x)) = _
  rw [he]
  exact (SheafOfModules.scalarExtension_map_tmul q
    (integralForgetIso S l E).hom U 1 x).trans
      (congrArg (SheafOfModules.scalarExtensionSection q (purTwistIntegralOne S l E) U 1)
        (integralForgetIso_hom_apply S l E U x))

private def pointFiniteIntegralCoordinates (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (e : SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E S) ≅
      purTwistIntegralModule S l E) (n : ℕ) :
    SheafOfModules.unit (integralCoefficientSheaf l E S n) ≅
      purTwistFiniteOne S l E n :=
  pointExtendCoordinates (completedIntegralCommRingProjectionUnrestricted l E S n) e ≪≫
    integralFiniteIso S l E n

private theorem pointFiniteIntegralCoordinates_one (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (e : SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E S) ≅
      purTwistIntegralModule S l E) (n : ℕ) (U : S.ProEtᵒᵖ) :
    (pointFiniteIntegralCoordinates S l E e n).hom.val.app U
      (1 : (integralCoefficientSheaf l E S n).obj.obj U) =
      SheafOfModules.scalarExtensionSection (purTwistIntegralQuotient S l E n)
        (purTwistIntegralOne S l E) U 1
          (e.hom.val.app U (1 :
            (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)) := by
  change (integralFiniteIso S l E n).hom.val.app U
    ((pointExtendCoordinates (completedIntegralCommRingProjectionUnrestricted l E S n)
      e).hom.val.app U 1) = _
  have h := pointExtendCoordinates_one
    (completedIntegralCommRingProjectionUnrestricted l E S n) e U
  exact (congrArg ((integralFiniteIso S l E n).hom.val.app U) h).trans
    (pointIntegralFinite_one S l E n U
      (e.hom.val.app U (1 :
        (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)))

/-- Compatible primitive roots give coordinates for every signed finite or completed
integral Tate line on the algebraically closed point.

Source: Deligne, La conjecture de Weil I, (2.2), pp. 280--281 and (2.13), p. 283
(blueprint: lem-pur-point-tate-root-coordinates).

Proof: (1) lem-sc-primitive-root supplies a primitive l-th root. Recursively take an
l-th root of the preceding root in the algebraically closed field. Its order is
l^(r+1): a smaller order would contradict primitivity at the preceding level.
(2) For any such sequence, lem-pur-proetale-finite-constant-sections identifies
finite constant sections with locally constant labels. The distinct powers of a
primitive root split T^(l^r)-1. For a root section, the opens where the other
linear factors are invertible are disjoint and cover; on each the section equals
one prescribed root. This constructs the inverse labels, even on the empty object.
(3) The equation ζ_(r+1)^l=ζ_r identifies the power transition with label reduction.
The sectionwise inverse limit def-pur-sheaf-inverse-limit therefore gives g, sending
1 to the root tuple e; this uses completed, rather than discrete, Z_l coefficients.
(4) Tensor with the constant integers of E. Clause 3 of
lem-pur-twist-sheaf-locally-free identifies the source with the completed coefficient
unit. At finite level the ordinary tensor maps onto the tensor over the completion;
both are locally free of rank one, so the surjection is locally multiplication by a
unit and is invertible. These give c(1) and d(n,1), normalized by e tensor 1.
(5) For degree zero use the unit. Induct on positive powers: the balanced map
(a e_r) tensor (b e_1) ↦ ab has inverse c ↦ (c e_r) tensor e_1. These formulas
pass through the sheafification of def-pur-sheaf-tensor-product.
(6) For negative degrees def-pur-sheaf-hom computes internal Hom on the localized
site. Evaluate a functional on e_r; its inverse sends b to (a e_r ↦ ab), compatibly
on every object over U. Thus the negative generator evaluates to 1 on e_r.
(7) At the terminal object the finite constant sections are the coefficient ring
by lem-pur-proetale-finite-constant-sections. For integral coefficients apply
lem-pur-connected-adic-integral-basis to the identity extension E/E on Spec k.
Evaluate the signed coordinates there to obtain exactly B e_m in every degree. -/
theorem point_tate_root_coordinates (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (∃ ζ : ℕ → D.k,
      (∀ n : ℕ, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) ∧
      (∀ n : ℕ, ζ (n + 1) ^ l = ζ n)) ∧
    ∀ ζ : ℕ → D.k,
      (∀ n : ℕ, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) →
      (∀ n : ℕ, ζ (n + 1) ^ l = ζ n) →
      HasPurPointRootCoordinates D l E ζ := by
  classical
  refine ⟨pointRootTower D l hl, ?_⟩
  intro ζ hζ hc
  let S := Spec (.of D.k)
  let f := pointFiniteCoordinates D l ζ hζ
  let g := pointCompletedCoordinates D l ζ hζ hc
  let e := pointIntegralCoordinates S l E g
  let en := pointFiniteIntegralCoordinates S l E e
  let c := pointSignedCoordinates
    (R := completedIntegralCommRingSheafUnrestricted l E S) e
  let d := fun n ↦ pointSignedCoordinates
    (R := integralCoefficientCommRingSheaf l E S n) (en n)
  refine ⟨f, g, c, d, pointFiniteCoordinates_formula D l ζ hζ,
    pointFiniteCoordinates_transition D l ζ hζ hc,
    pointCompletedCoordinates_projection D l ζ hζ hc,
    pointIntegralCoordinates_one S l E g,
    pointFiniteIntegralCoordinates_one S l E e,
    pointSignedCoordinates_spec
      (R := completedIntegralCommRingSheafUnrestricted l E S) e,
    fun n ↦ pointSignedCoordinates_spec
      (R := integralCoefficientCommRingSheaf l E S n) (en n), ?_, ?_⟩
  · obtain ⟨ι, _, hi, _⟩ := connected_adic_integral_basis l E E (AlgHom.id ℚ_[l] E) S
    exact ⟨ι, hi, fun m ↦ (pointIso_bijective (c m) _).comp ι.bijective⟩
  · intro n
    let ι := finiteConstantEquiv l E S n
    exact ⟨ι, fun _ ↦ rfl, fun m ↦ (pointIso_bijective (d n m) _).comp ι.bijective⟩

end WeilConjectures
