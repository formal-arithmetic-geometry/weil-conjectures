/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Sheaf.Paper.GaloisLisseRepresentations
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import Sheaf.Paper.LisseModuleSheaves
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Mathlib.CategoryTheory.Conj
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.CategoryTheory.Galois.ExactFiniteGsetsForgetful

/-! # Etale paths and transport of finite and adic stalks

Source: Stacks Project, 0BND (2), 0BN5; Deligne, Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport).

## Main definitions

* `LinearFibrePathFamily`: natural linear path maps and their functoriality laws.
* `FiniteFibrePathTransport`: evaluation on underlying FLC sheaves and scalar compatibility.
* `AdicFibrePathTransport`: integral, rational and algebraic path maps, characterized at
  finite levels and on pure tensors, with canonical scalar comparisons.

## Main statements

* `fibre_functor_basepoint_transport`: existence of paths, topological conjugation and
  transport at all finite and adic coefficient levels.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

/-- The module stalk functor restricted to lisse sheaves. Source: Stacks 0BND (2),
0DV5 (blueprint: lem-wf-fibre-functor-basepoint-transport). -/
abbrev pathModuleFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R] :=
  ObjectProperty.ι (IsLisseModuleSheaf (Y := Y) (Λ := R)) ⋙
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)

/-- The canonical comparison with the underlying set stalk, including the universe lift.
Source: Stacks 0DV5; Weil II (1.1.1) b)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def pathUnderlyingStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (((pointSmallEtale y).ulift.{u + 1}.sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).symm.app F ≪≫
      ((pointSmallEtale y).uliftSheafFiberIso (Type (u + 1))).app
        (galoisUnderlyingSetSheaf R F)).toEquiv

/-- The canonical balanced scalar-extension stalk comparison. Source: Stacks 03EL, 04FM
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def pathScalarStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  ((pointSmallEtale y).ulift.{u + 1}.presheafFiberCompIso
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm.app F.obj ≪≫
      ((pointSmallEtale y).ulift.{u + 1}.presheafToSheafCompSheafFiberIso
        (ModuleCat.{u + 1} S)).symm.app
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)

/-- A family of natural linear path maps, with identity, composition, loop conjugation
and change-of-path laws. The loop action is evaluation of the same family at a loop.
Source: Stacks 0BND (2), 0BN5; Weil II (1.1.1) b)-d)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
structure LinearFibrePathFamily (Y : Scheme.{u})
    (C : Type v) [Category.{w} C] (R : Type (u + 1)) [Ring R]
    (T : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω],
      (Spec (.of Ω) ⟶ Y) → C ⥤ ModuleCat.{u + 1} R) where
  map : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y), (flcFiber y ≅ flcFiber z) → (T y ≅ T z)
  identity : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y), map y y (Iso.refl _) = Iso.refl (T y)
  composition : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    {Ωq : Type u} [Field Ωq] [IsAlgClosed Ωq]
    (q : Spec (.of Ωq) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (s : flcFiber z ≅ flcFiber q),
    map y q (t ≪≫ s) = map y z t ≪≫ map z q s
  conjugation : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (g : Aut (flcFiber y)),
    map z z (t.conjAut g) = (map y z t).symm ≪≫ map y y g ≪≫ map y z t
  change : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t s : flcFiber y ≅ flcFiber z),
    map y z s = map y z t ≪≫ map z z (t.symm ≪≫ s)

/-- Finite coefficient path maps are the evaluation of the set path, through the
canonical forgetful-stalk comparison; they commute with arbitrary finite-ring extensions.
Source: Stacks 0BND (2), 0BN5; Weil II (1.1.1) b)-d)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
structure FiniteFibrePathTransport (Y : Scheme.{u}) where
  linear : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
    LinearFibrePathFamily Y (LisseModuleSheafCategory Y R) R
      (fun y ↦ pathModuleFiber y R)
  evaluation : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R] [Finite R]
    (F : LisseModuleSheafCategory Y R),
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj),
      ∀ x : (pathModuleFiber y R).obj F,
      pathUnderlyingStalk z R F.obj (((linear R).map y z t).hom.app F x) =
        t.hom.app (galoisUnderlyingFLC R F.obj h) (pathUnderlyingStalk y R F.obj x)
  scalar : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R S : Type (u + 1))
    [Ring R] [Finite R] [Ring S] [Finite S] (a : R →+* S)
    (F : LisseModuleSheafCategory Y R) (H : LisseModuleSheafCategory Y S)
    (e : H.obj ≅ (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology a).obj F.obj),
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map
        (((linear R).map y z t).hom.app F) ≫ (pathScalarStalk z a F.obj).hom ≫
      ((pointSmallEtale z).ulift.{u + 1}.sheafFiber).map e.inv =
      (pathScalarStalk y a F.obj).hom ≫
        ((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map e.inv ≫
          ((linear S).map y z t).hom.app H

/-- Expose the existing scalar extension's prescribed finite-level isomorphism through
its irreducible functor wrapper. This is the existing data, with a definitional transport.
Source: Weil II (1.1.1) d) (blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def pathIntegralScalarLevelIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (E L : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)
    (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m) ≅
      lisseIntegralScalarLevel l E Y L ι F m := by
  unfold lisseIntegralScalarExtension
  exact (lisseIntegralScalarExtensionData l E Y L ι).levelIso F m

/-- Natural linear path maps at the integral, rational and algebraic coefficient levels.
Their finite-level and tensor characterizations are the evaluation predicates below.
Source: Weil II (1.1.1) b)-d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
structure AdicFibrePathData (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] where
  integral : ∀ E : Padic.FiniteCoefficientFields l Q,
    LinearFibrePathFamily Y (LisseIntegralSheaf l E.val Y)
      (Padic.coefficientExtensionIntegers l E.val) (fun y ↦ lisseIntegralFiberFunctor l E.val Y y)
  rational : ∀ E : Padic.FiniteCoefficientFields l Q,
    LinearFibrePathFamily Y (LisseRationalSheaf l E.val Y) E.val
      (fun y ↦ lisseRationalFiberFunctor l E.val Y y)
  algebraic : LinearFibrePathFamily Y (LisseAlgebraicSheaf l Y Q) Q
    (fun y ↦ lisseAlgebraicFiberFunctor l Y y Q)

/-- The prescribed integral_evaluation formula for an adic path family.
Source: Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicIntegralPathEvaluation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibrePathData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E : Padic.FiniteCoefficientFields l Q)
    (F : LisseIntegralSheaf l E.val Y) (n : ℕ),
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
      (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))),
      ∀ x : (lisseIntegralFiberFunctor l E.val Y y).obj F,
      pathUnderlyingStalk z (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))
        (limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber) (op n)
          (((d.integral E).map y z t).hom.app F x)) =
      t.hom.app (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
        (F.obj.obj (op n)) h)
        (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))
          (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) x))

/-- The prescribed rational_evaluation formula for an adic path family.
Source: Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicRationalPathEvaluation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibrePathData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E : Padic.FiniteCoefficientFields l Q)
    (F : LisseRationalSheaf l E.val Y) (a : E.val)
    (x : (lisseIntegralFiberFunctor l E.val Y y).obj F.integral),
    eqToHom (lisseRationalFiberFunctor_obj l E.val Y z F)
      (((d.rational E).map y z t).hom.app F
        (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F).symm
          (TensorProduct.tmul _ a x))) =
      TensorProduct.tmul _ a (((d.integral E).map y z t).hom.app F.integral x)

/-- The prescribed algebraic_evaluation formula for an adic path family.
Source: Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicAlgebraicPathEvaluation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibrePathData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E : Padic.FiniteCoefficientFields l Q)
    (F : LisseRationalSheaf l E.val Y) (a : Q)
    (x : (lisseRationalFiberFunctor l E.val Y y).obj F),
    eqToHom (lisseAlgebraicFiber_ofModel l Y z Q E F)
      (eqToHom (lisseAlgebraicFiberFunctor_obj l Y z Q (lisseAlgebraicOfModel l Y Q E F))
        ((d.algebraic.map y z t).hom.app (lisseAlgebraicOfModel l Y Q E F)
          (eqToHom (lisseAlgebraicFiberFunctor_obj l Y y Q
              (lisseAlgebraicOfModel l Y Q E F)).symm
            (eqToHom (lisseAlgebraicFiber_ofModel l Y y Q E F).symm
              (TensorProduct.tmul _ a
                (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F) x)))))) =
      TensorProduct.tmul _ a
        (eqToHom (lisseRationalFiberFunctor_obj l E.val Y z F)
          (((d.rational E).map y z t).hom.app F x))

/-- The two coefficient-extension fibre comparisons, before their characterizing formulas.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
structure AdicFibreScalarData (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    extends AdicFibrePathData l Y Q where
  integralScalar : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L),
    lisseIntegralFiberFunctor l E.val Y y ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1}
      (lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h)) ≅
    lisseIntegralScalarExtension l E.val Y L.val (IntermediateField.inclusion h) ⋙
      lisseIntegralFiberFunctor l L.val Y y
  rationalScalar : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) [Algebra E.val L.val]
    (_ha : algebraMap E.val L.val = (IntermediateField.inclusion h).toRingHom),
    lisseRationalFiberFunctor l E.val Y y ⋙ ModuleCat.extendScalars (algebraMap E.val L.val) ≅
      lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion h) ⋙
        lisseRationalFiberFunctor l L.val Y y

/-- The integralScalar_germ compatibility of the prescribed coefficient comparisons.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicIntegralScalarGerm (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibreScalarData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)
    (F : LisseIntegralSheaf l E.val Y) (m : ℕ) (U : Y.Etale)
    (ξ : (pointSmallEtale y).fiber.obj U) (b : Padic.coefficientExtensionIntegers l L.val)
    (x : (lisseIntegralFiberFunctor l E.val Y y).obj F)
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E.val L.val
      (IntermediateField.inclusion h) m))).obj.obj (op U)),
    limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)
      (op (lisseScalarSourceIndex l E.val L.val (IntermediateField.inclusion h) m)) x =
        (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩
          (F.obj.obj (op (lisseScalarSourceIndex l E.val L.val
            (IntermediateField.inclusion h) m))).obj s →
    ((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map
      (pathIntegralScalarLevelIso l Y E.val L.val
        (IntermediateField.inclusion h) F m).hom
      (limit.π (((lisseIntegralScalarExtension l E.val Y L.val
        (IntermediateField.inclusion h)).obj F).obj ⋙
          (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op m)
        ((d.integralScalar y E L h).hom.app F
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
            (lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h)) _ b x))) =
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩
        (lisseIntegralScalarLevel l E.val Y L.val (IntermediateField.inclusion h) F m).obj
        (lisseIntegralScalarGenerator l E.val Y L.val (IntermediateField.inclusion h) F m U
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L.val (m + 1)) b) s)

/-- The integralScalar_path compatibility of the prescribed coefficient comparisons.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicIntegralScalarPath (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibreScalarData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)
    (F : LisseIntegralSheaf l E.val Y),
    (ModuleCat.ringExtendScalars.{u + 1, u + 1}
      (lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h))).map
        (((d.integral E).map y z t).hom.app F) ≫ (d.integralScalar z E L h).hom.app F =
      (d.integralScalar y E L h).hom.app F ≫ ((d.integral L).map y z t).hom.app
        ((lisseIntegralScalarExtension l E.val Y L.val (IntermediateField.inclusion h)).obj F)

/-- The rationalScalar_tensor compatibility of the prescribed coefficient comparisons.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicRationalScalarTensor (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibreScalarData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) [Algebra E.val L.val]
    (ha : algebraMap E.val L.val = (IntermediateField.inclusion h).toRingHom)
    (F : LisseRationalSheaf l E.val Y) (a : L.val) (b : E.val)
    (x : (lisseIntegralFiberFunctor l E.val Y y).obj F.integral),
    eqToHom (lisseRationalFiberFunctor_obj l L.val Y y
      ((lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion h)).obj F))
      ((d.rationalScalar y E L h ha).hom.app F
        (TensorProduct.tmul _ a
          (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F).symm
            (TensorProduct.tmul _ b x)))) =
      TensorProduct.tmul _ (a * (IntermediateField.inclusion h) b)
        ((d.integralScalar y E L h).hom.app F.integral
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
            (lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h)) _ 1 x))

/-- The rationalScalar_path compatibility of the prescribed coefficient comparisons.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
def adicRationalScalarPath (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : AdicFibreScalarData l Y Q) : Prop :=
  ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)
    [Algebra E.val L.val]
    (ha : algebraMap E.val L.val = (IntermediateField.inclusion h).toRingHom)
    (F : LisseRationalSheaf l E.val Y),
    (ModuleCat.extendScalars (algebraMap E.val L.val)).map
      (((d.rational E).map y z t).hom.app F) ≫ (d.rationalScalar z E L h ha).hom.app F =
      (d.rationalScalar y E L h ha).hom.app F ≫ ((d.rational L).map y z t).hom.app
        ((lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion h)).obj F)

/-- The canonical adic path maps and all their scalar-extension compatibilities.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: lem-wf-fibre-functor-basepoint-transport). -/
structure AdicFibrePathTransport (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    extends AdicFibreScalarData l Y Q where
  integral_evaluation : adicIntegralPathEvaluation l Y Q toAdicFibrePathData
  rational_evaluation : adicRationalPathEvaluation l Y Q toAdicFibrePathData
  algebraic_evaluation : adicAlgebraicPathEvaluation l Y Q toAdicFibrePathData
  integralScalar_germ : adicIntegralScalarGerm l Y Q toAdicFibreScalarData
  integralScalar_path : adicIntegralScalarPath l Y Q toAdicFibreScalarData
  rationalScalar_tensor : adicRationalScalarTensor l Y Q toAdicFibreScalarData
  rationalScalar_path : adicRationalScalarPath l Y Q toAdicFibreScalarData

/-- Any two geometric fibre functors have a path; every path conjugates their topological
automorphism groups, and these paths transport finite and all three adic coefficient levels.
Source: Stacks 0BND (2), 0BN5 and Deligne, Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport).

Proof plan, following the ten steps of the node:
1. Use thm-galois-fundamental to identify FLC with finite continuous fundamental-group sets.
   The other stalk is exact and finite-valued by lem-fet-galois-category,
   thm-galois-lc-etale and lem-galois-equivalence-preserves-limits.
2. Apply lem-wf-exact-finite-gsets-forgetful and compose with the equivalence counit to
   construct a natural path, without independent choices of stalk points.
3. Conjugation by a path is a group isomorphism. In each evaluation coordinate it is
   conjugation between finite discrete permutation groups, hence it and its inverse are
   continuous. Replacing t by t' conjugates by the target loop t' t inverse.
4. Naturality with projections, addition and each scalar multiplication makes evaluation
   linear. Naturality for module arrows gives the natural linear isomorphisms; evaluating
   identity and composite paths gives the corresponding laws. Evaluating loops gives
   exactly the finite action stipulated in cor-galois-lisse-representations (1).
5. Apply naturality to x mapped to b tensor x. The stalk formula of
   lem-pod-lisse-tensor-and-scalar-extension gives finite-ring compatibility, including
   noncommutative rings and successive scalar maps.
6. At integral level act on every inverse-limit coordinate. Naturality with transitions
   preserves compatibility, and the inverse path gives the inverse. The same calculation
   gives integral linearity and naturality, with def-pod-lisse-adic-fibre-functors.
7. For ramified E into L use the prescribed ceiling reindexing. At each target level both
   scalar routes send b tensor x to b tensor t(x). This gives the normalized integral
   scalar comparison and its path square; equality of projections proves equality.
8. Rationalize integral maps. Every rational arrow is a sum of pure tensors, so integral
   naturality gives naturality for every rational arrow, including changes of lattice.
   Tensoring also gives the rational scalar formula and compatibility square.
9. Extend a rational model to the algebraic closure. Morphisms are represented over a
   common finite coefficient field; scalar compatibility and rational naturality make
   their squares commute and make the construction descend to the coefficient colimit.
10. Evaluate c_t(g) = t g t inverse and t' = a t at finite levels, pass to inverse limits,
    and then extend coefficients. These are the two conjugation and change-of-path laws
    in LinearFibrePathFamily. The finite-level normalization and the tensor formulas identify
    the loop actions with cor-galois-lisse-representations (2), rather than arbitrary actions.
-/
theorem fibre_functor_basepoint_transport {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y) :
    Nonempty (flcFiber y ≅ flcFiber z) ∧
    (∀ t : flcFiber y ≅ flcFiber z,
      ∃ c : Aut (flcFiber y) ≃ₜ* Aut (flcFiber z),
        c.toMulEquiv = t.conjAut ∧
        ∀ (s : flcFiber y ≅ flcFiber z) (g : Aut (flcFiber y)),
          s.conjAut g = (t.symm ≪≫ s).symm ≪≫ c g ≪≫ (t.symm ≪≫ s)) ∧
    Nonempty (FiniteFibrePathTransport Y) ∧
    ∀ (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
      [∀ x : Y, Invertible (l : Y.residueField x)]
      (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q],
      Nonempty (AdicFibrePathTransport l Y Q) := by
  sorry

end AlgebraicGeometry.Scheme
