/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Sheaf.Paper.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import Sheaf.Paper.LisseModuleSheaves
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Mathlib.CategoryTheory.Conj
public import Sheaf.Paper.LisseAdicFiberFunctors

/-! # Interfaces for finite and adic fibre path transport

These are the unchanged stalks, comparisons and transport records formerly defined in
`FibreFunctorBasepointTransport`. Keeping the interface below its existence theorems lets
finite transport and its adic extension have independent proofs.
Source: Stacks 0BND (2), 0BN5; Weil II (1.1.1) b)-d).
(blueprint: new-e5-fibre-path-transport-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

/-- The module stalk functor restricted to lisse sheaves. Source: Stacks 0BND (2),
0DV5 (blueprint: new-e5-fibre-path-transport-data). -/
abbrev pathModuleFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R] :=
  ObjectProperty.ι (IsLisseModuleSheaf (Y := Y) (Λ := R)) ⋙
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)

/-- The canonical comparison with the underlying set stalk, including the universe lift.
Source: Stacks 0DV5; Weil II (1.1.1) b)
(blueprint: new-e5-fibre-path-transport-data). -/
def pathUnderlyingStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (((pointSmallEtale y).ulift.{u + 1}.sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).symm.app F ≪≫
      ((pointSmallEtale y).uliftSheafFiberIso (Type (u + 1))).app
        (galoisUnderlyingSetSheaf R F)).toEquiv

/-- The canonical balanced scalar-extension stalk comparison. Source: Stacks 03EL, 04FM
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
def pathScalarStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F) ≅
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} S)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F) :=
  letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  ((pointSmallEtale y).ulift.{u + 1}.presheafFiberCompIso
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm.app F.obj ≪≫
      ((pointSmallEtale y).ulift.{u + 1}.presheafToSheafCompSheafFiberIso
        (ModuleCat.{u + 1} S)).symm.app
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A family of natural linear path maps, with identity, composition, loop conjugation
and change-of-path laws. The loop action is evaluation of the same family at a loop.
Source: Stacks 0BND (2), 0BN5; Weil II (1.1.1) b)-d)
(blueprint: new-e5-fibre-path-transport-data). -/
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

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Finite coefficient path maps are the evaluation of the set path, through the
canonical forgetful-stalk comparison; they commute with arbitrary finite-ring extensions.
Source: Stacks 0BND (2), 0BN5; Weil II (1.1.1) b)-d)
(blueprint: new-e5-fibre-path-transport-data). -/
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
Source: Weil II (1.1.1) d) (blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
def pathIntegralScalarLevelIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (E L : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)
    (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m) ≅
      lisseIntegralScalarLevel l E Y L ι F m := by
  unfold lisseIntegralScalarExtension
  exact (lisseIntegralScalarExtensionData l E Y L ι).levelIso F m

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Natural linear path maps at the integral, rational and algebraic coefficient levels.
Their finite-level and tensor characterizations are the evaluation predicates below.
Source: Weil II (1.1.1) b)-d), pp.146-147; Stacks 0BND (2)
(blueprint: new-e5-fibre-path-transport-data). -/
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The two coefficient-extension fibre comparisons, before their characterizing formulas.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: new-e5-fibre-path-transport-data). -/
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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
(blueprint: new-e5-fibre-path-transport-data). -/
@[irreducible]
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

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The canonical adic path maps and all their scalar-extension compatibilities.
Source: Weil II (1.1.1) d), pp.146-147; Stacks 0BND (2)
(blueprint: new-e5-fibre-path-transport-data). -/
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

end AlgebraicGeometry.Scheme
