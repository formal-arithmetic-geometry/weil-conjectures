/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Sheaf.Paper.FibreFunctorBasepointTransportData
import Sheaf.Paper.LisseRationalScalarFiberMaps
/-! # Rationalization of integral fibre paths

Source: Deligne, Weil II (1.1.1) c), p.147.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
private lemma fractionTensorPure {R B : Type*} [CommRing R] [IsDomain R] [Field B]
    [Algebra R B] [IsFractionRing R B]
    (M : Type*) [AddCommGroup M] [Module R M] (z : B ⊗[R] M) :
    ∃ a : B, ∃ m : M, z = a ⊗ₜ[R] m := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R)
    (TensorProduct.mk R B M 1) z
  have hs0 : algebraMap R B s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
  refine ⟨(algebraMap R B s)⁻¹, m, ?_⟩
  rw [Submonoid.smul_def, ← algebraMap_smul B] at hs
  have h : (algebraMap R B s) • z = (1 : B) ⊗ₜ[R] m := hs
  have hv := congrArg (fun x : B ⊗[R] M ↦ (algebraMap R B s)⁻¹ • x) h
  simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one] using hv

private def rationalPathComponent
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z)
    (F : LisseRationalSheaf l E Y) :
    (lisseRationalFiberFunctor l E Y y).obj F ≅
      (lisseRationalFiberFunctor l E Y z).obj F :=
  eqToIso (lisseRationalFiberFunctor_obj l E Y y F) ≪≫
    ((t.app F.integral).toLinearEquiv.baseChange
      (Padic.coefficientExtensionIntegers l E) E _ _).toModuleIso ≪≫
      (eqToIso (lisseRationalFiberFunctor_obj l E Y z F)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem rationalPathComponent_naturality
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z)
    (F H : LisseRationalSheaf l E Y) (f : F ⟶ H) :
    (lisseRationalFiberFunctor l E Y y).map f ≫
        (rationalPathComponent l E Y y z t H).hom =
      (rationalPathComponent l E Y y z t F).hom ≫
        (lisseRationalFiberFunctor l E Y z).map f := by
  have hy : IsLisseRationalFiberFunctor Y y l E (lisseRationalFiberFunctor l E Y y)
      (lisseRationalFiberFunctor_obj l E Y y) :=
    (lisseRationalFiberFunctor_exists l E Y y).choose_spec.choose_spec
  have hz : IsLisseRationalFiberFunctor Y z l E (lisseRationalFiberFunctor l E Y z)
      (lisseRationalFiberFunctor_obj l E Y z) :=
    (lisseRationalFiberFunctor_exists l E Y z).choose_spec.choose_spec
  have : IsFractionRing (Padic.coefficientExtensionIntegers l E) E :=
    (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.2.2.2.2.2.2.1
  obtain ⟨a, f, rfl⟩ := fractionTensorPure (F.integral ⟶ H.integral) f
  erw [hy, hz]
  simp only [rationalPathComponent, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv, Category.assoc]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  simp only [Category.assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  change (LinearMap.baseChange E (t.hom.app H.integral).hom).comp
      (a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom) =
    (a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y z).map f).hom).comp
      (LinearMap.baseChange E (t.hom.app F.integral).hom)
  rw [LinearMap.comp_smul, LinearMap.smul_comp, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp]
  have hn := congrArg ModuleCat.Hom.hom (t.hom.naturality f)
  exact congrArg (fun f ↦ a • LinearMap.baseChange E f) hn
private def rationalPathIso
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z) :
    lisseRationalFiberFunctor l E Y y ≅ lisseRationalFiberFunctor l E Y z :=
  NatIso.ofComponents (rationalPathComponent l E Y y z t)
    (fun f ↦ rationalPathComponent_naturality l E Y y z t _ _ f)

private theorem rationalPathIso_evaluation
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z)
    (F : LisseRationalSheaf l E Y) (a : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
      ((rationalPathIso l E Y y z t).hom.app F
        (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
          (TensorProduct.tmul _ a x))) =
      TensorProduct.tmul _ a (t.hom.app F.integral x) := by
  dsimp only [rationalPathIso, NatIso.ofComponents, rationalPathComponent,
    Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, eqToHom_trans_assoc]
  rfl

private theorem rationalPathIso_apply
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z)
    (F : LisseRationalSheaf l E Y) (a : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    (rationalPathIso l E Y y z t).hom.app F
      (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
        (TensorProduct.tmul _ a x)) =
      eqToHom (lisseRationalFiberFunctor_obj l E Y z F).symm
        (TensorProduct.tmul _ a (t.hom.app F.integral x)) := by
  apply ((eqToIso (lisseRationalFiberFunctor_obj l E Y z F)).toLinearEquiv).injective
  change eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
      ((rationalPathIso l E Y y z t).hom.app F
        (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm (a ⊗ₜ[_] x))) = _
  rw [rationalPathIso_evaluation]
  exact ((eqToIso (lisseRationalFiberFunctor_obj l E Y z F)).toLinearEquiv
    |>.apply_symm_apply _).symm

private theorem rationalPathIso_inv_apply
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z)
    (F : LisseRationalSheaf l E Y) (a : E)
    (x : (lisseIntegralFiberFunctor l E Y z).obj F.integral) :
    (rationalPathIso l E Y y z t).inv.app F
      (eqToHom (lisseRationalFiberFunctor_obj l E Y z F).symm
        (TensorProduct.tmul _ a x)) =
      eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
        (TensorProduct.tmul _ a (t.inv.app F.integral x)) := by
  dsimp only [rationalPathIso, NatIso.ofComponents, rationalPathComponent,
    Iso.trans_inv, eqToIso.hom, Iso.symm_inv, eqToIso.inv]
  simp only [← ConcreteCategory.comp_apply, Category.assoc,
    eqToHom_refl, Category.id_comp, eqToHom_trans_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rationalPathIso_ext
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : lisseIntegralFiberFunctor l E Y y ≅ lisseIntegralFiberFunctor l E Y z)
    (s : lisseRationalFiberFunctor l E Y y ≅ lisseRationalFiberFunctor l E Y z)
    (h : ∀ (F : LisseRationalSheaf l E Y) (a : E)
      (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral),
      eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
        (s.hom.app F
          (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
            (TensorProduct.tmul _ a x))) =
        TensorProduct.tmul _ a (t.hom.app F.integral x)) :
    rationalPathIso l E Y y z t = s := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ((eqToIso (lisseRationalFiberFunctor_obj l E Y z F)).toLinearEquiv).injective
  obtain ⟨w, rfl⟩ :=
    ((eqToIso (lisseRationalFiberFunctor_obj l E Y y F)).toLinearEquiv.symm).surjective x
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact (rationalPathIso_evaluation l E Y y z t F a x).trans (h F a x).symm
  | add x x' hx hx' => simp only [map_add]; exact congrArg₂ (· + ·) hx hx'

/-- Rationalize a natural integral path, preserving its four path laws and its formula
on pure tensors. Source: Weil II (1.1.1) c), p.147.
(blueprint: new-e5-rational-fibre-path-construction).
Proof: base-change each integral component to E and transport through the recorded
rational-fibre object identifications. Every rational morphism is a pure tensor after
clearing one denominator, so base-change of integral naturality proves naturality.
The formula on pure tensors determines a linear map. Test each path law there and use
the corresponding integral law, giving identity, composition, conjugation and change. -/
theorem rational_fibre_path_family_exists
    (d : LinearFibrePathFamily Y (LisseIntegralSheaf l E Y)
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ lisseIntegralFiberFunctor l E Y y)) :
    ∃ r : LinearFibrePathFamily Y (LisseRationalSheaf l E Y) E
        (fun y ↦ lisseRationalFiberFunctor l E Y y),
      ∀ {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
        {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
        (t : flcFiber y ≅ flcFiber z) (F : LisseRationalSheaf l E Y) (a : E)
        (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral),
        eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
          ((r.map y z t).hom.app F
            (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
              (TensorProduct.tmul _ a x))) =
          TensorProduct.tmul _ a ((d.map y z t).hom.app F.integral x) := by
  let map := fun {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) ↦ rationalPathIso l E Y y z (d.map y z t)
  refine ⟨{
    map := @map
    identity := ?_
    composition := ?_
    conjugation := ?_
    «change» := ?_ }, ?_⟩
  · intro Ω _ _ y
    apply rationalPathIso_ext l E Y y y
    intro F a x
    rw [d.identity]
    simp only [Iso.refl_hom, NatTrans.id_app, ModuleCat.id_apply]
    exact (eqToIso (lisseRationalFiberFunctor_obj l E Y y F)).toLinearEquiv
      |>.apply_symm_apply _
  · intro Ωy _ _ y Ωz _ _ z Ωq _ _ q t s
    apply rationalPathIso_ext l E Y y q
    intro F a x
    change eqToHom (lisseRationalFiberFunctor_obj l E Y q F)
      ((rationalPathIso l E Y z q (d.map z q s)).hom.app F
      ((rationalPathIso l E Y y z (d.map y z t)).hom.app F 
        (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm (a ⊗ₜ[_] x)))) = _
    rw [rationalPathIso_apply, rationalPathIso_evaluation, d.composition]
    rfl
  · intro Ωy _ _ y Ωz _ _ z t g
    apply rationalPathIso_ext l E Y z z
    intro F a x
    change eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
      ((rationalPathIso l E Y y z (d.map y z t)).hom.app F
      ((rationalPathIso l E Y y y (d.map y y g)).hom.app F
        ((rationalPathIso l E Y y z (d.map y z t)).inv.app F 
        (eqToHom (lisseRationalFiberFunctor_obj l E Y z F).symm (a ⊗ₜ[_] x))))) = _
    rw [rationalPathIso_inv_apply, rationalPathIso_apply, rationalPathIso_evaluation,
      d.conjugation]
    rfl
  · intro Ωy _ _ y Ωz _ _ z t s
    apply rationalPathIso_ext l E Y y z
    intro F a x
    change eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
      ((rationalPathIso l E Y z z (d.map z z (t.symm ≪≫ s))).hom.app F
      ((rationalPathIso l E Y y z (d.map y z t)).hom.app F 
        (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm (a ⊗ₜ[_] x)))) = _
    rw [rationalPathIso_apply, rationalPathIso_evaluation, d.change y z t s]
    rfl
  · intro Ωy _ _ y Ωz _ _ z t F a x
    exact rationalPathIso_evaluation l E Y y z (d.map y z t) F a x

/-- The rational family determined by the integral family and its pure-tensor formula.
Source: Weil II (1.1.1) c), p.147.
(blueprint: new-e5-rational-fibre-path-construction). -/
@[irreducible]
def rationalFibrePathFamily
    (d : LinearFibrePathFamily Y (LisseIntegralSheaf l E Y)
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ lisseIntegralFiberFunctor l E Y y)) :
    LinearFibrePathFamily Y (LisseRationalSheaf l E Y) E
      (fun y ↦ lisseRationalFiberFunctor l E Y y) :=
  (rational_fibre_path_family_exists l E Y d).choose

/-- The selected rational family has the prescribed pure-tensor formula.
Source: Weil II (1.1.1) c), p.147.
(blueprint: new-e5-rational-fibre-path-construction).
Proof: the formula is the specification of its defining existence theorem. -/
theorem rationalFibrePathFamily_evaluation
    (d : LinearFibrePathFamily Y (LisseIntegralSheaf l E Y)
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ lisseIntegralFiberFunctor l E Y y))
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (F : LisseRationalSheaf l E Y) (a : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    eqToHom (lisseRationalFiberFunctor_obj l E Y z F)
      (((rationalFibrePathFamily l E Y d).map y z t).hom.app F
        (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
          (TensorProduct.tmul _ a x))) =
      TensorProduct.tmul _ a ((d.map y z t).hom.app F.integral x) := by
  unfold rationalFibrePathFamily
  exact (rational_fibre_path_family_exists l E Y d).choose_spec y z t F a x

/-- On each object the rational path is base change of the integral path.
Source: Weil II (1.1.1) c), p.147.
(blueprint: new-e5-rational-fibre-path-construction).
Proof: the pure-tensor formula uniquely determines each component; compare with the
explicit base-changed integral isomorphism. -/
theorem rationalFibrePathFamily_component
    (d : LinearFibrePathFamily Y (LisseIntegralSheaf l E Y)
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ lisseIntegralFiberFunctor l E Y y))
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (F : LisseRationalSheaf l E Y) :
    ((rationalFibrePathFamily l E Y d).map y z t).hom.app F =
      eqToHom (lisseRationalFiberFunctor_obj l E Y y F) ≫
        ModuleCat.ofHom (LinearMap.baseChange E (((d.map y z t).hom.app F.integral).hom)) ≫
          eqToHom (lisseRationalFiberFunctor_obj l E Y z F).symm := by
  have hh := rationalPathIso_ext l E Y y z (d.map y z t)
    ((rationalFibrePathFamily l E Y d).map y z t)
    (rationalFibrePathFamily_evaluation l E Y d y z t)
  rw [← hh]
  rfl

/-- The rational path on a pure tensor, before applying the target object transport.
Source: Weil II (1.1.1) c), p.147.
(blueprint: new-e5-rational-fibre-path-construction).
Proof: cancel the target object isomorphism in the evaluation formula. -/
theorem rationalFibrePathFamily_apply
    (d : LinearFibrePathFamily Y (LisseIntegralSheaf l E Y)
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ lisseIntegralFiberFunctor l E Y y))
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (F : LisseRationalSheaf l E Y) (a : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    ((rationalFibrePathFamily l E Y d).map y z t).hom.app F
      (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm (a ⊗ₜ[_] x)) =
        eqToHom (lisseRationalFiberFunctor_obj l E Y z F).symm
          (a ⊗ₜ[_] ((d.map y z t).hom.app F.integral x)) := by
  have hh := rationalPathIso_ext l E Y y z (d.map y z t)
    ((rationalFibrePathFamily l E Y d).map y z t)
    (rationalFibrePathFamily_evaluation l E Y d y z t)
  rw [← hh]
  exact rationalPathIso_apply l E Y y z (d.map y z t) F a x

end AlgebraicGeometry.Scheme
