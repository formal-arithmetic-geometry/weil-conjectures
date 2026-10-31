/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorProductFrameExt
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealizationPure
import WeilConjectures.SixFunctors.Supporting.Tensor.ProEtaleTensorPairNaturality
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Normalized ordinary finite signed product maps

Source: finite-reduction proof Step 2; Stacks Project, Modules on Sites,
Sections 03EK and 04TT.
(blueprint: lem-route-exists-finite-tensor-sheaf-product-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  SheafOfModules.unit PresheafOfModules.restrictOver
  WeilConjectures.coefficientTwistLine SheafOfModules.scalarTensorPower
  SheafOfModules.signedLinePower
attribute [local instance 50000]
  SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory

private def tensorPresentation (T : Scheme.{u})
    [EssentiallySmall.{u + 1} T.ProEt]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M N : proEtaleRingModules T R) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N).obj M ≅
      ((proEtaleOrdinaryTensor T R).obj M).obj N :=
  (PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (𝟙 _)).mapIso
    ((SheafOfModules.siteTensorRightIso.{u + 1, u, u + 1} R N.val).app M.val) ≪≫
      (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M N).symm

private theorem tensorPresentation_pure (T : Scheme.{u})
    [EssentiallySmall.{u + 1} T.ProEt]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M N : proEtaleRingModules T R) (W : T.ProEtᵒᵖ)
    (x : M.val.obj W) (y : N.val.obj W) :
    (tensorPresentation T R M N).hom.val.app W
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} (A := R) M N W x y) =
      proEtaleTensorPair T R M N W x y := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let q := (SheafOfModules.siteTensorRightIso.{u + 1, u, u + 1} R N.val).app M.val
  have h := congrArg (fun z ↦ z.app W (x ⊗ₜ[R.obj.obj W] y))
    (adj.unit.naturality q.hom).symm
  change ((PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (𝟙 _)).map q.hom).val.app W
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} (A := R) M N W x y) =
    (adj.unit.app (M.val ⊗ N.val)).app W (x ⊗ₜ[R.obj.obj W] y) at h
  exact congrArg
    ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M N).inv.val.app W) h

private theorem coordinate_identity {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    (q : M ≃ₗ[A] A) (f : M →ₗ[A] A) (x z : M) (hx : f x = 1) :
    f z • x = z := by
  have hq (y : M) : y = q y • q.symm 1 := by
    apply q.injective
    simp
  have hf (y : M) : f y = q y * f (q.symm 1) := by
    conv_lhs => rw [hq y]
    rw [map_smul, smul_eq_mul]
  have hunit : q x * f (q.symm 1) = 1 := (hf x).symm.trans hx
  apply q.injective
  rw [map_smul, smul_eq_mul, hf]
  calc
    (q z * f (q.symm 1)) * q x = q z * (q x * f (q.symm 1)) := by ring
    _ = q z := by rw [hunit, mul_one]

private theorem frame_first_basis (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L : proEtaleRingModules T R)
    (hL : ∃ (I : Type (u + 1)) (X : I → T.ProEt),
      (ProEt.topology T).CoversTop X ∧ ∀ i,
        Nonempty (L.over (X i) ≅ SheafOfModules.unit.{u, u + 1, u + 1}
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (X i))))
    (V : T.ProEt) (e : FiniteTensorLineFrame T R L V) :
    ∀ W : (Over V)ᵒᵖ, Function.Bijective
      (fun a : R.obj.obj (op W.unop.left) ↦ a • L.val.map W.unop.hom.op (e.basis 1 0)) := by
  obtain ⟨I, X, hX, h⟩ := hL
  let φ := e.basis (-1) 0
  have heval (W : (Over V)ᵒᵖ) :
      φ.app W (L.val.map W.unop.hom.op (e.basis 1 0)) =
        (1 : R.obj.obj (op W.unop.left)) := by
    have hn := PresheafOfModules.naturality_apply φ
      (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 V)).op
        (e.basis 1 0)
    change φ.app W (L.val.map W.unop.hom.op (e.basis 1 0)) =
      R.obj.map W.unop.hom.op (φ.app (op (Over.mk (𝟙 V))) (e.basis 1 0)) at hn
    rw [show φ.app (op (Over.mk (𝟙 V))) (e.basis 1 0) = (1 : R.obj.obj (op V)) from e.negative 0,
      map_one] at hn
    exact hn
  intro W
  have hid (z : L.val.obj (op W.unop.left)) :
      φ.app W z • L.val.map W.unop.hom.op (e.basis 1 0) = z := by
    apply L.isSheaf.isSeparated _ _ (hX W.unop.left)
    intro Z k hk
    obtain ⟨i, ⟨g⟩⟩ := hk
    let WZ : (Over V)ᵒᵖ := op (Over.mk (k ≫ W.unop.hom))
    let q : L.val.obj (op Z) ≃ₗ[R.obj.obj (op Z)] R.obj.obj (op Z) :=
      ((SheafOfModules.evaluation _ (op (Over.mk g))).mapIso (h i).some).toLinearEquiv
    have hh := coordinate_identity q (φ.app WZ).hom
      (L.val.map (k ≫ W.unop.hom).op (e.basis 1 0)) (L.val.map k.op z) (heval WZ)
    have hn := PresheafOfModules.naturality_apply φ
      (Over.homMk k : Over.mk (k ≫ W.unop.hom) ⟶ W.unop).op z
    change φ.app WZ (L.val.map k.op z) = R.obj.map k.op (φ.app W z) at hn
    change L.val.map k.op (φ.app W z • L.val.map W.unop.hom.op (e.basis 1 0)) =
      L.val.map k.op z
    rw [L.val.map_smul]
    change R.obj.map k.op (φ.app W z) •
      L.val.map k.op (L.val.map W.unop.hom.op (e.basis 1 0)) = L.val.map k.op z
    rw [← hn, ← PresheafOfModules.map_comp_apply]
    exact hh
  constructor
  · intro a b hab
    have hf := congrArg (φ.app W) hab
    have ha := (φ.app W).hom.map_smul a (L.val.map W.unop.hom.op (e.basis 1 0))
    have hb := (φ.app W).hom.map_smul b (L.val.map W.unop.hom.op (e.basis 1 0))
    rw [ha, hb, heval, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hf
    exact hf
  · intro z
    exact ⟨φ.app W z, hid z⟩

private theorem frame_basis_powers (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L : proEtaleRingModules T R)
    (hL : ∃ (I : Type (u + 1)) (X : I → T.ProEt),
      (ProEt.topology T).CoversTop X ∧ ∀ i,
        Nonempty (L.over (X i) ≅ SheafOfModules.unit.{u, u + 1, u + 1}
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (X i))))
    (V : T.ProEt) (e : FiniteTensorLineFrame T R L V) :
    SheafOfModules.SignedLineBasisPowers.{u + 1, u, u + 1} L (op V)
      (fun m ↦ e.basis m 0) := by
  obtain ⟨E, ⟨hE, he⟩, _⟩ :=
    SheafOfModules.existsUnique_signedLineBasisPowers.{u + 1, u, u + 1}
      L (op V) (e.basis 1 0) (frame_first_basis T R L hL V e)
  have hp (n : ℕ) : e.basis (.ofNat n) 0 = E (.ofNat n) := by
    induction n using Nat.twoStepInduction with
    | zero => exact e.zero.trans hE.2.1.symm
    | one => exact he.symm
    | more n _ ih =>
      have hpos : e.basis (.ofNat (n + 2)) 0 =
          SheafOfModules.siteSheafTensorTmul (A := R)
            (SheafOfModules.scalarTensorPower R L (n + 1)) L (op V)
            (e.basis (.ofNat (n + 1)) 0) (e.basis 1 0) := e.positive n
      exact hpos.trans (by rw [ih, ← he]; exact (hE.2.2.1 n).symm)
  have hall (m : ℤ) : e.basis m 0 = E m := by
    cases m with
    | ofNat n => exact hp n
    | negSucc n =>
      apply SheafOfModules.basisFunctional_ext
        (SheafOfModules.scalarTensorPower R L (n + 1)) (op V)
        (E (.ofNat (n + 1))) (hE.1 (.ofNat (n + 1)))
      intro W
      have hn := PresheafOfModules.naturality_apply (e.basis (.negSucc n) 0)
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 V)).op
          (e.basis (.ofNat (n + 1)) 0)
      change (e.basis (.negSucc n) 0).app W
          ((SheafOfModules.scalarTensorPower R L (n + 1)).val.map
            W.unop.hom.op (e.basis (.ofNat (n + 1)) 0)) =
        R.obj.map W.unop.hom.op
          ((e.basis (.negSucc n) 0).app (op (Over.mk (𝟙 V)))
            (e.basis (.ofNat (n + 1)) 0)) at hn
      rw [show (e.basis (.negSucc n) 0).app (op (Over.mk (𝟙 V)))
          (e.basis (.ofNat (n + 1)) 0) =
          (1 : R.obj.obj (op V)) from e.negative n, map_one, hp] at hn
      exact hn.trans (hE.2.2.2 n W).symm
  have hh : (fun m ↦ e.basis m 0) = E := funext hall
  rw [hh]
  exact hE
/-- The local signed multiplication rule glues to an ordinary sheaf morphism.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, invertible twists;
Stacks Project, sites-modules.tex, Section tensor-product and Section invertible.
(blueprint: lem-route-exists-finite-tensor-sheaf-product-map).
Proof: the first finite line is the positive finite coefficient line reindexed by
(level-1)+1 = level, hence locally free of rank one (coefficientTwistFiniteRank,
with l invertible in every residue field); its local trivializations give a cover on
which it is isomorphic to the coefficient unit. existsUnique_signedLineProduct gives
intrinsic maps mu(r,t) : L_r tensor L_t -> L_(r+t) normalized on every family of
signed basis powers. An arbitrary frame e over V is such a family: e(-1) evaluates to
one on every restriction of e(1), so by local coordinates and separatedness e(1)
generates every restriction; two-step induction and uniqueness of dual functionals
identify the frame with the signed powers of e(1). Transport mu through the finite
scalar tensor comparison, the realization counits and the presentation of the site
tensor as the monoidal tensor, and lift by full faithfulness of the realization.
Naturality of the realization unit and the two pure-tensor formulas give the stated
normalization for every frame. Only existence is asserted; no step uses 0 ≠ 1 or a
nonempty object. -/
theorem exists_finiteTensorSheafProductMap (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    ∃ f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T (r + t),
      ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T (r + t) V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
          e.basis (r + t) 0 := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let E := sfIntrinsicModuleEquivalence T P.Ring
  let L := P.finiteTensorFirstLine T
  have hfirst : (P.finiteTensorFirstLine T).IsFiniteLocallyFreeOfRank 1 := by
    let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
      (map_natCast (IsLocalRing.residue (T.presheaf.stalk x)) P.coefficients.l) ▸
        ((P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x).map
          (IsLocalRing.residue (T.presheaf.stalk x))).invertible
    have transport_rank (n m : ℕ) (h : n = m)
        (L : proEtaleRingModules T (proEtaleConstantRing T
          (Padic.coefficientExtensionRing P.coefficients.l P.extension n)))
        (hL : L.IsFiniteLocallyFreeOfRank 1) :
        (Eq.mp (congrArg (fun k : ℕ ↦ proEtaleRingModules T
          (proEtaleConstantRing T
            (Padic.coefficientExtensionRing P.coefficients.l P.extension k))) h) L
          ).IsFiniteLocallyFreeOfRank 1 := by
      subst m
      exact hL
    exact transport_rank _ _ (Nat.sub_add_cancel P.level_pos) _
      (coefficientTwistFiniteRank P.coefficients.l P.extension T (P.level - 1))
  let := hfirst
  have hLfree :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp hfirst
  have hL : ∃ (I : Type (u + 1)) (X : I → T.ProEt),
      (ProEt.topology T).CoversTop X ∧ ∀ i,
        Nonempty (L.over (X i) ≅ SheafOfModules.unit.{u, u + 1, u + 1}
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing T P.Ring)).over (X i))) := by
    obtain ⟨I, X, hX, h⟩ := hLfree
    refine ⟨I, X, hX, ?_⟩
    intro i
    obtain ⟨e⟩ := h i
    exact ⟨e ≪≫ SheafOfModules.freeUniqueIso (ULift (Fin 1))⟩
  obtain ⟨μ, hμ, _⟩ :=
    SheafOfModules.existsUnique_signedLineProduct.{u + 1, u, u + 1} L hL
  let Fr := P.finiteTensorFixedSheaf T r
  let Ft := P.finiteTensorFixedSheaf T t
  let Fs := P.finiteTensorFixedSheaf T (r + t)
  let τ := finiteScalarOrdinaryTensorIso T P.Ring
  let R := proEtaleConstantRing T P.Ring
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let h : E.functor.obj (Fr ⊗ Ft) ⟶ E.functor.obj Fs :=
    τ.hom.app (Fr, Ft) ≫
      (E.counitIso.hom.app (P.finiteTensorLine T r) ⊗ₘ
        E.counitIso.hom.app (P.finiteTensorLine T t)) ≫
      (tensorPresentation T R (P.finiteTensorLine T r) (P.finiteTensorLine T t)).inv ≫
      (μ r t).hom ≫ E.counitIso.inv.app (P.finiteTensorLine T (r + t))
  let f := E.fullyFaithfulFunctor.preimage h
  have hf : E.functor.map f = h := E.fullyFaithfulFunctor.map_preimage h
  refine ⟨f, ?_⟩
  intro V e x y hx hy
  let W := op V
  let z := P.finiteTensorSectionTmul T r t V x y
  have hη := congrArg (fun q ↦ q.app W z)
    ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T P.Ring)).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt
          (ULift.{u + 1} P.Ring)).map f.hom))
  change sfIntrinsicRealizationUnit T P.Ring Fs W (f.hom.app W z) =
    (E.functor.map f).val.app W
      (sfIntrinsicRealizationUnit T P.Ring (Fr ⊗ Ft) W z) at hη
  rw [hf] at hη
  let s := tensorPresentation T R (P.finiteTensorLine T r) (P.finiteTensorLine T t)
  let c := E.counitIso.app (P.finiteTensorLine T (r + t))
  have hc (a : (P.finiteTensorLine T (r + t)).val.obj W) :
      c.hom.val.app W (c.inv.val.app W a) = a := by
    have hi := congrArg (fun q ↦ q.val.app W a) c.inv_hom_id
    exact hi
  change c.hom.val.app W
    (sfIntrinsicRealizationUnit T P.Ring Fs W (f.hom.app W z)) = _
  rw [hη]
  change c.hom.val.app W (c.inv.val.app W
    ((μ r t).hom.val.app W (s.inv.val.app W
      ((E.counitIso.hom.app (P.finiteTensorLine T r) ⊗ₘ
        E.counitIso.hom.app (P.finiteTensorLine T t)).val.app W
          ((τ.hom.app (Fr, Ft)).val.app W
            (sfIntrinsicRealizationUnit T P.Ring (Fr ⊗ Ft) W z)))))) = _
  rw [hc]
  have ht := finiteScalarTensorRealization_pure T P.Ring Fr Ft W x y
  change (τ.hom.app (Fr, Ft)).val.app W
      (sfIntrinsicRealizationUnit T P.Ring (Fr ⊗ Ft) W z) = _ at ht
  rw [ht]
  erw [proEtaleTensorPair_natural]
  change (μ r t).hom.val.app W (s.inv.val.app W
    (proEtaleTensorPair T R (P.finiteTensorLine T r) (P.finiteTensorLine T t) W
      (P.finiteTensorSection T r V x) (P.finiteTensorSection T t V y))) = _
  rw [hx, hy, ← tensorPresentation_pure]
  have hs := congrArg (fun q ↦ q.val.app W
    (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} (A := R)
      (P.finiteTensorLine T r) (P.finiteTensorLine T t) W
        (e.basis r 0) (e.basis t 0))) s.hom_inv_id
  change s.inv.val.app W (s.hom.val.app W _) = _ at hs
  rw [hs]
  exact hμ W (fun m ↦ e.basis m 0) (frame_basis_powers T R L hL V e) r t

end WeilConjectures.PurityFiniteSetting
