/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.PurTwistCoefficientRings
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Paper.DerivedCompleteIntegralDetailed
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.PurTwistCoefficientTensor
import Sheaf.CategoryTheory.TensorPushoutAction

/-! # The integral Tate line on the pro-etale site

Source: Stacks Project, Tag 03PK; the coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).

The auxiliary constructions retain the root tower, constant scalar extension and completed
scalar action. All choices below have a uniqueness specification. The tensor of commutative
ring sheaves is their pushout, so the coefficient comparison is a morphism of ring sheaves.
The natural-number level `n` means positive exponent `n + 1` throughout.

## Main definitions

* `purTwistZlOne` and `purTwistZlModule`: the root limit and its completed scalar action.
* `purTwistIntegralOne` and `purTwistIntegralModule`: the prescribed integral tensor line.
* `purTwistFiniteOne`: its prescribed ordinary finite-coefficient tensor reduction.
* `purTwistCoefficientComparison`: the canonical comparison of coefficient ring sheaves.

## Main statements

* `pur_twist_sheaf_locally_free`: all four local-freeness and derived-completeness clauses.
-/

@[expose] public section

set_option autoImplicit false

universe u d

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The original root tower's inverse limit, with no replacement of its underlying groups.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlOne :=
  limit (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))

/-- Forgetting commutativity preserves sheafification on the small pro-etale site.
Source: Stacks Tag 00W1 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: sheafification uses covering-compatible families and their local equality relation.
Forgetting commutativity preserves the finite limits and filtered colimits in this
construction. Thus the same sheafification is obtained before and after forgetting. -/
theorem purTwistForgetPreservesSheafification :
    (ProEt.topology S).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change (ProEt.topology S).W
    (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective (ProEt.topology S) f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (ProEt.topology S) f := hf.isLocallySurjective
  apply ((ProEt.topology S).W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology S) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology S) f x⟩

/-- The constant-ring comparison coming from commutation with forgetting commutativity.
Source: Stacks Tags 03CY and 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistFiniteRingIso (n : ℕ) :
    purTwistRing S (purTwistFiniteRing S l n) ≅
      proEtaleRootsOfUnityCoefficientRing S (l ^ (n + 1)) :=
  letI := purTwistForgetPreservesSheafification S
  (constantCommuteCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app _

/-- The recorded finite roots module, transported along the canonical coefficient comparison.
Source: Stacks Tags 03CY and 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistRootsModule (n : ℕ) :=
  (SheafOfModules.restrictScalars (purTwistFiniteRingIso S l n).hom).obj
    (proEtaleRootsOfUnityModule S (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _))

set_option backward.isDefEq.respectTransparency.types false in
-- Pull back the target action along the coefficient reduction. Normalized torsion
-- actions make every additive sheaf morphism linear for this pulled-back action.
private theorem purTwistTorsionMap_smul
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J RingCat.{u + 1}] (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (F G : Sheaf J AddCommGrpCat.{u + 1})
    (hF : ∀ U (x : F.obj.obj U), N' • x = 0)
    (hG : ∀ U (x : G.obj.obj U), N • x = 0)
    (hG' : ∀ U (x : G.obj.obj U), N' • x = 0)
    (ρ : constantZModRingSheaf J N' ⟶
      constantZModRingSheaf J N) (φ : F ⟶ G)
    (U : Cᵒᵖ) (a : (constantZModRingSheaf J N').obj.obj U)
    (x : F.obj.obj U) :
    φ.hom.app U
      (@SMul.smul _ _ (torsionSheafModuleStructure J N' hN' F hF U).toSMul
        a x) =
      @SMul.smul _ _ (torsionSheafModuleStructure J N hN G hG U).toSMul
        (ρ.hom.app U a) (φ.hom.app U x) := by
  let M (V : Cᵒᵖ) := torsionSheafModuleStructure J N hN G hG V
  let M' (V : Cᵒᵖ) :
      Module ((constantZModRingSheaf J N').obj.obj V) (G.obj.obj V) :=
    letI := M V
    Module.compHom _ (ρ.hom.app V).hom
  have hM' : IsConstantZModSheafModuleStructure J N' G M' := by
    constructor
    · intro V z y
      change @SMul.smul _ _ (M V).toSMul (ρ.hom.app V
        (((toSheafify J
          ((Functor.const Cᵒᵖ).obj
            (RingCat.of (ULift.{u + 1} (ZMod N'))))).app V).hom
          (z : ULift.{u + 1} (ZMod N')))) y = z • y
      rw [map_intCast, map_intCast]
      exact @Int.cast_smul_eq_zsmul _ _ _ _ (M V) z y
    · intro V W f b y
      change G.obj.map f (@SMul.smul _ _ (M V).toSMul (ρ.hom.app V b) y) =
        @SMul.smul _ _ (M W).toSMul
          (ρ.hom.app W ((constantZModRingSheaf J N').obj.map f b))
          (G.obj.map f y)
      rw [(torsionSheafModuleStructure_spec J N hN G hG).2 f]
      rw [NatTrans.naturality_apply ρ.hom f]
  exact torsionSheaf_hom_linear J N' hN' F G hF hG' φ
    (torsionSheafModuleStructure J N' hN' F hF) M'
    (torsionSheafModuleStructure_spec J N' hN' F hF) hM' U a x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem purTwistTransition_smul (n : ℕ) (U : S.ProEtᵒᵖ)
    (a : (purTwistFiniteRing S l (n + 1)).obj.obj U)
    (x : (purTwistRootsModule S l (n + 1)).val.obj U) :
    (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U (a • x) =
      (purTwistFiniteTransition S l n).hom.app U a •
        (@id ((purTwistRootsModule S l n).val.obj U)
          ((proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
            (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
            (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U x)) := by
  let ρ := (purTwistFiniteRingIso S l (n + 1)).inv ≫
    (sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistFiniteTransition S l n) ≫ (purTwistFiniteRingIso S l n).hom
  have h := purTwistTorsionMap_smul (ProEt.topology S) (l ^ (n + 1)) (l ^ (n + 2))
    (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
    _ _ (proEtaleRootsOfUnity_nsmul S _) (proEtaleRootsOfUnity_nsmul S _)
    (proEtaleRootsOfUnity_nsmul_of_dvd S _ _ (pow_dvd_pow l (Nat.le_succ (n + 1))))
    ρ (proEtaleRootsOfUnityTransition S _ _
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1)))) U
    ((purTwistFiniteRingIso S l (n + 1)).hom.hom.app U a) x
  have he : ρ.hom.app U ((purTwistFiniteRingIso S l (n + 1)).hom.hom.app U a) =
      (purTwistFiniteRingIso S l n).hom.hom.app U
        ((purTwistFiniteTransition S l n).hom.app U a) := by
    change ((purTwistFiniteRingIso S l n).hom.hom.app U)
      ((purTwistFiniteTransition S l n).hom.app U
        (((purTwistFiniteRingIso S l (n + 1)).hom ≫
          (purTwistFiniteRingIso S l (n + 1)).inv).hom.app U a)) = _
    rw [Iso.hom_inv_id]
    rfl
  rw [he] at h
  exact h

-- Jointly injective coordinates transfer the module laws and determine the action uniquely.
private theorem purTwistCoordinateModule
    {R M : Type*} [CommRing R] [AddCommGroup M]
    {A : ℕ → Type*} [∀ n, CommRing (A n)]
    {N : ℕ → Type*} [∀ n, AddCommGroup (N n)] [∀ n, Module (A n) (N n)]
    (p : ∀ n, M →+ N n) (q : ∀ n, R →+* A n)
    (hext : ∀ x y, (∀ n, p n x = p n y) → x = y)
    (hs : ∀ a x, ∃ y, ∀ n, p n y = q n a • p n x) :
    ∃! m : Module R M, ∀ n a x, p n (@SMul.smul _ _ m.toSMul a x) = q n a • p n x := by
  classical
  choose sm hsm using hs
  let m : Module R M :=
    { smul := sm
      one_smul := by
        intro x
        apply hext
        intro n
        change p n (sm 1 x) = p n x
        rw [hsm, map_one, one_smul]
      mul_smul := by
        intro a b x
        apply hext
        intro n
        change p n (sm (a * b) x) = p n (sm a (sm b x))
        rw [hsm, hsm, hsm, map_mul, mul_smul]
      smul_zero := by
        intro a
        apply hext
        intro n
        change p n (sm a 0) = p n 0
        rw [hsm, map_zero, smul_zero]
      smul_add := by
        intro a x y
        apply hext
        intro n
        change p n (sm a (x + y)) = p n (sm a x + sm a y)
        rw [hsm, map_add, map_add, hsm, hsm, smul_add]
      add_smul := by
        intro a b x
        apply hext
        intro n
        change p n (sm (a + b) x) = p n (sm a x + sm b x)
        rw [hsm, map_add, map_add, hsm, hsm, add_smul]
      zero_smul := by
        intro x
        apply hext
        intro n
        change p n (sm 0 x) = p n 0
        rw [hsm, map_zero, zero_smul, map_zero] }
  refine ⟨m, (fun n a x ↦ hsm a x n), ?_⟩
  intro m' hm'
  apply Module.ext'
  intro a x
  apply hext
  intro n
  exact (hm' n a x).trans (hsm a x n).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The completed scalar action is determined coordinatewise on the root limit.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: limits of abelian sheaves are sectionwise compatible tuples. Multiplication
of each root by its finite coefficient is compatible with reduction and the power
transition. All module identities and restriction identities hold coordinatewise.
Joint injectivity of the limit projections gives uniqueness of this module action. -/
theorem purTwistZlAction_existsUnique :
    ∃! M : ∀ U : S.ProEtᵒᵖ,
      Module ((purTwistZlCompletion S l).obj.obj U) ((purTwistZlOne S l).obj.obj U),
      (∀ ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
        (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U),
        (purTwistZlOne S l).obj.map f (@SMul.smul _ _ (M U).toSMul a x) =
          @SMul.smul _ _ (M V).toSMul ((purTwistZlCompletion S l).obj.map f a)
            ((purTwistZlOne S l).obj.map f x)) ∧
      ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
        (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U),
        (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
          (@SMul.smul _ _ (M U).toSMul a x) =
        ((purTwistZlProjection S l n).hom.app U a) •
          (@id ((purTwistRootsModule S l n).val.obj U)
            ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
              U x)) := by
  classical
  let T : ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
    proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)
  let ev (U : S.ProEtᵒᵖ) :
      Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation S.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj U
  let p (n : ℕ) (U : S.ProEtᵒᵖ) : (purTwistZlOne S l).obj.obj U →+
      (purTwistRootsModule S l n).val.obj U := ((limit.π T (op n)).hom.app U).hom
  let q (n : ℕ) (U : S.ProEtᵒᵖ) : (purTwistZlCompletion S l).obj.obj U →+*
      (purTwistFiniteRing S l n).obj.obj U := ((purTwistZlProjection S l n).hom.app U).hom
  have hxext (U : S.ProEtᵒᵖ) (x y : (purTwistZlOne S l).obj.obj U)
      (h : ∀ n, p n U x = p n U y) : x = y := by
    exact Concrete.isLimit_ext (T ⋙ ev U)
      (isLimitOfPreserves (ev U) (limit.isLimit T)) x y (fun n ↦ h n.unop)
  have hp (n : ℕ) (U : S.ProEtᵒᵖ) (x : (purTwistZlOne S l).obj.obj U) :
      (T.map (homOfLE (Nat.le_succ n)).op).hom.app U (p (n + 1) U x) = p n U x := by
    exact congrArg (fun f ↦ f.hom.app U x) (limit.w T (homOfLE (Nat.le_succ n)).op)
  have hq (n : ℕ) (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U) :
      (purTwistFiniteTransition S l n).hom.app U (q (n + 1) U a) = q n U a := by
    have h := limit.w (purTwistZlTower S l) (homOfLE (Nat.le_succ n)).op
    rw [show (purTwistZlTower S l).map (homOfLE (Nat.le_succ n)).op =
      purTwistFiniteTransition S l n from Functor.ofOpSequence_map_homOfLE_succ _ n] at h
    exact congrArg (fun f ↦ f.hom.app U a) h
  have hs (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U)
      (x : (purTwistZlOne S l).obj.obj U) :
      ∃ y : (purTwistZlOne S l).obj.obj U,
        ∀ n, p n U y = q n U a • (@id ((purTwistRootsModule S l n).val.obj U) (p n U x)) := by
    let c : Cone (T ⋙ ev U ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      { pt := PUnit
        π := NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ q n U a •
          (@id ((purTwistRootsModule S l n).val.obj U) (p n U x))) (by
          intro n
          ext z
          change q n U a • (@id ((purTwistRootsModule S l n).val.obj U) (p n U x)) =
            (T.map (homOfLE (Nat.le_succ n)).op).hom.app U
              (q (n + 1) U a •
                (@id ((purTwistRootsModule S l (n + 1)).val.obj U) (p (n + 1) U x)))
          rw [show (T.map (homOfLE (Nat.le_succ n)).op) =
            proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.le_succ (n + 1))) by
                exact Functor.ofOpSequence_map_homOfLE_succ _ n]
          erw [purTwistTransition_smul]
          rw [hq]
          have hpx := hp n U x
          rw [show T.map (homOfLE (Nat.le_succ n)).op =
            proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.le_succ (n + 1))) from
                Functor.ofOpSequence_map_homOfLE_succ _ n] at hpx
          exact congrArg (fun y : (purTwistRootsModule S l n).val.obj U ↦ q n U a • y)
            hpx.symm) }
    let hc₁ := isLimitOfPreserves (ev U) (limit.isLimit T)
    let hc := isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1}) hc₁
    exact ⟨hc.lift c PUnit.unit, fun n ↦ ConcreteCategory.congr_hom (hc.fac c (op n)) PUnit.unit⟩
  have hmod (U : S.ProEtᵒᵖ) := purTwistCoordinateModule
    (R := (purTwistZlCompletion S l).obj.obj U) (M := (purTwistZlOne S l).obj.obj U)
    (A := fun n ↦ (purTwistFiniteRing S l n).obj.obj U)
    (N := fun n ↦ (purTwistRootsModule S l n).val.obj U)
    (p := fun n ↦ p n U) (q := fun n ↦ q n U) (hxext U) (hs U)
  choose M hM huniq using hmod
  refine ⟨M, ⟨?_, fun n U a x ↦ hM U n a x⟩, ?_⟩
  · intro U V f a x
    apply hxext V
    intro n
    have hn (y : (purTwistZlOne S l).obj.obj U) :
        p n V ((purTwistZlOne S l).obj.map f y) =
          (purTwistRootsModule S l n).val.map f (p n U y) :=
      NatTrans.naturality_apply (limit.π T (op n)).hom f y
    have hqn := (NatTrans.naturality_apply (purTwistZlProjection S l n).hom f a).symm
    rw [hn, hM, hM, (purTwistRootsModule S l n).val.map_smul, ← hqn, hn]
    rfl
  · intro M' hM'
    funext U
    exact huniq U (M' U) (fun n a x ↦ hM'.2 n U a x)

/-- The unique coordinatewise completed coefficient action.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
@[instance_reducible]
noncomputable def purTwistZlAction := (purTwistZlAction_existsUnique S l).exists.choose

/-- The action commutes with restriction.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: take the restriction clause of the defining unique coordinatewise action. -/
theorem purTwistZlAction_restriction ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
    (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U) :
    (purTwistZlOne S l).obj.map f
      (@SMul.smul _ _ (purTwistZlAction S l U).toSMul a x) =
    @SMul.smul _ _ (purTwistZlAction S l V).toSMul
      ((purTwistZlCompletion S l).obj.map f a) ((purTwistZlOne S l).obj.map f x) := by
  exact (purTwistZlAction_existsUnique S l).exists.choose_spec.1 f a x

/-- `Z_l(1)` as a module over the completed coefficient sheaf, with unchanged root limit.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlModule :
    SheafOfModules.{u + 1} (purTwistRing S (purTwistZlCompletion S l)) :=
  letI : ∀ U : S.ProEtᵒᵖ,
      Module ((purTwistRing S (purTwistZlCompletion S l)).obj.obj U)
        ((purTwistZlOne S l).obj.obj U) := purTwistZlAction S l
  ⟨PresheafOfModules.ofPresheaf
    (R := (purTwistRing S (purTwistZlCompletion S l)).obj) (purTwistZlOne S l).obj
    (purTwistZlAction_restriction S l), (purTwistZlOne S l).property⟩

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The integral Tate line is the prescribed scalar extension over the discrete constants.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralOne :
    SheafOfModules.{u + 1} (purTwistRing S (purTwistIntegralConstant S l E)) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap S l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l))

/-- A pure tensor in the prescribed integral line, after sheafification.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralTensor (U : S.ProEtᵒᵖ)
    (b : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (purTwistIntegralOne S l E).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (purTwistRing S (purTwistIntegralConstant S l E)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistConstantIntegersMap S l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)))).app U)
      (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U,
        ((purTwistConstantIntegersMap S l E).hom.app U).hom] x)

/-- The completed action on the integral tensor is uniquely fixed on pure tensors.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: the coefficient comparison identifies the completed ring with the ring-sheaf tensor.
Its action is `(a tensor b)(x tensor c) = (a*x) tensor (b*c)`. This respects balanced
relations and sheafifies. The section formulas below and local generation by pure tensors
prove uniqueness; restriction compatibility follows from the same formula. -/
theorem purTwistIntegralAction_existsUnique :
    ∃! M : ∀ U : S.ProEtᵒᵖ,
      Module ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        ((purTwistIntegralOne S l E).val.obj U),
      (∀ ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
        (a : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        (x : (purTwistIntegralOne S l E).val.obj U),
        (purTwistIntegralOne S l E).val.map f (@SMul.smul _ _ (M U).toSMul a x) =
          @SMul.smul _ _ (M V).toSMul
            ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.map f a)
            ((purTwistIntegralOne S l E).val.map f x)) ∧
      (∀ (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistIntegralOne S l E).val.obj U),
        @SMul.smul _ _ (M U).toSMul
          ((purTwistIntegralCompletionMap S l E).hom.app U b) x = b • x) ∧
      ∀ (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U)
        (b : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistZlModule S l).val.obj U),
        @SMul.smul _ _ (M U).toSMul ((purTwistCompletedScalarMap S l E).hom.app U a)
          (purTwistIntegralTensor S l E U b x) =
        purTwistIntegralTensor S l E U b (a • x) := by
  let e (U : S.ProEtᵒᵖ) :=
    letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    letI := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
    RingEquiv.ofBijective (purTwistCoefficientTensorMap S l E U)
      (purTwistCoefficientTensor S l E U)
  have he (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
      (a : (purTwistZlCompletion S l).obj.obj U) :
      letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
      letI := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
      e U (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U] a) =
        (purTwistIntegralCompletionMap S l E).hom.app U b *
          (purTwistCompletedScalarMap S l E).hom.app U a := rfl
  exact CategoryTheory.tensorPushoutAction_existsUnique
    (purTwistZlCompletionMap S l) (purTwistConstantIntegersMap S l E)
    (purTwistCompletedScalarMap S l E) (purTwistIntegralCompletionMap S l E)
    (purTwistZlModule S l) e he

/-- The unique action on the concrete integral tensor sheaf.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
@[instance_reducible]
noncomputable def purTwistIntegralAction :=
  (purTwistIntegralAction_existsUnique S l E).exists.choose

/-- The integral action commutes with restriction.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: take the restriction clause of the uniquely characterized action. -/
theorem purTwistIntegralAction_restriction ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
    (a : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
    (x : (purTwistIntegralOne S l E).val.obj U) :
    (purTwistIntegralOne S l E).val.map f
      (@SMul.smul _ _ (purTwistIntegralAction S l E U).toSMul a x) =
    @SMul.smul _ _ (purTwistIntegralAction S l E V).toSMul
      ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.map f a)
      ((purTwistIntegralOne S l E).val.map f x) := by
  exact (purTwistIntegralAction_existsUnique S l E).exists.choose_spec.1 f a x

/-- The prescribed integral tensor equipped with its canonical completed-ring action.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralModule :
    SheafOfModules.{u + 1}
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S) :=
  letI : ∀ U : S.ProEtᵒᵖ,
      Module ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        ((purTwistIntegralOne S l E).val.presheaf.obj U) := purTwistIntegralAction S l E
  ⟨PresheafOfModules.ofPresheaf
    (R := (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj)
    (purTwistIntegralOne S l E).val.presheaf
    (purTwistIntegralAction_restriction S l E), (purTwistIntegralOne S l E).isSheaf⟩

/-- The finite Tate line, exactly the ordinary constant-coefficient tensor in the node.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistFiniteOne (n : ℕ) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E S n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistIntegralQuotient S l E n)
    (purTwistIntegralOne S l E)

/-- All four properties of the concrete Tate lines, including the empty-scheme case.
Source: Stacks Project, Tag 03PK and Lemma 03RV; coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).
Proof:
1. On affine opens the finite root scheme is etale, by
   lem-sbc-root-split-away-cover-etale. Use lem-asd-finite-etale-twist-line and the
   representable calculation for def-weil-pbc-site-comparison-morphism to transfer its
   trivializations to the pro-etale root sheaf. The comparison of constant finite
   coefficients in lem-sf-comparison-pullback-exact respects the scalar action.
2. Apply lem-amb-kummer-any-base on each test scheme to lift roots through the power
   transitions locally. The sheaf local-surjectivity criterion makes them epimorphisms.
3. Refine the level-one etale cover by
   lem-weil-pbc-proetale-affine-wcontractible-covering-family. On each weakly contractible
   member lift primitive roots recursively. Every lift stays primitive: its coefficient
   modulo l is a unit, hence its coefficient modulo every l-power is a unit. Constant
   sections and their equality can be checked locally by
   lem-weil-pbc-site-sheafification-sections-local and the constant-sheaf stalk theorem.
4. Take the compatible root trivializations to the inverse limit. Slice restriction
   commutes with sectionwise limits, by lem-weil-proetale-weakly-etale-localization.
   The coordinate action gives a completed coefficient line. The quotient clause of
   lem-weil-pbc-constant-completion-equivalence and the tensor-quotient formula identify
   its finite reductions with the roots sheaves.
5. The valuation-ring DVR theorem writes l as a unit times a positive uniformizer power.
   Lift a finite residue basis and use successive l-adic digit expansions and completeness
   to obtain finite generation over Z_l. Torsion freeness and
   lem-sc-dvr-fg-torsionfree-free give a finite basis.
6. Reduce that basis modulo l-powers and take limits. Uniformizer powers and l-powers are
   cofinal, so the canonical ring-sheaf tensor comparison is an isomorphism, including its
   multiplicative and unit structure. Its pure-tensor formula gives the completed action
   on the prescribed integral tensor sheaf, which is locally a line.
7. Both ordinary reductions are quotient by the same uniformizer power, hence coincide.
   Choose a finite l-power annihilating each coefficient quotient; its finite root
   trivialization is an etale trivialization of the finite Tate line. The geometric-point
   lifting and constant-stalk lemmas make its stalks finite.
8. The integral line placed in degree zero is K-flat: on its trivializing cover its tensor
   with any acyclic complex is that complex, and slice restriction is exact by
   lem-pur-site-restriction-module-adjunction-exact. Compute derived reduction on this
   representative using def-weil-integral-derived-reduction, obtaining the ordinary
   finite line in degree zero with the same quotient transition and augmentation maps.
9. The single stratum S witnesses constructibility of each finite reduction. Its support
   is contained in {0}; on a nonempty S a geometric stalk is the nonzero coefficient ring,
   so the support equals {0}. On the empty scheme every sheaf is zero and support is empty.
10. The finite reduction tower is surjective and its ordinary inverse limit is the
    integral line, checked on the same trivializing cover. Apply
    lem-weil-proetale-surjective-tower-derived-limit to its quotient maps to obtain the
    Roos triangle with the actual augmentation. This is def-weil-derived-complete.
11. All reductions are constructible with uniform amplitude [0,0], so the integral line
    belongs to def-weil-derived-complete-integral-detailed. -/
theorem pur_twist_sheaf_locally_free
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ,
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        (∀ i : I, Etale (U i).hom) ∧
        ∀ i : I, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i))) ∧
      (purTwistRootsModule S l n).IsFiniteLocallyFreeOfRank 1 ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
          (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1))) ∧
      Epi (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1))))) ∧
    ((∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i : I, Nonempty ((purTwistZlModule S l).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over (U i))) ∧
      (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ, Nonempty
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistZlProjection S l n)
          (purTwistZlModule S l) ≅ purTwistRootsModule S l n)) ∧
    ((∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E)))) ∧
      IsIso (purTwistCoefficientComparison S l E) ∧
      (purTwistIntegralModule S l E).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ,
        Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
            (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
        (purTwistFiniteOne S l E n).IsFiniteLocallyFreeOfRank 1 ∧
        IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
          (purTwistFiniteOne S l E n) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
          Finite (proEtaleGeometricModuleStalk s
            (WeilConjectures.integralCoefficientCommRingSheaf l E S n)
            (purTwistFiniteOne S l E n))) ∧
    (∀ (D : WeilConjectures.FiniteFieldDatum.{d}) (hl : l ≠ D.p),
      (∀ n : ℕ,
        Nonempty ((WeilConjectures.integralDerivedReduction l E S D hl n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ≅
            (DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) S
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ⊆ {0} ∧
        (Nonempty S → proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) = {0})) ∧
      WeilConjectures.IsDerivedComplete l E S D hl
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ∧
      WeilConjectures.boundedConstructibleDerivedCompleteIntegral D l hl E S
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E))) := by
  sorry

end AlgebraicGeometry.Scheme
