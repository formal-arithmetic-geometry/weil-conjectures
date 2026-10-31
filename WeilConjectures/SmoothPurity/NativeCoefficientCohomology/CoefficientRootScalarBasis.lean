/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbRootTowerPullbackCoherence

/-! # The scalar equation on a finite normalized root basis -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology

private def normalized_root_map (S : Scheme.{u}) (N : ℕ)
    (z : Γ(S, ⊤)ˣ) (hz : z ^ N = 1) :
    (constantSheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ⟶
        proEtaleRootsOfUnitySheaf S N :=
  ((sheafificationAdjunction (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).homEquiv
    _ _).symm (ProEtale.zmodToRootsPresheaf S N z hz ≫
      (Scheme.rootRawPresheafIso S N).inv)

private theorem normalized_root_map_isIso (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (z : Γ(S, ⊤)ˣ) (hz : z ^ N = 1)
    (hd : ∀ i < N, ∀ j < N, i ≠ j → IsUnit ((z : Γ(S, ⊤)) ^ i - (z : Γ(S, ⊤)) ^ j)) :
    IsIso (normalized_root_map S N z hz) := by
  unfold normalized_root_map
  rw [Adjunction.homEquiv_counit]
  rw [Functor.map_comp]
  have : IsIso ((presheafToSheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).map
      (ProEtale.zmodToRootsPresheaf S N z hz)) :=
    inferInstanceAs (IsIso (ProEtale.constantRootsIso N z hz hd).hom)
  infer_instance

private theorem normalized_root_map_value (S : Scheme.{u}) (N : ℕ)
    (z : Γ(S, ⊤)ˣ) (hz : z ^ N = 1) (U : S.ProEtᵒᵖ) (a : ℕ) :
    (Additive.toMul (proEtaleRootsOfUnitySections S N U
      ((normalized_root_map S N z hz).hom.app U
        ((toSheafify (Scheme.ProEt.topology S)
          ((Functor.const S.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app U
              (ULift.up (a : ZMod N)))))).val.val =
      U.unop.hom.appTop.hom (z : Γ(S, ⊤)) ^ a := by
  let adj := sheafificationAdjunction (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}
  let h := ProEtale.zmodToRootsPresheaf S N z hz ≫ (Scheme.rootRawPresheafIso S N).inv
  have hh := (adj.homEquiv _ (proEtaleRootsOfUnitySheaf S N)).apply_symm_apply h
  rw [Adjunction.homEquiv_unit] at hh
  have hv := congrArg (fun f ↦ f.app U (ULift.up (a : ZMod N))) hh
  change (normalized_root_map S N z hz).hom.app U
      ((toSheafify (Scheme.ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app U
            (ULift.up (a : ZMod N))) =
    (Scheme.rootRawPresheafIso S N).inv.app U
      ((ProEtale.zmodToRootsPresheaf S N z hz).app U (ULift.up (a : ZMod N))) at hv
  have he := congrArg ((Scheme.rootRawPresheafIso S N).hom.app U) hv
  have hc := ConcreteCategory.congr_hom
    ((Scheme.rootRawPresheafIso S N).inv_hom_id_app U)
    ((ProEtale.zmodToRootsPresheaf S N z hz).app U (ULift.up (a : ZMod N)))
  change (Scheme.rootRawPresheafIso S N).hom.app U
    ((Scheme.rootRawPresheafIso S N).inv.app U _) = _ at hc
  rw [hc] at he
  change (AddEquiv.ulift.symm
      (proEtaleRootsOfUnitySections S N U _)) = _ at he
  have he' := congrArg (fun t ↦ t.down.toMul.val.val) he
  exact he'.trans (ProEtale.zmodToRootsPresheaf_app_natCast N z hz U a)

set_option maxHeartbeats 1000000 in
-- Elaborating the normalized sheaf-section and fibre-product types exceeds the default limit.
/-- A normalized finite root basis satisfies the scaled direct-pullback equation.

Source: Weil I (2.2), geometric Frobenius is inverse arithmetic Frobenius.
(blueprint: lem-sf-coefficient-root-scalar-basis)

Proof: sheafify the map taking an integer residue a to z^a. Invertible differences
of the distinct powers make it locally bijective, hence its sheafification is an
isomorphism. The sheafification adjunction gives its displayed section formula.
The normalized root direct-image map restricts roots along the first fibre-product
projection. The pullback square changes that restriction to the second projection
followed by g. Raising to q and using (g^* z)^q=z therefore gives the target root.
The roots-of-unity section equivalence is injective, so these root values prove
the scaled equation. The case N=1 and the empty scheme use the same formulas. -/
private theorem coefficient_root_scalar_basis (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (g : S ⟶ S) (q : ℕ) (z : Γ(S, ⊤)ˣ) (hz : z ^ N = 1)
    (hd : ∀ i < N, ∀ j < N, i ≠ j → IsUnit ((z : Γ(S, ⊤)) ^ i - (z : Γ(S, ⊤)) ^ j))
    (hg : (Units.map g.appTop.hom.toMonoidHom z) ^ q = z) :
    ∃ b : (constantSheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ proEtaleRootsOfUnitySheaf S N,
      ∀ (U : S.ProEtᵒᵖ) (a : ℕ),
        let x := (toSheafify (Scheme.ProEt.topology S)
          ((Functor.const S.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app U
              (ULift.up (a : ZMod N))
        let V := (proEtaleBaseChange g).op.obj U
        let y := (toSheafify (Scheme.ProEt.topology S)
          ((Functor.const S.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app V
              (ULift.up (a : ZMod N))
        (Additive.toMul (proEtaleRootsOfUnitySections S N U
          (b.hom.hom.app U x))).val.val = U.unop.hom.appTop.hom (z : Γ(S, ⊤)) ^ a ∧
        q • ((proEtaleRootsOfUnityDirectImageMap g N).hom.app U (b.hom.hom.app U x)) =
          b.hom.hom.app V y := by
  have := normalized_root_map_isIso S N z hz hd
  refine ⟨asIso (normalized_root_map S N z hz), ?_⟩
  intro U a
  dsimp only
  constructor
  · exact normalized_root_map_value S N z hz U a
  · apply (proEtaleRootsOfUnitySections S N _).injective
    apply Additive.toMul.injective
    apply Subtype.val_injective
    apply Units.ext
    rw [map_nsmul, toMul_nsmul]
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    erw [Scheme.roots_direct_value, normalized_root_map_value S N z hz U a,
      normalized_root_map_value S N z hz ((proEtaleBaseChange g).op.obj U) a, map_pow]
    have hp' : (pullback.fst U.unop.hom g).appTop.hom
        (U.unop.hom.appTop.hom (z : Γ(S, ⊤))) =
      (pullback.snd U.unop.hom g).appTop.hom
        (g.appTop.hom (z : Γ(S, ⊤))) :=
      congrArg (fun f : pullback U.unop.hom g ⟶ S ↦ f.appTop.hom (z : Γ(S, ⊤)))
        (pullback.condition (f := U.unop.hom) (g := g))
    have hg' : g.appTop.hom (z : Γ(S, ⊤)) ^ q = (z : Γ(S, ⊤)) := by
      exact congrArg (fun t : Γ(S, ⊤)ˣ ↦ (t : Γ(S, ⊤))) hg
    let r := (pullback.snd U.unop.hom g).appTop.hom
    have hcomm : (r (g.appTop.hom (z : Γ(S, ⊤))) ^ a) ^ q =
        (r (g.appTop.hom (z : Γ(S, ⊤))) ^ q) ^ a :=
      (pow_mul _ a q).symm.trans
        ((congrArg (fun n : ℕ ↦ r (g.appTop.hom (z : Γ(S, ⊤))) ^ n)
          (Nat.mul_comm a q)).trans (pow_mul _ q a))
    have hroot : r (g.appTop.hom (z : Γ(S, ⊤))) ^ q = r (z : Γ(S, ⊤)) :=
      (r.map_pow _ q).symm.trans (congrArg r hg')
    exact (congrArg (fun t ↦ (t ^ a) ^ q) hp').trans
      (hcomm.trans (congrArg (fun t ↦ t ^ a) hroot))

/-- The constant finite residue sheaf used for a root frame.
Source: coefficient root tower (blueprint: lem-sf-coefficient-root-scalar-basis). -/
def coefficientRootConstants (S : Scheme.{u}) (N : ℕ) :=
  (constantSheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))

/-- The constant residue a, as an actual section of the constant sheaf.
Source: coefficient root tower (blueprint: lem-sf-coefficient-root-scalar-basis). -/
def coefficientRootSection (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ) (a : ℕ) :
    (coefficientRootConstants S N).obj.obj U :=
  (toSheafify (Scheme.ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app U (ULift.up (a : ZMod N))

/-- Compatible global roots and their finite scalar-normalized bases.
All data are actual roots and actual sheaf maps, with the power and scalar equations.
Source: Weil I (2.2) (blueprint: lem-sf-coefficient-root-scalar-basis). -/
structure CoefficientTateRootFrames (S : Scheme.{u}) (l q : ℕ) (g : S ⟶ S) where
  roots : ℕ → Γ(S, ⊤)ˣ
  zero : roots 0 = 1
  step : ∀ n, roots (n + 1) ^ l = roots n
  power : ∀ n, roots n ^ (l ^ n) = 1
  differences : ∀ n i, i < l ^ n → ∀ j, j < l ^ n → i ≠ j →
    IsUnit ((roots n : Γ(S, ⊤)) ^ i - (roots n : Γ(S, ⊤)) ^ j)
  frobenius_power : ∀ n, (Units.map g.appTop.hom.toMonoidHom (roots n)) ^ q = roots n
  basis : ∀ n, coefficientRootConstants S (l ^ n) ≅ proEtaleRootsOfUnitySheaf S (l ^ n)
  value : ∀ n U a,
    (Additive.toMul (proEtaleRootsOfUnitySections S (l ^ n) U
      ((basis n).hom.hom.app U (coefficientRootSection S (l ^ n) U a)))).val.val =
      U.unop.hom.appTop.hom (roots n : Γ(S, ⊤)) ^ a
  scalar : ∀ n U a,
    q • ((proEtaleRootsOfUnityDirectImageMap g (l ^ n)).hom.app U
      ((basis n).hom.hom.app U (coefficientRootSection S (l ^ n) U a))) =
      (basis n).hom.hom.app ((proEtaleBaseChange g).op.obj U)
        (coefficientRootSection S (l ^ n) ((proEtaleBaseChange g).op.obj U) a)

private instance rootFrameBaseFintype (D : FiniteFieldDatum.{u}) : Fintype D.k₀ :=
  Fintype.ofFinite D.k₀

private theorem geometric_frobenius_pow_card (D : FiniteFieldDatum.{u}) (x : D.k) :
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k x) ^ Nat.card D.k₀ = x := by
  have h := (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k).apply_symm_apply x
  simpa only [Nat.card_eq_fintype_card,
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic, AlgEquiv.aut_inv,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using h

private theorem geometric_global_root_scalar (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (z : D.kˣ) :
    let f := (D.geometricFiber X₀).hom
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ f.appTop).hom
    (Units.map (D.geometricFrobenius X₀).hom.appTop.hom.toMonoidHom
      (Units.map φ.toMonoidHom z)) ^ Nat.card D.k₀ = Units.map φ.toMonoidHom z := by
  let f := (D.geometricFiber X₀).hom
  let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ f.appTop).hom
  let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  have hproj : (D.geometricFrobenius X₀).hom ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) :=
    (D.galoisMap_projections X₀.hom γ).2
  have hΓ := congrArg (fun h ↦ h.appTop) hproj
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hΓ
  have hm : ((Scheme.ΓSpecIso (.of D.k)).inv ≫ f.appTop) ≫
      (D.geometricFrobenius X₀).hom.appTop =
    CommRingCat.ofHom γ.toRingHom ≫ ((Scheme.ΓSpecIso (.of D.k)).inv ≫ f.appTop) := by
    rw [Category.assoc, hΓ, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  have hm' := ConcreteCategory.congr_hom hm (z : D.k)
  change (D.geometricFrobenius X₀).hom.appTop.hom (φ (z : D.k)) = φ (γ (z : D.k)) at hm'
  apply Units.ext
  change ((D.geometricFrobenius X₀).hom.appTop.hom (φ (z : D.k))) ^ Nat.card D.k₀ = φ (z : D.k)
  rw [hm', ← map_pow, geometric_frobenius_pow_card]

/-- The actual geometric fibre has compatible finite root frames satisfying the
q-scaled equation for its geometric Frobenius.

Source: Weil I (2.2), compatible primitive roots and inverse arithmetic Frobenius.
(blueprint: lem-sf-coefficient-root-scalar-basis)

Proof: an algebraically closed field is strictly henselian and weakly contractible.
Choose the compatible primitive-root tower there. Map it to global functions on the
geometric fibre; its power relations and invertible differences are preserved.
The projection equation for the geometric Galois map and naturality of Gamma(Spec)
identify its action on these roots with the inverse arithmetic field Frobenius.
The latter followed by the qth power is the identity. Apply the normalized finite
root-basis calculation at every level. It gives actual basis isomorphisms with
both the root-value and q-scaled direct-image formulas. The roots' power equations
ensure that these are compatible frames of the tower. All statements include the
level with modulus one and the empty geometric fibre. -/
theorem coefficient_tate_root_frames (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Nonempty (CoefficientTateRootFrames (D.geometricFiber X₀).left l
      (Nat.card D.k₀) (D.geometricFrobenius X₀).hom) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : IsStrictlyHenselianLocalRing D.k :=
    ⟨IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (IsLocalRing.residue D.k)
      ⟨(IsLocalRing.residue D.k).injective, IsLocalRing.residue_surjective⟩)⟩
  have := IsStrictlyHenselianLocalRing.isWContractibleRing D.k
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hl₀ : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
  have hlk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hl₀.map (algebraMap D.k₀ D.k)
  obtain ⟨z, hz0, hs, hz, hd⟩ := ProEtale.exists_primitive_unit_tower D.k l hlk
  let S := (D.geometricFiber X₀).left
  let f := (D.geometricFiber X₀).hom
  let φ : D.k →+* Γ(S, ⊤) := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ f.appTop).hom
  let zS : ℕ → Γ(S, ⊤)ˣ := fun n ↦ Units.map φ.toMonoidHom (z n)
  have hzS (n : ℕ) : zS n ^ (l ^ n) = 1 := by
    simpa only [zS, ← map_pow, map_one] using congrArg (Units.map φ.toMonoidHom) (hz n)
  have hsS (n : ℕ) : zS (n + 1) ^ l = zS n := by
    simpa only [zS, ← map_pow] using congrArg (Units.map φ.toMonoidHom) (hs n)
  have hdS (n i : ℕ) (hi : i < l ^ n) (j : ℕ) (hj : j < l ^ n) (hij : i ≠ j) :
      IsUnit ((zS n : Γ(S, ⊤)) ^ i - (zS n : Γ(S, ⊤)) ^ j) := by
    change IsUnit (φ (z n : D.k) ^ i - φ (z n : D.k) ^ j)
    simpa only [map_sub, map_pow] using (hd n i hi j hj hij).map φ
  have hγ (n : ℕ) :
      (Units.map (D.geometricFrobenius X₀).hom.appTop.hom.toMonoidHom (zS n)) ^
        Nat.card D.k₀ = zS n := geometric_global_root_scalar D X₀ (z n)
  have he (n : ℕ) := by
    have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact coefficient_root_scalar_basis S (l ^ n) (D.geometricFrobenius X₀).hom
      (Nat.card D.k₀) (zS n) (hzS n) (hdS n) (hγ n)
  refine ⟨{ roots := zS
            zero := ?_
            step := hsS
            power := hzS
            differences := hdS
            frobenius_power := hγ
            basis := fun n ↦ (he n).choose
            value := fun n U a ↦ ((he n).choose_spec U a).1
            scalar := fun n U a ↦ ((he n).choose_spec U a).2 }⟩
  simp only [zS, hz0, map_one]

/-- Matching finite constant coordinates give the scalar equation in the root limit.
Source: Weil I (2.2), inverse-limit construction of the Tate line
(blueprint: lem-sf-coefficient-root-scalar-basis).
Proof: project to every finite root sheaf. Projection commutes with direct image
and natural multiplication. Substitute the two coordinate formulas and apply the
finite-frame scalar equation. Joint injectivity of the limit projections gives
the asserted equality, including on the empty scheme. -/
theorem CoefficientTateRootFrames.limit_scalar
    (S : Scheme.{u}) (l q : ℕ) [Fact l.Prime] (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) (V : S.ProEt)
    (x : (purTwistZlOne S l).obj.obj (op V))
    (y : (purTwistZlOne S l).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (a : ℕ → ℕ)
    (hx : ∀ n,
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op V) x =
        (A.basis (n + 1)).hom.hom.app (op V)
          (coefficientRootSection S (l ^ (n + 1)) (op V) (a n)))
    (hy : ∀ n,
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op ((proEtaleBaseChange g).obj V)) y =
        (A.basis (n + 1)).hom.hom.app (op ((proEtaleBaseChange g).obj V))
          (coefficientRootSection S (l ^ (n + 1))
            (op ((proEtaleBaseChange g).obj V)) (a n))) :
    q • FrobeniusCoefficientTwists.rootSection l g V x = y := by
  have ht : FrobeniusCoefficientTwists.rootTowerMap l g =
      ((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose := by
    apply NatTrans.ext
    funext n
    exact (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose_spec n.unop).symm
  have hr : (Scheme.root_direct l g).hom.app (op V) x =
      FrobeniusCoefficientTwists.rootSection l g V x := by
    unfold FrobeniusCoefficientTwists.rootSection FrobeniusCoefficientTwists.rootLineMap
    rw [ht]
    rfl
  rw [← hr]
  apply Scheme.root_section_ext l
  intro n
  rw [map_nsmul]
  exact (congrArg (fun t ↦ q • t)
    (Scheme.root_direct_project_value l g n (op V) x)).trans
    ((congrArg (fun t ↦ q •
      (proEtaleRootsOfUnityDirectImageMap g (l ^ (n + 1))).hom.app (op V) t)
      (hx n)).trans ((A.scalar (n + 1) (op V) (a n)).trans (hy n).symm))

end WeilConjectures.NativeCoefficientCohomology
