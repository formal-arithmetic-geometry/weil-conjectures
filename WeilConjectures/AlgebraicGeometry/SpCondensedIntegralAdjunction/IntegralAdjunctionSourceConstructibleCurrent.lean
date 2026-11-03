/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullTensorConstructible
import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement

/-! # Constructibility of the native integral purity source

Source: current blueprint, integral-adjunction-bijection, Purity paragraph;
prop-weil-twist-preserves, integral local-line argument.
(blueprint: lem-sp-current-integral-twisted-source-constructible). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.SpCondensedIntegralAdjunction

open IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]



private noncomputable def sourcePointIntegerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCondensedRing l E) ≅ Mon.mk (DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e : latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
    RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
      _ _ (fun _ ↦ Iff.rfl)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheafOfUniverse (latticeCoefficientIntegers l E) ≅
      DerivedNakayama.integerRingSheaf l E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let cAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso c
  have : IsMonHom cAb.hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  have : IsMonHom cAb.inv := Sheaf.isMonHom_sheafCompose_map _ c.inv
  exact
    { hom := Mon.ofHom cAb.hom
      inv := Mon.ofHom cAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact cAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact cAb.inv_hom_id }


attribute [local irreducible] sourcePointIntegerIso

private theorem sourceComparisonTransport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    (X : Scheme.{u})
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) :
    IsConstructibleModuleObject (condensedRingObj Λ' X) M ↔
      IsConstantModelConstructible Λ' X M := by
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let ψ := (upperStarFromPoint X).map φ
  let N := (Mod.comap ψ).obj M
  have er : (Mod.comap (inv ψ)).obj N ≅ M :=
    ((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app M
  constructor
  · intro hM
    have hN := (h N).mp (_root_.constructible_comap ψ hM)
    have hback := constructible_comap (inv φ) X N hN
    apply constructible_iso _ hback
    exact ((Mod.comapComp ((upperStarFromPoint X).map (inv φ)) ψ).symm ≪≫
      Mod.comapCongr (by
        dsimp only [ψ]
        rw [← Functor.map_comp]
        simp) ≪≫ Mod.comapId _).app M
  · intro hM
    exact _root_.constructible_of_iso er
      (_root_.constructible_comap (inv ψ) ((h N).mpr (constructible_comap φ X M hM)))

set_option maxHeartbeats 1600000 in
-- Transport the local-model predicate across the two presentations of the integer ring.
/-- Ordinary derived pullback, positive integral Tate twist and the purity shift
preserve the category defined by finite constant local models of cohomology.

Source: current blueprint integral-adjunction-bijection, Purity paragraph;
prop-weil-twist-preserves, integral local-line argument.

Proof: the canonical lattice/spectral integer-ring isomorphism transports finite
constant local models by restriction of scalars. The integral LFP comparison then
identifies the two cohomology predicates on X. Ordinary derived pullback preserves
bounded constructibility by
integral-direct-image-tower (3). Compatible primitive roots trivialize the integral
Tate line on a pro-etale cover. Its nonnegative powers are again trivial on that
cover; the regular point module is finitely presented, so these trivializations
give finite constant local models. Placing the line in degree zero gives a bounded
constructible complex. Integral tensor closure therefore applies to the pullback
and this degree-zero line. Finally cohomological shift translates the finite
cohomology interval and only reindexes the same constructible cohomology objects.
This proof includes the zero twist, the zero complex and the empty scheme.
(blueprint: lem-sp-current-integral-twisted-source-constructible).
-/
theorem integral_twisted_source_constructible
    (k : Type u) [Field k] (pchar : ℕ) (hp : 0 < pchar)
    [hchar : CharP k pchar] (hne : l ≠ pchar)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) :
    ∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        ((source l E f d).obj K) := by
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  have hring : ringChar k = pchar := @ringChar.eq k _ pchar hchar
  have hpprime : pchar.Prime :=
    (CharP.char_is_prime_or_zero k pchar).resolve_right (by omega)
  let : Fact pchar.Prime := ⟨hpprime⟩
  let : Fact (ringChar k).Prime := ⟨by simpa only [hring] using hpprime⟩
  let : Fact (ringChar k ≠ l) := ⟨by rw [hring]; exact hne.symm⟩
  let := spectralNorm.normedField (Padic l) E
  let : MonObj (spIntegralCondensed l E) :=
    Profinite.continuousMapRingObjOfUniverseMonObj (Padic.coefficientExtensionIntegers l E)
  let : IsCommMonObj (spIntegralCondensed l E) :=
    Profinite.isCommMonObj_continuousMapRingObjOfUniverse
      (Padic.coefficientExtensionIntegers l E)
  let : MonObj (condensedRingObj (spIntegralCondensed l E) X) :=
    (upperStarFromPoint X).monObjObj (spIntegralCondensed l E)
  let coeffIso : Mon.mk (integralCondensedRing l E) ≅ Mon.mk (spIntegralCondensed l E) :=
    sourcePointIntegerIso l E ≪≫ eqToIso (IntegralConstantModel.pointEquality l E)
  let (x : X) : Invertible (l : X.residueField x) := by
    let φ : k →+* X.residueField x :=
      (X.evaluation ⊤ x (by trivial)).hom.comp
        ((X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    exact (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        (isUnit_iff_ne_zero.mpr
          (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime) (by
            simpa only [hring] using hne.symm))).map φ).invertible
  have hmod (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (spIntegralCondensed l E) X)) :
      IsConstructibleModuleObject (condensedRingObj (spIntegralCondensed l E) X) N ↔
        IsConstantModelConstructible (spIntegralCondensed l E) X N :=
    sourceComparisonTransport coeffIso X (integralLfpConstantModelComparison l E X) N
  have hcmp (M : Integral l E X) :
      constantModelBoundedConstructible (spIntegralCondensed l E) X M ↔
        boundedConstructible (condensedRingObj (spIntegralCondensed l E) X) M := by
    constructor
    · intro h
      exact ⟨h.1, fun n ↦ (hmod _).mpr (h.2 n)⟩
    · intro h
      exact ⟨h.1, fun n ↦ (hmod _).mp (h.2 n)⟩
  intro K
  have hK := (integral_pull_tensor_constructible l E k X Y f).1 K
  obtain ⟨L, he, hfin⟩ := (twist_preserves_native_finiteness l E X).2.1
  have ht : boundedConstructible (condensedRingObj (spIntegralCondensed l E) X)
      ((coefficientIntegralTwistFunctor l E X (d : ℤ)).obj ((pull l E f).obj K.obj)) := by
    change boundedConstructible (condensedRingObj (twistIntegralRing l E) X)
      (((pull l E f).obj K.obj) ⊗ (DerivedCategory.singleFunctor _ 0).obj
        (coefficientSignedTwist X _ (coefficientIntegralTwistOne l E X) (d : ℤ)))
    rw [congrFun he (d : ℤ)]
    exact hfin.boundedConstructible _ _ ((hcmp _).mp hK)
  apply (hcmp _).mpr
  exact ⟨DerivedCategory.TStructure.t.bounded.le_shift _ _ ht.1, fun n ↦
    IsConstructibleModuleObject.of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso (2 * (d : ℤ)) n
        (2 * (d : ℤ) + n) rfl).app _).symm (ht.2 _)⟩

end AlgebraicGeometry.ProEtale.SpCondensedIntegralAdjunction
