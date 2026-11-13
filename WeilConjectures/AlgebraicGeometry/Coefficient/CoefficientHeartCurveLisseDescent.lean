/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-!
# Lisse condensed-coefficient descent through a surjective closed immersion

Source: Stacks Project, Tag 09AB and Tag 09BK.

The two comparison isomorphisms below specify the finite-free normalization and the
composition comparison used in compatibility with the prescribed trivializations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical finite-free coefficient comparison: preserve the finite biproduct,
then identify the transported regular module using extension along the Cartesian
coefficient isomorphism, restriction along its inverse, and the coefficient map itself.
This also constructs the rank-zero comparison without a choice of basis.
Source: Stacks Project Tag 09AB. -/
def coefficientHeartFiniteFreePullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    (CondensedRing.upperStar Λ f).obj (Mod.finiteFree (condensedRingObj Λ X) n) ≅
      Mod.finiteFree (condensedRingObj Λ Y) n :=
  (CondensedRing.upperStar Λ f).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ X)) ≪≫
    biproduct.mapIso (fun _ ↦
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app _ ≪≫
        Mod.regularIsoOfIsIso (condensedPullbackHom Λ f))

/-- Canonical comparison from the pullback along the closed fibre of a covering member
to the iterated pullback through its specified refinement map. Only the commutativity
witness is supplied; every isomorphism is the existing coefficient-module composition
isomorphism or transport along that equality.
Source: Stacks Project Tag 09AB. -/
def coefficientHeartRefinementPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W T B C P : Scheme.{u}}
    (t : T ⟶ W) (b : B ⟶ W) (c : C ⟶ T) (q : P ⟶ B) (r : P ⟶ C)
    (h : q ≫ b = r ≫ c ≫ t)
    (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) :
    (CondensedRing.upperStar Λ q).obj ((CondensedRing.upperStar Λ b).obj M) ≅
      (CondensedRing.upperStar Λ r).obj
        ((CondensedRing.upperStar Λ c).obj ((CondensedRing.upperStar Λ t).obj M)) :=
  ((CondensedRing.upperStarComp Λ q b).app M).symm ≪≫
    eqToIso (congrArg (fun f : P ⟶ W ↦ (CondensedRing.upperStar Λ f).obj M) h) ≪≫
    (CondensedRing.upperStarComp Λ r (c ≫ t)).app M ≪≫
    (CondensedRing.upperStar Λ r).mapIso ((CondensedRing.upperStarComp Λ c t).app M)

-- Keep the actual pullback and its canonical comparisons abstract in the descent proof.
attribute [local irreducible] CondensedRing.upperStar coefficientHeartFiniteFreePullbackIso
  coefficientHeartRefinementPullbackIso

private theorem small_closed_cover_refinement {W T : Scheme.{u}} (t : T ⟶ W)
    [IsClosedImmersion t] [Surjective t]
    (C : Scheme.Cover.{v} Scheme.proetalePrecoverage T) :
    ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage W, ∀ b : B.I₀,
      ∃ (a : C.I₀) (f : pullback (B.f b) t ⟶ C.X a),
        f ≫ C.f a = pullback.snd (B.f b) t := by
  classical
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage := by
    change Precoverage.Small (Scheme.propQCPrecoverage @WeaklyEtale)
    infer_instance
  let C₀ : Scheme.Cover.{u} Scheme.proetalePrecoverage T := C.restrictIndexOfSmall.{u}
  let j : C₀.I₀ → C.I₀ := Precoverage.ZeroHypercover.Small.restrictFun.{u} C
  obtain ⟨B, hB⟩ := Scheme.exists_cover_refinement_surjective_closed t C₀
  refine ⟨B, fun b ↦ ?_⟩
  obtain ⟨a₀, P, q, p, g, hsq, hg⟩ := hB b
  let a := j a₀
  let f : pullback (B.f b) t ⟶ C.X a := hsq.isoPullback.inv ≫ g
  have hf : f ≫ C.f a = pullback.snd (B.f b) t := by
    change (hsq.isoPullback.inv ≫ g) ≫ C₀.f a₀ = _
    rw [Category.assoc, hg, hsq.isoPullback_inv_snd]
  exact ⟨a, f, hf⟩

private theorem exists_pullback_cover {W T : Scheme.{u}} (t : T ⟶ W)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage W) :
    ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage T,
      ∃ (a : B.I₀ → C.I₀) (q : ∀ b, B.X b ⟶ C.X (a b)),
        ∀ b, B.f b ≫ t = q b ≫ C.f (a b) := by
  exact ⟨C.pullback₁ t, id, fun b ↦ pullback.snd t (C.f b), fun _ ↦ pullback.condition⟩

-- Work with an abstract functor so the inverse identities do not unfold sheaf pullbacks.
private theorem lift_compatible_iso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} {N : D}
    (β : F.obj A ≅ N) (κ : F.obj B ≅ N) :
    ∃ ψ : A ≅ B, F.map ψ.hom ≫ κ.hom = β.hom := by
  refine ⟨F.preimageIso (β ≪≫ κ.symm), ?_⟩
  rw [Functor.preimageIso_hom, Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem compatible_trivializations
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W T : Scheme.{u}} (t : T ⟶ W)
    [IsClosedImmersion t] [Surjective t]
    (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) :
    ∀ (C : Scheme.Cover.{v} Scheme.proetalePrecoverage T) (r : C.I₀ → ℕ)
      (φ : ∀ a : C.I₀, (CondensedRing.upperStar Λ (C.f a)).obj
        ((CondensedRing.upperStar Λ t).obj M) ≅ Mod.finiteFree (condensedRingObj Λ (C.X a))
          (r a)),
      ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage W, ∀ b : B.I₀,
        ∃ (a : C.I₀) (f : pullback (B.f b) t ⟶ C.X a)
          (hf : f ≫ C.f a = pullback.snd (B.f b) t)
          (ψ : (CondensedRing.upperStar Λ (B.f b)).obj M ≅
            Mod.finiteFree (condensedRingObj Λ (B.X b)) (r a)),
          (CondensedRing.upperStar Λ (pullback.fst (B.f b) t)).map ψ.hom ≫
              (coefficientHeartFiniteFreePullbackIso Λ (pullback.fst (B.f b) t) (r a)).hom =
            (coefficientHeartRefinementPullbackIso Λ t (B.f b) (C.f a)
                (pullback.fst (B.f b) t) f
                ((pullback.condition (f := B.f b) (g := t)).trans
                  (congrArg (fun p : pullback (B.f b) t ⟶ T ↦ p ≫ t) hf).symm) M).hom ≫
              (CondensedRing.upperStar Λ f).map (φ a).hom ≫
              (coefficientHeartFiniteFreePullbackIso Λ f (r a)).hom := by
  classical
  intro C r φ
  obtain ⟨B, hB⟩ := small_closed_cover_refinement t C
  refine ⟨B, fun b ↦ ?_⟩
  obtain ⟨a, f, hf⟩ := hB b
  refine ⟨a, f, hf, ?_⟩
  let q₀ := pullback.fst (B.f b) t
  let F := CondensedRing.upperStar Λ q₀
  have : F.IsEquivalence := condensedSurjectiveClosedPullback_isEquivalence Λ q₀
  let γ := coefficientHeartRefinementPullbackIso Λ t (B.f b) (C.f a) q₀ f
    ((pullback.condition (f := B.f b) (g := t)).trans
      (congrArg (fun p : pullback (B.f b) t ⟶ T ↦ p ≫ t) hf).symm) M
  let β := γ ≪≫ (CondensedRing.upperStar Λ f).mapIso (φ a) ≪≫
    coefficientHeartFiniteFreePullbackIso Λ f (r a)
  let κ := coefficientHeartFiniteFreePullbackIso Λ q₀ (r a)
  exact lift_compatible_iso F β κ

/-- Lissity descends and ascends through a surjective closed immersion, with a covering
refinement that lifts every specified finite-free trivialization, in its specified rank.

Source: Stacks Project Tag 09AB, Tag 09BK. -/
theorem coefficientHeart_curve_lisse_descent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W T : Scheme.{u}} (t : T ⟶ W)
    [IsClosedImmersion t] [Surjective t]
    (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) :
    (IsLisseCoefficientModule Λ M ↔
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ t).obj M)) ∧
    ∀ (C : Scheme.Cover.{v} Scheme.proetalePrecoverage T) (r : C.I₀ → ℕ)
      (φ : ∀ a : C.I₀, (CondensedRing.upperStar Λ (C.f a)).obj
        ((CondensedRing.upperStar Λ t).obj M) ≅ Mod.finiteFree (condensedRingObj Λ (C.X a))
          (r a)),
      ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage W, ∀ b : B.I₀,
        ∃ (a : C.I₀) (f : pullback (B.f b) t ⟶ C.X a)
          (hf : f ≫ C.f a = pullback.snd (B.f b) t)
          (ψ : (CondensedRing.upperStar Λ (B.f b)).obj M ≅
            Mod.finiteFree (condensedRingObj Λ (B.X b)) (r a)),
          (CondensedRing.upperStar Λ (pullback.fst (B.f b) t)).map ψ.hom ≫
              (coefficientHeartFiniteFreePullbackIso Λ (pullback.fst (B.f b) t) (r a)).hom =
            (coefficientHeartRefinementPullbackIso Λ t (B.f b) (C.f a)
                (pullback.fst (B.f b) t) f
                ((pullback.condition (f := B.f b) (g := t)).trans
                  (congrArg (fun p : pullback (B.f b) t ⟶ T ↦ p ≫ t) hf).symm) M).hom ≫
              (CondensedRing.upperStar Λ f).map (φ a).hom ≫
              (coefficientHeartFiniteFreePullbackIso Λ f (r a)).hom := by
  classical
  constructor
  · constructor
    · rintro ⟨C, hC⟩
      obtain ⟨B, a, q, hs⟩ := exists_pullback_cover t C
      refine ⟨B, fun b ↦ ?_⟩
      obtain ⟨n, ⟨e⟩⟩ := hC (a b)
      refine ⟨n, ⟨?_⟩⟩
      exact ((CondensedRing.upperStarComp Λ (B.f b) t).app M).symm ≪≫
        eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) (hs b)) ≪≫
        (CondensedRing.upperStarComp Λ (q b) (C.f (a b))).app M ≪≫
        (CondensedRing.upperStar Λ (q b)).mapIso e ≪≫
        coefficientHeartFiniteFreePullbackIso Λ (q b) n
    · rintro ⟨C, hC⟩
      choose r hφ using hC
      let φ := fun a ↦ Classical.choice (hφ a)
      obtain ⟨B, hB⟩ := compatible_trivializations Λ t M C r φ
      refine ⟨B, fun b ↦ ?_⟩
      obtain ⟨a, f, hf, ψ, hψ⟩ := hB b
      exact ⟨r a, ⟨ψ⟩⟩
  · exact compatible_trivializations Λ t M

end AlgebraicGeometry.ProEtale
