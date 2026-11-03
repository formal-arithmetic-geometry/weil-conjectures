/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleKummerLimitBoundary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleSupportedHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-! # Supported divisor classes from the full compatible-root boundary

Source: latest blueprint part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-divisor-class.proof.md,
(b), the relative class and anticommuting boundaries; vector-bundle-thom proof,
Steps 1 and 3 (blueprint: lem-pur-supported-kummer-root-realization).

Ext is Mathlib's presentation of the displayed derived Hom. Its universe is
u+2 for internal modules and u+1 for abelian sheaves. The supported transpose
is explicitly forgetting scalars followed by the supported coefficient unit.
The abelian arrow is formed before any coefficient is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.SupportedKummer
open CondensedRing.Admissible

private theorem roots_transition_normalized (X : Scheme.{u}) (N m : ℕ)
    (hN : 0 < N) (hm : 0 < m) :
    rootsOfUnitySheafPow X N m ≫ (PurityTransport.rootComparison X N).hom =
      (PurityTransport.rootComparison X (m * N)).hom ≫
        proEtaleRootsOfUnityTransition X N (m * N) hN (Nat.mul_pos hm hN)
          (dvd_mul_left N m) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    (proEtaleRootsOfUnitySheaf X N).property
  change toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N)) ≫
      sheafifyMap (ProEt.topology X)
        (Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
          (CommRingCat.rootsOfUnityPow N m)) ≫ (PurityTransport.rootComparison X N).hom.hom = _
  rw [← Category.assoc, ← toSheafify_naturality]
  ext U z
  apply (proEtaleRootsOfUnitySections X N U).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  have hleft := (PurityTransport.rootComparison_existsUnique X N).exists.choose_spec U
    ((Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow N m)).app U z)
  have hright := roots_transition_value X N (m * N) hN (Nat.mul_pos hm hN)
    (dvd_mul_left N m) U
      ((PurityTransport.rootComparison X (m * N)).hom.hom.app U
        ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z))
  have hnorm := (PurityTransport.rootComparison_existsUnique X (m * N)).exists.choose_spec U z
  change proEtaleRootsOfUnitySections X (m * N) U
    ((PurityTransport.rootComparison X (m * N)).hom.hom.app U
      ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z)) =
    z.down at hnorm
  rw [hnorm] at hright
  rw [Nat.mul_div_cancel _ hN] at hright
  exact (congrArg (fun x ↦ x.toMul.val) hleft).trans hright.symm

private theorem roots_transition_normalized_cast (X : Scheme.{u}) (N m K : ℕ)
    (hN : 0 < N) (hm : 0 < m) (hK : 0 < K) (hd : N ∣ K) (e : K = m * N) :
    (eqToHom (congrArg (rootsOfUnitySheaf X) e) ≫ rootsOfUnitySheafPow X N m) ≫
        (PurityTransport.rootComparison X N).hom =
      (PurityTransport.rootComparison X K).hom ≫
        proEtaleRootsOfUnityTransition X N K hN hK hd := by
  subst K
  simpa only [eqToHom_refl, Category.id_comp] using
    roots_transition_normalized X N m hN hm

private theorem rootLevel_step (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (n : ℕ) :
    (tateModuleTransition X ell (n + 1)).hom ≫ ((kummerData ell X).level n).hom =
      ((kummerData ell X).level (n + 1)).hom ≫
        (compatibleRootsTower ell X).map (homOfLE (Nat.le_succ n)).op := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X
  let g (r : ℕ) := (λ_ (rootsOfUnitySheaf X (ell ^ (r + 1)))).inv ≫
    η[R] ▷ rootsOfUnitySheaf X (ell ^ (r + 1))
  have hs (r : ℕ) : g r ≫ ((kummerData ell X).level r).hom =
      (PurityTransport.rootComparison X (ell ^ (r + 1))).hom := by
    simpa only [g, R, Category.assoc] using (kummerData ell X).level_spec r
  have hg (r : ℕ) : g r = (PurityTransport.rootComparison X (ell ^ (r + 1))).hom ≫
      ((kummerData ell X).level r).inv := by
    apply (cancel_mono ((kummerData ell X).level r).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      hs r
  have : IsIso (g (n + 1)) := by
    rw [hg]
    infer_instance
  let f : rootsOfUnitySheaf X (ell ^ (n + 1 + 1)) ⟶
      rootsOfUnitySheaf X (ell ^ (n + 1)) :=
    eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ell ^ (n + 1)) ell
  have hnat : g (n + 1) ≫ R ◁ f = f ≫ g n := by
    exact ((Mod.freeForgetAdjunction R).unit.naturality f).symm
  have hroot : f ≫ (PurityTransport.rootComparison X (ell ^ (n + 1))).hom =
      (PurityTransport.rootComparison X (ell ^ (n + 1 + 1))).hom ≫
        (compatibleRootsTower ell X).map (homOfLE (Nat.le_succ n)).op := by
    dsimp only [f, compatibleRootsTower, SpTowerClasses.roots,
      Scheme.proEtaleRootsOfUnityTower]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact roots_transition_normalized_cast X (ell ^ (n + 1)) ell _
      (pow_pos (Fact.out : ell.Prime).pos _) (Fact.out : ell.Prime).pos _ _
      (pow_succ' ell (n + 1))
  apply (cancel_epi (g (n + 1))).mp
  change g (n + 1) ≫ R ◁ f ≫ ((kummerData ell X).level n).hom = _
  rw [← Category.assoc, hnat, Category.assoc, hs n, ← Category.assoc, hs (n + 1)]
  exact hroot

/-- The two root-limit presentations are identified by every positive coordinate.
Source: compatible-root-boundary, native linear realization; divisor-class root data
(blueprint: lem-pur-supported-kummer-root-realization).
Proof: insert a compatible root in each finite Tate level by z tensor one.
The native level comparison identifies this insertion with the root itself.
These maps give inverse cones on the positive cofinal subsystem. Their limits
are inverse; equality of every coordinate gives uniqueness. -/
theorem rootComparison_existsUnique (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :
    ∃! e : compatibleRoots ell X ≅ (tateModule X ell).X,
      ∀ n : ℕ, e.hom ≫ (limit.π (tateModuleSystem X ell) (op (n + 1))).hom ≫
        ((kummerData ell X).level n).hom = compatibleRootsCoordinate ell X n := by
  let shift : ℕᵒᵖ ⥤ ℕᵒᵖ := (show Monotone (fun n : ℕ ↦ n + 1) from
    fun _ _ h ↦ Nat.add_le_add_right h 1).functor.op
  have hfinal : ((show Monotone (fun n : ℕ ↦ n + 1) from
      fun _ _ h ↦ Nat.add_le_add_right h 1).functor).Final :=
    (Monotone.final_functor_iff _).mpr (fun n ↦ ⟨n, Nat.le_succ n⟩)
  let U : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X) ⥤
      Sheaf (ProEt.topology X) Ab.{u + 1} := Mod.forget _
  let c := (U.mapCone (limit.cone (tateModuleSystem X ell))).whisker shift
  have hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv shift _).symm
    (isLimitOfPreserves U (limit.isLimit (tateModuleSystem X ell)))
  let t : shift ⋙ tateModuleSystem X ell ⋙ U ⟶ compatibleRootsTower ell X :=
    NatTrans.ofOpSequence (fun n ↦ ((kummerData ell X).level n).hom) (fun n ↦ by
      change ((tateModuleSystem X ell).map (homOfLE (Nat.le_succ (n + 1))).op).hom ≫
        ((kummerData ell X).level n).hom = _
      simp only [tateModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
      exact rootLevel_step ell X n)
  have : ∀ j, IsIso (t.app j) := fun j ↦ ((kummerData ell X).level j.unop).isIso_hom
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let d := (Cone.postcompose t).obj c
  have hd : IsLimit d := (IsLimit.postcomposeHomEquiv (asIso t) c).symm hc
  let e : compatibleRoots ell X ≅ (tateModule X ell).X :=
    (limit.isLimit (compatibleRootsTower ell X)).conePointUniqueUpToIso hd
  have he (n : ℕ) : e.hom ≫
      (limit.π (tateModuleSystem X ell) (op (n + 1))).hom ≫
        ((kummerData ell X).level n).hom = compatibleRootsCoordinate ell X n :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ hd (op n)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply hd.hom_ext
  rintro ⟨n⟩
  exact (he' n).trans (he n).symm

end AlgebraicGeometry.ProEtale.SupportedKummer
