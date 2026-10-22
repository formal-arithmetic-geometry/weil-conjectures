/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtalePointMonodromy
public import Mathlib.Algebra.Polynomial.Laurent
import Sheaf.AlgebraicGeometry.QuadraticKummerAction
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The generic monodromy witness on the punctured line

Source: blueprint `lem-trf-devissage-generation`, proof Step 3.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

attribute [local irreducible] finiteCoefficientModuleStalkFunctor

/-- The punctured line used for the quadratic Kummer cover.
Source: blueprint `lem-trf-devissage-generation`, Step 3
(blueprint: lem-trf-kummer-monodromy). -/
def trfKummerBase (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (LaurentPolynomial k))

/-- The usual structure morphism of the punctured line.
Source: blueprint `lem-trf-devissage-generation`, Step 3
(blueprint: lem-trf-kummer-monodromy). -/
def trfKummerStructureMap (k : Type u) [Field k] : trfKummerBase k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- On the punctured line in characteristic five, quadratic Kummer monodromy
separates a flat lisse generator from constant stratum extensions.
Source: blueprint `lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-kummer-monodromy).

Proof: put R=k[t,t^-1], K=k(t), and Omega an algebraic closure of K.
The polynomial z^2-t has no root in K by the parity of rational-function degrees;
its two roots in Omega are therefore exchanged by a K-automorphism sigma. The
canonical localization map R to K gives a geometric point of X=Spec R fixed by
sigma. The R-algebra R[z]/(z^2-t) is finite free by its monic presentation and
etale because 2 and t are units. Evaluating z at the chosen root gives a lift of
the geometric point to this cover, moved by sigma and fixed by its square.
Apply the finite-etale point-monodromy lemma. Its fibre functor is exact, and the
permutation sheaf of this cover has a nonzero anti-invariant vector in its stalk;
monodromy minus identity fixes that vector in characteristic three. Constants on
locally closed strata have trivial point monodromy, including their zero stalks. -/
theorem exists_trf_kummer_monodromy
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 5]
    (A : Type u) [CommRing A] [Finite A] [CharP A 3] [Nontrivial A] :
    let X := trfKummerBase k
    ∃ F : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
        ModuleCat.{u + 1} (ULift.{u + 1, u} A),
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
      ∃ (t : F ⟶ F) (L : proEtaleRingModules X (proEtaleConstantRing X A)),
        SeparatingPointMonodromy X A F t L := by
  let R := LaurentPolynomial k
  let K := RatFunc k
  let Ω := AlgebraicClosure K
  have hu : ∀ z : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (algebraMap (Polynomial k) K z) := by
    rintro ⟨z, n, rfl⟩
    rw [map_pow, RatFunc.algebraMap_X]
    exact (isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero).pow n
  let ι : R →+* K := IsLocalization.lift hu
  have hι (p : Polynomial k) : ι (Polynomial.toLaurent p) =
      algebraMap (Polynomial k) K p := by
    change ι (algebraMap (Polynomial k) R p) = _
    exact IsLocalization.lift_eq hu p
  let e : R →+* Ω := (algebraMap K Ω).comp ι
  let X := trfKummerBase k
  let x : Spec (.of Ω) ⟶ X := Spec.map (CommRingCat.ofHom e)
  obtain ⟨r, σ, hr, hσ, hrneg⟩ := quadratic_kummer_generic_action k
  have heT : e (LaurentPolynomial.T 1) = algebraMap K Ω RatFunc.X := by
    change algebraMap K Ω (ι (LaurentPolynomial.T 1)) = _
    rw [← Polynomial.toLaurent_X, hι, RatFunc.algebraMap_X]
  have hσe : σ.toRingHom.comp e = e := by
    apply RingHom.ext
    intro z
    exact σ.commutes (ι z)
  let s : Spec (.of Ω) ≅ Spec (.of Ω) :=
    Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
  have hs : s.hom ≫ x = x := by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom e) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσe]
  let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.C (LaurentPolynomial.T 1)
  let B := AdjoinRoot p
  have hm : p.Monic := Polynomial.monic_X_pow_sub_C _ (by decide)
  let : Module.Finite R B := hm.finite_adjoinRoot
  have htwo : IsUnit (2 : R) := by
    exact (isUnit_iff_ne_zero.mpr (show (2 : k) ≠ 0 from
      (CharP.cast_eq_zero_iff k 5 2).not.mpr (by decide))).map LaurentPolynomial.C
  let : Algebra.Etale R B :=
    AdjoinRoot.etale_X_pow_sub_C (by decide) htwo (LaurentPolynomial.isUnit_T 1)
  let π : Spec (.of B) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let : IsFinite π := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  let : Etale π := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hrp : p.eval₂ e r = 0 := by
    dsimp only [p]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, hr, heT, sub_self]
  let yr : B →+* Ω := AdjoinRoot.lift e r hrp
  let y : Spec (.of Ω) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom yr)
  have hyr : yr.comp (algebraMap R B) = e := AdjoinRoot.lift_comp_of hrp
  have hy : y ≫ π = x := by
    dsimp [y, π, x]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hyr]
  have hmove : s.hom ≫ y ≠ y := by
    intro h
    have hh : σ.toRingHom.comp yr = yr := by
      have hc : CommRingCat.ofHom (σ.toRingHom.comp yr) = CommRingCat.ofHom yr := by
        apply Spec.map_injective
        change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom yr) = Spec.map (CommRingCat.ofHom yr) at h
        simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using h
      exact congrArg CommRingCat.Hom.hom hc
    have hroot := RingHom.congr_fun hh (AdjoinRoot.root p)
    have : -r = r := by
      change σ (AdjoinRoot.lift e r hrp (AdjoinRoot.root p)) =
        AdjoinRoot.lift e r hrp (AdjoinRoot.root p) at hroot
      rw [AdjoinRoot.lift_root, hσ] at hroot
      exact hroot
    exact hrneg this.symm
  have htwice : s.hom ≫ s.hom ≫ y = y := by
    have hh : σ.toRingHom.comp (σ.toRingHom.comp yr) = yr := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro z
        change σ (σ (yr (algebraMap R B z))) = yr (algebraMap R B z)
        rw [show yr (algebraMap R B z) = e z from RingHom.congr_fun hyr z]
        change σ (σ (algebraMap K Ω (ι z))) = algebraMap K Ω (ι z)
        rw [σ.commutes, σ.commutes]
      · change σ (σ (AdjoinRoot.lift e r hrp (AdjoinRoot.root p))) =
          AdjoinRoot.lift e r hrp (AdjoinRoot.root p)
        rw [AdjoinRoot.lift_root, hσ, map_neg, hσ, neg_neg]
    dsimp [s, y]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact hh
  let F := finiteCoefficientModuleStalkFunctor x A
  let t := genericStalkMonodromy A x σ.toRingEquiv hs
  obtain ⟨L, hL⟩ :=
    finite_etale_point_monodromy π Ω x σ.toRingEquiv hs y hy hmove htwice A
  exact ⟨F, finiteCoefficientModuleStalkFunctorAdditive x A,
    (proEtaleCoefficientStalk_exact A x).1, (proEtaleCoefficientStalk_exact A x).2,
    t, L, hL⟩

end AlgebraicGeometry
