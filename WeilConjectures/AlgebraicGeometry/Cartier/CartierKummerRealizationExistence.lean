/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionModulus
import WeilConjectures.AlgebraicGeometry.Cartier.CartierSourceUnitSquare
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedComparisons
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedCoherence
import WeilConjectures.AlgebraicGeometry.Curve.KummerTransition

/-! # Existence of a simultaneous Cartier Kummer realization

Source: blueprint, final paragraph of lem-amb-cartier-kummer-map.proof.md.
(blueprint: lem-route-cartier-kummer-realization-exists)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private instance coefficientFinite (n : ℕ) : Finite (finiteTateCoefficient l E n) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  infer_instance

private theorem root_power_value (T : Scheme.{u}) (m m' d : ℕ)
    (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
    (hq : q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = d • kernel.ι (m' • 𝟙 T.gmSheaf))
    (U : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf m').obj.obj U) :
    finiteTateEtaleRootValue T m U (q.hom.app U z) =
      finiteTateEtaleRootValue T m' U z ^ d := by
  have h := congrArg (fun t ↦ t.hom.app U z) hq
  have hn : (d • kernel.ι (m' • 𝟙 T.gmSheaf)).hom =
      d • (kernel.ι (m' • 𝟙 T.gmSheaf)).hom :=
    (sheafToPresheaf _ _).map_nsmul (f := kernel.ι (m' • 𝟙 T.gmSheaf)) (n := d)
  rw [hn, NatTrans.app_nsmul] at h
  exact congrArg (fun t ↦ Additive.toMul t.down) h

/-- A normalized ordinary Cartier Kummer family admits a simultaneous realization.

Source: blueprint latest, sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.proof.md, final paragraph; parent descent proof steps
8--11 and the existence part of step 13.
(blueprint: lem-route-cartier-kummer-realization-exists).

Proof: Choose one family of root-projection-normalized Tate comparisons, and for
each coefficient level an annihilating exponent. Postcompose the constructed
canonical
Cartier class with this comparison. Its source mate is invertible, and its
comparison equation identifies its pullback with the supplied ordinary class by
uniqueness of the ordinary supported boundary (geoCartierEtaleClass_spec). The
adjunction mate-unit identity,
checked on sheafification generators, identifies the supported quotient
normalization with constant comparison followed by the pro-etale quotient unit.
For r ≤ s construct the root projection by rootsOfUnityPowMap. Its kernel
inclusion equation says its underlying unit value is the l^(s-r) power. Thus the
coherent etale transition from finite Tate descent satisfies the pure root tensor
formula required by geoCartierCanonicalClass_modulus. Apply that theorem and
postcompose with the normalized Tate comparison. Coherence applied to the
chosen comparison family gives the transition compatible with these comparisons;
associativity of Ext gives equality of the transported classes. Compare two
arbitrary annihilating exponents with their maximum. Hence the class chosen at
each coefficient level realizes every exponent. Choice assembles these into the
required family. This argument applies also to the zero coefficient ring, empty
schemes and empty divisors: all quotient and comparison formulas remain valid.
This statement asserts existence only; uniqueness is proved in the parent. -/
theorem cartier_kummer_realization_exists
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ) :
    ∃ c : CartierKummerFamily l E, CartierKummerRealization l E κ c := by
  classical
  choose b hb using (fun n ↦ finite_tate_normalized_comparisons l E n)
  let x (n r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
      (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
      Ext ((ProEtale.lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
        (ProEtale.geoCartierConstant (finiteTateCoefficient l E n) D))
          (finiteTateProSheaf l E n T 1) 2 :=
    (ProEtale.geoCartierCanonicalClass (finiteTateCoefficient l E n)
      (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).comp
        (Ext.mk₀ (b n T hT r hA 1).hom) (add_zero 2)
  have hx (n r s : ℕ) (hrs : r ≤ s)
      (hr : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      (hs : ((l ^ (s + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
      (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
      x n s hs i hI hT = x n r hr i hI hT := by
    obtain ⟨t, ht, htb⟩ := (finite_tate_normalized_coherence l E n (b n) (hb n)).2
      T hT r s hrs hr hs 1
    have hmul : l ^ (r + 1) * l ^ (s - r) = l ^ (s + 1) := by
      rw [← pow_add]
      congr 1
      omega
    let q := T.rootsOfUnityPowMap (l ^ (s - r)) hmul
    have hd : l ^ (s + 1) / l ^ (r + 1) = l ^ (s - r) := by
      rw [← Nat.sub_add_cancel (Nat.add_le_add_right hrs 1), pow_add,
        Nat.mul_div_cancel _ (pow_pos (Fact.out : l.Prime).pos _)]
      congr 1
      omega
    have hq : q ≫ kernel.ι ((l ^ (r + 1)) • 𝟙 T.gmSheaf) =
        (l ^ (s + 1) / l ^ (r + 1)) • kernel.ι ((l ^ (s + 1)) • 𝟙 T.gmSheaf) := by
      rw [hd]
      exact Scheme.rootsOfUnityPowMap_ι (X := T) _ hmul
    have he (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
        (z : (T.rootsOfUnitySheaf (l ^ (s + 1))).obj.obj U) :
        t.hom.hom.app U (finiteEtaleTateOneGenerator _ _ T hs U a z) =
          finiteEtaleTateOneGenerator _ _ T hr U a (q.hom.app U z) := by
      apply ht U a (fun _ ↦ z) (fun _ ↦ q.hom.app U z)
      intro j
      exact root_power_value T _ _ _ q (by simpa only [hd] using hq) U z
    have hm := ProEtale.geoCartierCanonicalClass_modulus l (Fact.out : l.Prime)
      (r + 1) (s + 1) (by omega) (by omega) (by omega)
      (finiteTateCoefficient l E n) hs hr i hI
      (by simpa only [Nat.cast_pow] using hT.pow (s + 1))
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) q t hq he
    have htb' := congrArg Iso.hom htb
    dsimp only [Functor.mapIso, Iso.trans] at htb'
    dsimp only [x]
    rw [← hm, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, htb']
  let c : CartierKummerFamily l E := fun n _ _ i _ hI hT ↦ by
    unfold cartierSupported
    change Ext ((ProEtale.lowerStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
      (ProEtale.geoCartierConstant (finiteTateCoefficient l E n) _)) _ _
    exact x n (hkill n).choose (hkill n).choose_spec i hI hT
  refine ⟨c, ?_⟩
  unfold CartierKummerRealization
  intro n r hr D T i hi hI hT
  unfold cartierSupported cartierSupportedUnit
  let α := asIso (ProEtale.geoCartierSourceComparison (finiteTateCoefficient l E n) i)
  refine ⟨α, b n T hT r hr 1, hb n T hT r hr 1, ?_, ?_⟩
  · exact ProEtale.cartierSourceUnitSquare l E n i
  · have hAmax : ((l ^ (max r (hkill n).choose + 1) : ℕ) :
        finiteTateCoefficient l E n) = 0 := by
      have he : l ^ (max r (hkill n).choose + 1) =
          l ^ (r + 1) * l ^ (max r (hkill n).choose - r) := by
        rw [← pow_add]
        congr 1
        omega
      rw [he, Nat.cast_mul, hr, zero_mul]
    have hsame := (hx n (hkill n).choose (max r (hkill n).choose)
      (le_max_right _ _) (hkill n).choose_spec hAmax i hI hT).symm.trans
        (hx n r (max r (hkill n).choose) (le_max_left _ _) hr hAmax i hI hT)
    change (Ext.mk₀ α.hom).comp
      (x n (hkill n).choose (hkill n).choose_spec i hI hT) (zero_add 2) = _
    rw [hsame]
    have hxcanon : x n r hr i hI hT =
        (ProEtale.geoCartierCanonicalClass (finiteTateCoefficient l E n)
          (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hr i hI
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).comp
          (Ext.mk₀ (b n T hT r hr 1).hom) (add_zero 2) := by
      rfl
    rw [hxcanon]
    dsimp only [α]
    have hcan := ProEtale.geoCartierCanonicalClass_comparison
      (finiteTateCoefficient l E n) (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hr i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
    have hκeq := (geoCartierEtaleClass_spec (finiteTateCoefficient l E n)
      (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hr i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).2
        (κ n r hr i hI hT) (by
          unfold CartierEtaleKummerNormalization at hκ
          exact hκ n r hr i hI hT)
    have heq := hcan.trans (congrArg (fun z ↦ z.mapExactFunctor
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)) hκeq.symm)
    have heq' := congrArg (fun z ↦ z.comp
      (Ext.mk₀ (b n T hT r hr 1).hom) (add_zero 2)) heq
    simpa only [asIso_hom, Ext.comp_assoc_of_third_deg_zero] using heq'

end AlgebraicGeometry.Etale
