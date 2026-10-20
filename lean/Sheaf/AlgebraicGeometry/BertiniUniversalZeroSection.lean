/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
import Sheaf.AlgebraicGeometry.BertiniUniversalBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# The zero-parameter section of universal incidence

Source: Stacks Project, Varieties, situation-family-divisors; More on Morphisms, Tag 0G4F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme.Modules

/-- The universal incidence scheme contains a section over its base obtained by setting
all coefficient parameters equal to zero.

Source: Stacks Project, Varieties, situation-family-divisors, the universal linear equation;
More on Morphisms, Tag 0G4F, gluing the irreducible incidence charts.
(blueprint: lem-zl-bertini-universal-zero-section).

Proof: The coefficient evaluation at zero and the identity of Y define a map from Y to
the ambient product. The universal zero-ideal pullback formula makes its pulled-back ideal
zero, since each coefficient is zero. Thus it factors through the closed incidence scheme.
The second projection of the factorization is the identity by the pullback equations. -/
theorem exists_bertiniUniversalZeroSection
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    ∃ z : Y ⟶ (bertiniUniversalIdeal f L s).subscheme,
      z ≫ (bertiniUniversalIdeal f L s).subschemeι ≫
        pullback.snd (Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial I k))) f = 𝟙 Y := by
  classical
  let a := Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := k) (fun _ : I ↦ (0 : k))).toRingHom)
  have ha : a ≫ Spec.map
      (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact MvPolynomial.aeval_C _ c
  let g := pullback.lift (f ≫ a) (𝟙 Y)
    (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])
  have hg : (bertiniUniversalIdeal f L s).comap g = ⊥ := by
    rw [bertiniUniversalIdeal_comap, pullback.lift_fst]
    have hcoord (i : I) : (f ≫ a).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv (MvPolynomial.X i)) = 0 := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [Scheme.specMap_appTop_ΓSpecIso_inv]
      simp only [CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_X, map_zero]
    simp only [hcoord, zero_smul, Finset.sum_const_zero]
    let t := g ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f
    let E := ((Classical.choose (exists_tensorPullbackAdjunction t)).leftAdjointUniq
      (pullbackPushforwardAdjunction t)).app L
    have : ((tensorPullback t).obj L).IsInvertible := IsInvertible.of_iso E.symm
    have := IsInvertible.sheafOfModules_isInvertible ((tensorPullback t).obj L)
    have : SheafOfModules.IsInvertible.{u, u, u} (unit Y) :=
      IsInvertible.sheafOfModules_isInvertible (MonoidalCategory.tensorUnit Y.Modules)
    apply (Hom.zeroLocus_eq_bot_iff _).mpr
    apply unit_hom_ext
    simp only [Hom.zero_app, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
  let z := IsClosedImmersion.lift (bertiniUniversalIdeal f L s).subschemeι g
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact Scheme.IdealSheafData.le_ker_of_comap_eq_bot g hg)
  refine ⟨z, ?_⟩
  rw [← Category.assoc, IsClosedImmersion.lift_fac]
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry
