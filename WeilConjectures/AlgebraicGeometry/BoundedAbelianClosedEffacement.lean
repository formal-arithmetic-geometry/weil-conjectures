/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.ConstructibleRestrictionClass
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleClosedEffacement
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Effacement preserving a fixed coefficient exponent

Source: Stacks Project, Tag 09ZE, proof with coefficients in Z/n.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- A positive-degree class on a closed subscheme of an affine scheme can be effaced
without changing the integer annihilating its coefficients (Stacks, Tag 09ZE). -/
theorem exists_bounded_mono_closed_cohomology_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (hn : 0 < n)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : n • 𝟙 G = 0)
    (q : ℕ) (hq : 0 < q)
    (x : Sheaf.H (((i)^*[AddCommGrpCat.{u + 1}]).obj G) q) :
    ∃ (G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ G'),
      Mono a ∧ n • 𝟙 G' = 0 ∧
        Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map a) q x = 0 := by
  classical
  let Λ := ULift.{u + 1} (ZMod n)
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let V := (i)^*[AddCommGrpCat.{u + 1}]
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves U (sheafToPresheaf _ _)
  obtain ⟨M, ⟨eM⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X n G hG
  obtain ⟨e⟩ := exists_upperStar_forget₂_natIso Λ i
  let eH := Functor.isoWhiskerRight e (Sheaf.functorH _ q)
  have : IsAffine Z := isAffine_of_isAffineHom i
  let xM := Sheaf.H.map (V.map eM.inv) q x
  obtain ⟨C, hC, a, z, hz⟩ := exists_constructible_restriction_class i Λ M q
    ((eH.inv.app M) xM)
  let zC := (eH.hom.app C) z
  have hzC : Sheaf.H.map (V.map (U.map a)) q zC = xM := by
    have h := ConcreteCategory.congr_hom (eH.hom.naturality a) z
    change (eH.hom.app M)
      (Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map a)) q z) =
      Sheaf.H.map (V.map (U.map a)) q zC at h
    rw [← h, hz]
    rw [← ConcreteCategory.comp_apply, eH.inv_hom_id_app, ConcreteCategory.id_apply]
  obtain ⟨D, b, hb, hkill⟩ := exists_constructible_module_mono_closed_cohomology_eq_zero
    i Λ C hC q hq zC
  let P := pushout b a
  let m : M ⟶ P := pushout.inr b a
  have : Mono m := inferInstance
  let f : G ⟶ U.obj P := eM.inv ≫ U.map m
  refine ⟨U.obj P, f, inferInstance, ?_, ?_⟩
  · have hnΛ : (n : Λ) = 0 := by
      apply ULift.ext
      exact ZMod.natCast_self n
    have bounded (N : ModuleCat.{u + 1} Λ) (y : N) : n • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul Λ, hnΛ, zero_smul]
    ext T y
    exact bounded (P.obj.obj T) y
  · change Sheaf.H.map (V.map f) q x = 0
    rw [Functor.map_comp, Sheaf.H.map_comp_apply]
    change Sheaf.H.map (V.map (U.map m)) q xM = 0
    rw [← hzC, ← Sheaf.H.map_comp_apply, ← V.map_comp, ← U.map_comp]
    change Sheaf.H.map (V.map (U.map (a ≫ pushout.inr b a))) q zC = 0
    rw [← pushout.condition, U.map_comp, V.map_comp, Sheaf.H.map_comp_apply,
      hkill, map_zero]


end AlgebraicGeometry.Etale
