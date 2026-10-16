/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # The normalized quotient comparison for an ideal-power closed immersion

Source: Stacks Project, Lemma 087T and equation 0880.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem power_iso {X : Scheme.{v}} (J : X.IdealSheafData) (n : ℕ) :
    ∃ e : (Scheme.idealSheafPower J.toModulesι n).1 ≅ (J ^ n).toModules,
      e.hom ≫ (J ^ n).toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
  have : Mono (Scheme.idealSheafPower J.toModulesι n).2 := by
    induction n using Nat.twoStepInduction with
    | zero => dsimp [Scheme.idealSheafPower]; infer_instance
    | one => dsimp [Scheme.idealSheafPower]; infer_instance
    | more n _ ih =>
      change Mono (Scheme.idealModuleProductι J.toModulesι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).1 ≫
          (Scheme.idealSheafPower J.toModulesι (n + 1)).2)
      have := ih
      have : Mono (Scheme.idealModuleProductι J.toModulesι
          (Scheme.idealSheafPower J.toModulesι (n + 1)).1) := by
        dsimp [Scheme.idealModuleProductι]
        infer_instance
      infer_instance
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hr (U : X.affineOpens) :
      Set.range ((Scheme.idealSheafPower J.toModulesι n).2.app U.1) =
        Set.range ((J ^ n).toModulesι.app U.1) := by
    rw [(J ^ n).range_toModulesι_app]
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    cases n with
    | zero => simp [Scheme.idealSheafPower]
    | succ n =>
      exact (((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J
        (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 (n + 1)
          (Nat.zero_lt_succ n))
  let K := J ^ n
  let P := (Scheme.idealSheafPower J.toModulesι n).1
  let i := (Scheme.idealSheafPower J.toModulesι n).2
  have hz : i ≫ K.toPushforwardSubscheme = 0 := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    change (i ≫ K.toPushforwardSubscheme).app W s = 0
    let N : X.Modules :=
      (SheafOfModules.pushforward K.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit K.subscheme.ringCatSheaf)
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
      (fun t : {U : X.affineOpens // U.1 ≤ W} ↦ t.1.1) W
      (fun t ↦ homOfLE t.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
    · intro t
      rw [← Scheme.Modules.Hom.app_presheaf_map, map_zero]
      let z := P.presheaf.map (homOfLE t.2).op s
      obtain ⟨b, hb⟩ := (hr t.1).subset ⟨z, rfl⟩
      change K.subschemeι.app t.1.1 (i.app t.1.1 z) = 0
      rw [← hb]
      exact (K.range_toModulesι_app_eq t.1.1).subset ⟨b, rfl⟩
  let f : P ⟶ K.toModules := kernel.lift K.toPushforwardSubscheme i hz
  have hf : f ≫ K.toModulesι = i := kernel.lift_ι _ _ hz
  have : Mono f := mono_of_mono_fac hf
  have hB : TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : X.affineOpens ↦ U.1)) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  have : IsIso f := Scheme.Modules.isIso_of_bijective_app_of_basis hB f (by
    intro U
    constructor
    · have : Mono ((SheafOfModules.evaluation X.ringCatSheaf (.op U.1)).map f) :=
        inferInstance
      exact (ModuleCat.mono_iff_injective _).mp this
    · intro b
      obtain ⟨a, ha⟩ := (hr U).symm.subset ⟨b, rfl⟩
      refine ⟨a, K.injective_toModulesι_app U.1 ?_⟩
      exact (congrArg (fun g ↦ g.app U.1 a) hf).trans ha)
  exact ⟨asIso f, hf⟩

set_option backward.isDefEq.respectTransparency false in
/-- The quotient by an ideal power is the pushforward of restriction, with its
projection identified with the unit of the supplied adjunction.
Source: Stacks Project, Lemma 087T (lemma-i-star-equivalence), equation 0880.
(blueprint: lem-weil-pbc-closed-immersion-power-quotient).

Proof: On each affine open, the image of the recursively defined ideal-sheaf power
has range J(U)^n, by induction using the affine tensor multiplication calculation.
Thus its product with F has the same image subobject as multiplication by (J^n).
The equality is checked on affine opens and glued by sheaf separatedness. Replace
J^n by the kernel of j. The closed-immersion unit quotient theorem identifies the
cokernel of this image inclusion with j_*j^*F, taking the projection to the canonical
adjunction unit. Equal image subobjects induce the unique quotient isomorphism
preserving projections. Finally compose with the pushforward of leftAdjointUniq
from the canonical adjunction to a; its unit equation gives the claimed equality.
The zero power is the unit ideal, so the closed subscheme and both quotient objects
are zero; zero ideals and zero modules give the same calculation. -/
theorem closedImmersion_power_quotient {X Z : Scheme.{v}} (J : X.IdealSheafData)
    (n : ℕ) (j : Z ⟶ X) [IsClosedImmersion j] (hj : j.ker = J ^ n)
    (a : Scheme.Modules.tensorPullback j ⊣ Scheme.Modules.pushforward j)
    (F : X.Modules) :
    ∃ e : formalModuleQuotient J n F ≅
        (Scheme.Modules.pushforward j).obj ((Scheme.Modules.tensorPullback j).obj F),
      formalModuleQuotientπ J n F ≫ e.hom = a.unit.app F := by
  classical
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨d, hd⟩ :
      ∃ d : (Scheme.idealSheafPower J.toModulesι n).1 ≅ j.ker.toModules,
        d.hom ≫ j.ker.toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
    rw [hj]
    exact power_iso J n
  let μ : MonoidalCategory.tensorObj (Scheme.idealSheafPower J.toModulesι n).1 F ⟶ F :=
    MonoidalCategory.whiskerRight (Scheme.idealSheafPower J.toModulesι n).2 F ≫
      (MonoidalCategory.leftUnitor F).hom
  let ν : MonoidalCategory.tensorObj j.ker.toModules F ⟶ F :=
    MonoidalCategory.whiskerRight j.ker.toModulesι F ≫ (MonoidalCategory.leftUnitor F).hom
  have hμ : μ ≫ (Iso.refl F).hom = (MonoidalCategory.whiskerRightIso d F).hom ≫ ν := by
    simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerRightIso_hom, ν, μ]
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hd]
  let q := cokernelImageι μ ≪≫
    cokernel.mapIso μ ν (MonoidalCategory.whiskerRightIso d F) (Iso.refl F) hμ ≪≫
    (cokernelImageι ν).symm
  have hq : formalModuleQuotientπ J n F ≫ q.hom = cokernel.π (image.ι ν) := by
    change cokernel.π (image.ι μ) ≫ q.hom = _
    simp [q]
  let adj : Scheme.Modules.tensorPullback j ⊣ Scheme.Modules.pushforward j :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction j)
  obtain ⟨η, hη, _⟩ := Scheme.Modules.closedImmersion_unit_quotient j
  have hηF := hη F
  have : IsIso (η F) := hηF.2.2.2
  let t := (Scheme.Modules.pushforward j).mapIso ((adj.leftAdjointUniq a).app F)
  refine ⟨q ≪≫ asIso (η F) ≪≫ t, ?_⟩
  change formalModuleQuotientπ J n F ≫ q.hom ≫ η F ≫ t.hom = _
  rw [← Category.assoc, hq, ← Category.assoc, hηF.2.2.1]
  exact adj.unit_leftAdjointUniq_hom_app a F

end AlgebraicGeometry
