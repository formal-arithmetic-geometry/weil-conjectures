/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.SectionsAnnihilatedByIdeal
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Descent of the generic maximal-ideal-annihilated part

Source: Stacks Project, Tag 01YE, first two paragraphs of the proof.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The part of a coherent module annihilated by the defining ideal descends to the
integral closed subscheme, and its inclusion has an invertible generic stalk.

Source: Stacks Project, Tag 01YE, first two paragraphs of the proof. -/
theorem coherent_generic_point_closed_descent {X Z : Scheme.{w}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ x : (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint Z))).obj F,
        a • x = 0) :
    ∃ (G : Z.Modules), RingedSpace.IsCoherent Z.toRingedSpace G ∧
      ∃ (β : (pushforward i).obj G ⟶ F), Mono β ∧
        IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint Z))).map β)  := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have hunit := isCoherent_unit_of_finite_to_locallyNoetherian (𝟙 X)
  have : i.ker.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := i.ker.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward i.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)) :=
      ((closedImmersion_pushforward_annihilated i.ker.subschemeι).1
        (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)).1
    exact isQuasicoherent_kernel i.ker.toPushforwardSubscheme
  have hJ := (isCoherent_kernel_cokernel_biprod_and_submodule X).2
    (SheafOfModules.unit X.ringCatSheaf) i.ker.toModules i.ker.toModulesι
    hunit inferInstance inferInstance
  have : i.ker.toModules.IsFiniteType := hJ.1.1
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq
  obtain ⟨F', ι, hι, hq', hrange, _, hstalk⟩ := sections_annihilated_by_ideal X i.ker F
  have : Mono ι := hι
  have : F'.IsQuasicoherent := hq'
  have hF' := (isCoherent_kernel_cokernel_biprod_and_submodule X).2 F F' ι hF hι hq'
  have hkill' (V : X.Opens) (a : Γ(X, V)) (ha : a ∈ i.ker.idealOfOpens V)
      (s : Γ(F', V)) : a • s = 0 := by
    have : Mono ι.val := inferInstanceAs (Mono ((SheafOfModules.forget _).map ι))
    apply PresheafOfModules.injective_of_mono ι.val (op V)
    change (ι.app V) (a • s) = (ι.app V) 0
    rw [Hom.app_smul, map_zero]
    have hv := (hrange V (ι.app V s)).mp ⟨s, rfl⟩ V le_rfl a ha
    simpa using hv
  obtain ⟨hGp, hη, hGt⟩ :=
    (closedImmersion_pushforward_annihilated i).2 F' hkill'
  let G := (tensorPullback i).obj F'
  have hG : RingedSpace.IsCoherent Z.toRingedSpace G :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType Z G).mpr ⟨hGp, hGt hF'.1.1⟩
  let η := (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app F'
  have : IsIso η := hη
  let β := inv η ≫ ι
  have hst : Function.Bijective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map ι) := by
    refine ⟨(hstalk _).2.1, ?_⟩
    intro s
    apply ((hstalk _).2.2 s).mpr
    intro U hx a ha
    apply hkill (X.presheaf.germ U _ hx a) ?_ s
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hz : (i.app U).hom a = 0 := by
      have hz := (Scheme.IdealSheafData.mem_idealOfOpens_iff i.ker).mp ha
      rw [← i.toImage_imageι, Scheme.Hom.comp_app]
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hz, map_zero]
    have hgerm : (i.stalkMap (genericPoint Z)).hom (X.presheaf.germ U _ hx a) = 0 := by
      rw [Scheme.Hom.germ_stalkMap_apply, hz, map_zero]
    have hu := hunit.map (i.stalkMap (genericPoint Z)).hom
    rw [hgerm] at hu
    exact not_isUnit_zero hu
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map ι) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hst
  refine ⟨G, hG, β, inferInstance, ?_⟩
  dsimp only [β]
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
