/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Direct image of sections supported on a closed subset

Source: Stacks Project, Properties, Tag 07ZQ, with Tag 07ZP
(blueprint: lem-trf-supported-sections-pushforward).

The supported subsheaf is the kernel of the canonical open-restriction unit.
Equality of submodule sheaves is expressed as equality of the sectionwise linear
ranges of their inclusions in the same ambient direct image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to `V`, followed by its open direct image. On an open `W` this
is restriction from `W` to `W ∩ V`.
Source: Stacks Project, Properties, Tags 07ZP and 07ZQ
(blueprint: lem-trf-supported-sections-pushforward). -/
noncomputable def supportedModuleRestriction {X : Scheme.{u}} (F : X.Modules)
    (V : X.Opens) : F ⟶ (pushforward V.ι).obj ((restrictFunctor V.ι).obj F) :=
  (restrictAdjunction V.ι).unit.app F

/-- The subsheaf of sections of `F` vanishing on the complementary open `V`.
Its kernel construction uses the actual restriction unit, with no arbitrary map.
Source: Stacks Project, Properties, Tags 07ZP and 07ZQ
(blueprint: lem-trf-supported-sections-pushforward). -/
noncomputable def supportedModuleKernel {X : Scheme.{u}} (F : X.Modules)
    (V : X.Opens) : X.Modules :=
  kernel (supportedModuleRestriction F V)

/-- The canonical inclusion of the supported subsheaf into `F`.
Source: Stacks Project, Properties, Tags 07ZP and 07ZQ
(blueprint: lem-trf-supported-sections-pushforward). -/
noncomputable def supportedModuleInclusion {X : Scheme.{u}} (F : X.Modules)
    (V : X.Opens) : supportedModuleKernel F V ⟶ F :=
  kernel.ι (supportedModuleRestriction F V)

private lemma supportedModuleInclusion_range {X : Scheme.{u}} (F : X.Modules)
    (V U : X.Opens) :
    Set.range ((supportedModuleInclusion F V).app U) =
      {s : Γ(F, U) | F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s = 0} := by
  have h := range_map_kernelι U (supportedModuleRestriction F V)
  change Set.range ((supportedModuleInclusion F V).app U) =
    {s | ((supportedModuleRestriction F V).app U) s = 0} at h
  rw [h]
  ext s
  change ((supportedModuleRestriction F V).app U) s = 0 ↔ _
  rw [supportedModuleRestriction, restrictAdjunction_unit_app_app]
  have he : V.ι ''ᵁ V.ι ⁻¹ᵁ U = U ⊓ V := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]
  have hm : F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op =
      F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op ≫
        F.presheaf.map (eqToHom he).op := by
    rw [← F.presheaf.map_comp]
    rfl
  rw [hm, ConcreteCategory.comp_apply]
  let e := F.presheaf.mapIso (eqToIso he).op
  have hinj : Function.Injective e.hom :=
    (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  exact hinj.eq_iff' e.hom.hom.map_zero

private lemma supportedModuleKernel_isQuasicoherent {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (V : X.Opens) [QuasiCompact V.ι] :
    (supportedModuleKernel F V).IsQuasicoherent := by
  have : ((pushforward V.ι).obj ((restrictFunctor V.ι).obj F)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated _ _
  exact isQuasicoherent_kernel (supportedModuleRestriction F V)

/-- Direct image commutes with the subsheaf of supported sections, as actual
submodules on every open; all three sheaves in question are quasi-coherent.
The final clause transports the supported subsheaf along any given isomorphism.
Source: Stacks Project, Properties, Tag 07ZQ, statement and proof hint, with Tag 07ZP
(blueprint: lem-trf-supported-sections-pushforward).

Proof:
1. The inclusion of `Z.compl` is quasi-compact by the affine-open criterion for
   retrocompactness. Its base change is the inclusion of `f ⁻¹ᵁ Z.compl`, so that
   open is retrocompact, by lem-weil-pbc-qcqs-morphism-permanence and
   def-weil-open-immersion.
2. Apply lem-trf-supported-sections-quasi-coherent to `F` on `X`, and to its
   direct image on `Y`. The latter is quasi-coherent by pqf-lem-pushforward-qcoh.
3. On each open `U` of `Y`, both inclusions have as image the sections of
   `F(f⁻¹U)` whose restriction to `f⁻¹(U ∩ Z.compl)` is zero. The restriction maps
   and induced scalar actions agree, so these are equal actual submodules.
4. Naturality of `β` identifies restriction of its image with its image after
   restriction. Its components are linear bijections, so vanishing is equivalent
   on both sides. This identifies the supported submodule of `H` with the direct
   image of the supported submodule of `F`, using Step 3. -/
theorem supportedSections_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (Z : TopologicalSpace.Closeds Y)
    (hZ : ∀ U : Y.affineOpens, IsCompact ((U : Y.Opens) ⊓ Z.compl : Set Y))
    (F : X.Modules) [F.IsQuasicoherent] :
    (∀ W : X.affineOpens,
      IsCompact ((W : X.Opens) ⊓ (f ⁻¹ᵁ Z.compl) : Set X)) ∧
    (supportedModuleKernel F (f ⁻¹ᵁ Z.compl)).IsQuasicoherent ∧
    ((pushforward f).obj F).IsQuasicoherent ∧
    (supportedModuleKernel ((pushforward f).obj F) Z.compl).IsQuasicoherent ∧
    (∀ U : Y.Opens,
      LinearMap.range
          ((((pushforward f).map (supportedModuleInclusion F (f ⁻¹ᵁ Z.compl))).val.app
            (op U)).hom) =
        LinearMap.range
          (((supportedModuleInclusion ((pushforward f).obj F) Z.compl).val.app (op U)).hom)) ∧
    (∀ (H : Y.Modules) (β : H ≅ (pushforward f).obj F) (U : Y.Opens),
      LinearMap.range
          ((((supportedModuleInclusion H Z.compl) ≫ β.hom).val.app (op U)).hom) =
        LinearMap.range
          ((((pushforward f).map (supportedModuleInclusion F (f ⁻¹ᵁ Z.compl))).val.app
            (op U)).hom)) := by
  have hqc : QuasiCompact (Scheme.Opens.ι (X := Y) Z.compl) := by
    apply quasiCompact_iff_forall_isAffineOpen.mpr
    intro U hU
    apply (Scheme.Opens.ι (X := Y) Z.compl).isOpenEmbedding.isEmbedding.isCompact_iff.mpr
    simpa only [← Scheme.Hom.coe_image, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, TopologicalSpace.Opens.coe_inf, Set.inf_eq_inter,
      inf_comm] using hZ ⟨U, hU⟩
  have hqcX : QuasiCompact (f ⁻¹ᵁ Z.compl).ι :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (isPullback_morphismRestrict f Z.compl) hqc
  have hretro (W : X.affineOpens) :
      IsCompact ((W : X.Opens) ⊓ (f ⁻¹ᵁ Z.compl) : Set X) := by
    have h := ((f ⁻¹ᵁ Z.compl).ι.isCompact_preimage W.2.isCompact).image
      (f ⁻¹ᵁ Z.compl).ι.continuous
    simpa only [← Scheme.Hom.coe_image, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, TopologicalSpace.Opens.coe_inf, Set.inf_eq_inter, inf_comm] using h
  have hF : ((pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f F
  have hrange (U : Y.Opens) :
      LinearMap.range
          ((((pushforward f).map (supportedModuleInclusion F (f ⁻¹ᵁ Z.compl))).val.app
            (op U)).hom) =
        LinearMap.range
          (((supportedModuleInclusion ((pushforward f).obj F) Z.compl).val.app (op U)).hom) := by
    apply SetLike.coe_injective
    change Set.range ((supportedModuleInclusion F (f ⁻¹ᵁ Z.compl)).app (f ⁻¹ᵁ U)) =
      Set.range ((supportedModuleInclusion ((pushforward f).obj F) Z.compl).app U)
    rw [supportedModuleInclusion_range, supportedModuleInclusion_range]
    simp only [pushforward_obj_presheaf_map, Scheme.Hom.preimage_inf]
    rfl
  refine ⟨hretro, supportedModuleKernel_isQuasicoherent F _, hF,
    supportedModuleKernel_isQuasicoherent _ _, hrange, ?_⟩
  intro H β U
  rw [hrange U]
  apply SetLike.coe_injective
  change Set.range (((supportedModuleInclusion H Z.compl) ≫ β.hom).app U) =
    Set.range ((supportedModuleInclusion ((pushforward f).obj F) Z.compl).app U)
  rw [Hom.comp_app]
  change Set.range (β.hom.app U ∘ (supportedModuleInclusion H Z.compl).app U) = _
  rw [Set.range_comp, supportedModuleInclusion_range, supportedModuleInclusion_range]
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hn := congr($(β.hom.mapPresheaf.naturality
      (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op) t)
    change H.presheaf.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op t = 0 at ht
    change ((pushforward f).obj F).presheaf.map _ (β.hom.app U t) = 0
    calc
      _ = β.hom.app (U ⊓ Z.compl)
          (H.presheaf.map (homOfLE inf_le_left).op t) := hn.symm
      _ = 0 := by rw [ht]; exact map_zero _
  · intro hs
    change ((pushforward f).obj F).presheaf.map
      (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op s = 0 at hs
    refine ⟨β.inv.app U s, ?_, ?_⟩
    · have hn := congr($(β.inv.mapPresheaf.naturality
        (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op) s)
      calc
        _ = β.inv.app (U ⊓ Z.compl)
            (((pushforward f).obj F).presheaf.map (homOfLE inf_le_left).op s) := hn.symm
        _ = 0 := by rw [hs]; exact map_zero _
    · have h := congrArg
        (fun k : (pushforward f).obj F ⟶ (pushforward f).obj F ↦ k.app U s) β.inv_hom_id
      exact h

end AlgebraicGeometry.Scheme.Modules
