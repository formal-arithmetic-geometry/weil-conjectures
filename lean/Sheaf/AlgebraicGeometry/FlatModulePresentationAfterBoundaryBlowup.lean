/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Topology.Constructible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier
import Sheaf.TraceFormula.FlatFiniteTypeDensePresentation
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-!
# Finite presentation after blowing up the boundary

Source: Stacks Project, flat.tex, Tags 0815 (final proof paragraph), 080Y (third
paragraph), and 081N (blueprint: lem-trf-flat-module-presentation-after-boundary-blowup).

The assertion applies to every finite-type centre cutting out the boundary. The
canonical quotient defining the strict transform is an isomorphism. Finite
presentation is asserted on the entire fibre product, without a compactness
assumption on the original source scheme.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem schematicallyDenseOpen_of_dominant {Y : Scheme.{u}} (V : Y.Opens)
    [IsSchemeTheoreticallyDominant V.ι] [QuasiCompact V.ι] : SchematicallyDenseOpen V := by
  intro W a b hab
  have heW : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  apply V.ι.app_injective W
  rw [Scheme.Opens.ι_app]
  change (Y.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op) a =
    (Y.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op) b
  have hh := congrArg (Y.presheaf.map (homOfLE heW.le).op) hab
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using hh

private theorem finitePresentation_restrict_tensorPullback {Y X : Scheme.{u}}
    (p : Y ⟶ X) (F : X.Modules) (W : X.Opens)
    [((restrictFunctor W.ι).obj F).IsFinitePresentation] :
    ((restrictFunctor (p ⁻¹ᵁ W).ι).obj ((tensorPullback p).obj F)).IsFinitePresentation := by
  let e := (tensorPullbackSectionAdjunction p).leftAdjointUniq
    (pullbackPushforwardAdjunction p)
  let i := (p ⁻¹ᵁ W).ι
  let a := p ∣_ W
  let c := (restrictFunctor i).mapIso (e.app F) ≪≫
    (restrictFunctorIsoPullback i).app ((Modules.pullback p).obj F) ≪≫
    (Modules.pullbackComp i p).app F ≪≫
    (Modules.pullbackCongr (morphismRestrict_ι p W).symm).app F ≪≫
    ((Modules.pullbackComp a W.ι).symm).app F ≪≫
    (Modules.pullback a).mapIso ((restrictFunctorIsoPullback W.ι).app F).symm
  exact isFinitePresentation_of_iso c.symm

/-- Boundary blowups make a relatively flat finite-type module finitely presented.
Source: Stacks Project, flat.tex, Tags 0815, 080Y, and 081N
(blueprint: lem-trf-flat-module-presentation-after-boundary-blowup).

Proof:
1. On the qcqs base, lemma-nagata-qc-open-complement-ideal-exists supplies a
   finite-type ideal with support the complement of U. For any such ideal,
   det-nagata-boundary-divisor-cartier makes its blowup U-admissible and the
   inverse image of U scheme-theoretically dense.
2. Clause (2) of lem-trf-module-admissible-blowup-calculus identifies the module
   strict transform with the ordinary pullback via the canonical quotient. It
   preserves relative flatness and finite type and gives a qcqs new base.
3. By lemma-nagata-admissible-blowup-over-open the inverse image of U is
   isomorphic to U, hence quasi-compact. Quasi-separatedness of the new base,
   using clause (1) of lem-weil-pbc-qcqs-morphism-permanence, makes its open
   inclusion quasi-compact. Intersecting with a finite affine cover of any
   quasi-compact open proves retrocompactness.
4. The new projection is locally of finite presentation by base change
   (lem-weil-pbc-qcqs-morphism-permanence, clause (3)). Over the inverse image
   of U its strict transform agrees with the given finitely presented
   restriction. Apply lem-trf-flat-finite-type-dense-presentation to obtain
   finite presentation everywhere on the fibre product. This criterion is
   local and requires no quasi-compactness of X.
-/
theorem flatModulePresentationAfterBoundaryBlowup
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [hF : F.IsQuasicoherent] [F.IsFiniteType]
    (hflat : F.IsFlatOver f) (U : S.Opens) (hU : IsCompact (U : Set S))
    (hUfp : ((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation) :
    (∃ I : S.IdealSheafData,
      I.toModules.IsFiniteType ∧ (I.support : Set S) = (U : Set S)ᶜ) ∧
    ∀ (I : S.IdealSheafData) (hI : I.toModules.IsFiniteType),
      (I.support : Set S) = (U : Set S)ᶜ →
      (∃ B : IsAdmissible S U, B.I = I) ∧
      CompactSpace I.blowup ∧ QuasiSeparatedSpace I.blowup ∧
      IsCompact ((I.blowupMap ⁻¹ᵁ U : I.blowup.Opens) : Set I.blowup) ∧
      IsRetrocompact ((I.blowupMap ⁻¹ᵁ U : I.blowup.Opens) : Set I.blowup) ∧
      IsSchemeTheoreticallyDominant (I.blowupMap ⁻¹ᵁ U).ι ∧
      IsIso (cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F))) ∧
      (@moduleStrictTransform _ _ f I hI F hF).IsFlatOver (pullback.snd f I.blowupMap) ∧
      (@moduleStrictTransform _ _ f I hI F hF).IsFinitePresentation := by
  obtain ⟨J, hJ, hJsupport⟩ := S.exists_finiteType_ideal_coe_support_eq_compl U hU
  refine ⟨⟨J, J.isFiniteType_toModules_sheaf hJ, hJsupport⟩, ?_⟩
  intro I hI hsupport
  let := hI
  let := hUfp
  have hIfinite : I.ofFiniteType := by
    have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent.{u, u, u}
        ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit I.subscheme.ringCatSheaf)) :=
      isQuasicoherent_pushforward_of_isClosedImmersion I.subschemeι
        (SheafOfModules.unit I.subscheme.ringCatSheaf)
    have : I.toModules.IsQuasicoherent := isQuasicoherent_kernel I.toPushforwardSubscheme
    intro V _
    have := finite_sections_of_finiteType I.toModules V.2
    have hr := Submodule.fg_range (I.toModulesι.appₗ V.1)
    have he : LinearMap.range (I.toModulesι.appₗ V.1) = I.ideal V := by
      ext x
      exact Set.ext_iff.mp (I.range_toModulesι_app V) x
    rwa [he] at hr
  obtain ⟨⟨I', hI', hdisj⟩, hBI, hdense, -⟩ :=
    exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl_with_density
      U hU I hIfinite hsupport
  change I' = I at hBI
  subst I'
  let B : IsAdmissible S U := ⟨I, hI', hdisj⟩
  have hB : ∃ B : IsAdmissible S U, B.I = I := ⟨B, rfl⟩
  obtain ⟨hIB, hqc, _, _, hft, hflatB, hcompact, hqs⟩ :=
    moduleAdmissibleBlowupPermanence U hU f F B
  have hiso : IsIso (I.blowupMap ∣_ U) := B.isIso_blowupMap_restrict
  have hqc' : (moduleStrictTransform f I F).IsQuasicoherent := hqc
  have hft' : (moduleStrictTransform f I F).IsFiniteType := hft inferInstance
  have hflat' := hflatB hflat
  have hquot : IsIso (moduleStrictTransformQuotient f I F) := hflat'.1
  have hflatI : (moduleStrictTransform f I F).IsFlatOver
      (pullback.snd f I.blowupMap) := hflat'.2
  have : CompactSpace I.blowup := hcompact
  have : QuasiSeparatedSpace I.blowup := hqs
  let V := I.blowupMap ⁻¹ᵁ U
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have hVcpt : CompactSpace V.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (I.blowupMap ∣_ U)
  have hV : IsCompact (V : Set I.blowup) := isCompact_iff_compactSpace.mpr hVcpt
  have hretro : IsRetrocompact (V : Set I.blowup) := hV.isRetrocompact V.isOpen
  have hdenseI : IsSchemeTheoreticallyDominant V.ι := hdense
  have : QuasiCompact V.ι := V.quasiCompact_ι hV
  have hdenseV : SchematicallyDenseOpen V := schematicallyDenseOpen_of_dominant V
  have he : (pullback.snd f I.blowupMap) ⁻¹ᵁ V =
      (pullback.fst f I.blowupMap) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change (pullback.snd f I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ U =
      (pullback.fst f I.blowupMap ≫ f) ⁻¹ᵁ U
    rw [pullback.condition]
  have hpullfp : ((restrictFunctor ((pullback.snd f I.blowupMap) ⁻¹ᵁ V).ι).obj
      ((tensorPullback (pullback.fst f I.blowupMap)).obj F)).IsFinitePresentation := by
    rw [he]
    exact finitePresentation_restrict_tensorPullback (pullback.fst f I.blowupMap) F
      (f ⁻¹ᵁ U)
  have hrestrictfp : ((restrictFunctor ((pullback.snd f I.blowupMap) ⁻¹ᵁ V).ι).obj
      (moduleStrictTransform f I F)).IsFinitePresentation :=
    isFinitePresentation_of_iso
      ((restrictFunctor ((pullback.snd f I.blowupMap) ⁻¹ᵁ V).ι).mapIso
        (asIso (moduleStrictTransformQuotient f I F)))
  have hfp : (moduleStrictTransform f I F).IsFinitePresentation :=
    flat_finite_type_dense_presentation (pullback.snd f I.blowupMap)
      (moduleStrictTransform f I F) ⟨hqc', hft'⟩ hflatI V hretro hdenseV hrestrictfp
  exact ⟨hB, inferInstance, inferInstance, hV, hretro, hdenseI, hquot, hflatI, hfp⟩

end AlgebraicGeometry.Scheme.Modules
