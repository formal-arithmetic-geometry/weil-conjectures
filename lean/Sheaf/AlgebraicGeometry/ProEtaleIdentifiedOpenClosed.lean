/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage

/-!
# Open and closed extensions with identified inverse-image coefficient rings

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; Pro-etale Cohomology,
Tags 09BN and 09AH
(blueprint: lem-sfb-proetale-identified-open-closed).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact open extension for the actual tensor pullback with identified coefficients.
The extension is constructed by scalar transport to the inverse-image ring, the open
slice equivalence, and the sheafified extension presheaf. Its adjunction unit is invertible.

Source: Stacks Project, Tags 03DI, 03DJ, 09BN and 09AH
(blueprint: lem-sfb-proetale-identified-open-closed).

Proof: obtain the exact slice extension and its invertible unit from ringed open/closed
localization. Restriction of scalars along the coefficient isomorphism is an equivalence;
its inverse is the actual sheafified tensor extension, by uniqueness of left adjoints.
Compose this scalar equivalence, the slice equivalence and extension by zero. Transport
the composite right adjoint using the published inverse-image/slice comparison. This is
an adjunction to the specified actual tensor pullback. Equivalences preserve finite limits
and colimits, so the composite extension is exact and additive. The slice extension has
invertible unit and hence is fully faithful. Its composite with the two equivalences is
fully faithful, so the unit of the transported adjunction is invertible as well.
Closed restriction of its image vanishes by ringed cross-vanishing and scalar transport.
For a sheaf with zero closed restriction, the localization sequence makes the ringed
open counit both monic and epic. The scalar and slice equivalences identify its source
with a value of the transported extension; essential-image membership makes the counit
of the transported adjunction invertible too. -/
private theorem identifiedOpenExtension
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj R ≅ S)
    (Si : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Si) :
    ∃ F : proEtaleRingModules U.left S ⥤ proEtaleRingModules X R,
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
        ∃ adj : F ⊣ proEtaleRingModulePullback U.hom R S c, IsIso adj.unit ∧
          (∀ N, IsZero ((proEtaleRingModulePullback i R Si ci).obj (F.obj N))) ∧
          ∀ M, IsZero ((proEtaleRingModulePullback i R Si ci).obj M) →
            IsIso (adj.counit.app M) := by
  obtain ⟨q, ⟨hq⟩, ai, aj, _, hu, _, hz, hlim, hcol, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let e := proEtaleScalarEquivalence U.left ((sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  let t := (proEtaleRingExtensionAdjunction U.hom R S c).leftAdjointUniq
    e.symm.toAdjunction
  let p : proEtaleRingModulePullback U.hom R S c ≅
      proEtaleModuleInverseImage U.hom R ⋙ e.inverse :=
    Functor.isoWhiskerLeft (proEtaleModuleInverseImage U.hom R) t
  let rq : SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U ⋙ q.inverse ≅
      proEtaleModuleInverseImage U.hom R :=
    Functor.isoWhiskerRight hq.symm q.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ q.unitIso.symm ≪≫ Functor.rightUnitor _
  let F := e.functor ⋙ q.functor ⋙ proEtaleRingedExtensionByZero U R
  let adj : F ⊣ proEtaleRingModulePullback U.hom R S c :=
    (e.toAdjunction.comp (q.toAdjunction.comp aj)).ofNatIsoRight
      (Functor.isoWhiskerRight rq e.inverse ≪≫ p.symm)
  have : PreservesFiniteLimits (proEtaleRingedExtensionByZero U R) := hlim
  have : PreservesFiniteColimits (proEtaleRingedExtensionByZero U R) := hcol
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  have : F.Additive := F.additive_of_preservesBinaryBiproducts
  have := hu
  have : IsIso aj.unit := NatIso.isIso_of_isIso_app _
  have : (proEtaleRingedExtensionByZero U R).Full := aj.fullyFaithfulLOfIsIsoUnit.full
  have : (proEtaleRingedExtensionByZero U R).Faithful := aj.fullyFaithfulLOfIsIsoUnit.faithful
  refine ⟨F, inferInstance, inferInstance, inferInstance, adj,
    adj.unit_isIso_of_L_fully_faithful, ?_, ?_⟩
  · intro N
    exact (pullback_isZero_iff_inverseImage i R Si ci (F.obj N)).2 (hz _)
  intro M hm
  have hz := (pullback_isZero_iff_inverseImage i R Si ci M).1 hm
  have : (proEtaleRingedDirectImage i R).IsRightAdjoint := ai.isRightAdjoint
  have hr := (proEtaleRingedDirectImage i R).map_isZero hz
  let T := ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)
  have hT : T.Exact := (hs M).2.2
  have he := (T.exact₂_iff hT.toIsComplex).1 hT
  have : Epi (aj.counit.app M) := he.epi_f (hr.eq_of_tgt _ _)
  have : Mono (aj.counit.app M) := (hs M).1
  have : IsIso (aj.counit.app M) := isIso_of_mono_of_epi _
  apply adj.isIso_counit_app_iff_mem_essImage.2
  refine ⟨e.inverse.obj (q.inverse.obj
    ((SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U).obj M)), ⟨?_⟩⟩
  exact (proEtaleRingedExtensionByZero U R).mapIso
    (q.functor.mapIso (e.counitIso.app _) ≪≫ q.counitIso.app _) ≪≫
      asIso (aj.counit.app M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem identifiedClosedImage
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ S) :
    PreservesFiniteLimits (proEtaleRingModuleDirectImage i R S c) ∧
      PreservesFiniteColimits (proEtaleRingModuleDirectImage i R S c) ∧
        IsIso (proEtaleRingModuleAdjunction i R S c).counit := by
  obtain ⟨_, _, ai, _, hc, _, _, _, _, _, hlim, hcol, _, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let d := coefficientDirectImageIso i R S c
  have : PreservesFiniteLimits (proEtaleRingedDirectImage i R) := hlim
  have : PreservesFiniteColimits (proEtaleRingedDirectImage i R) := hcol
  have := hc
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have : (proEtaleRingedDirectImage i R).Full := ai.fullyFaithfulROfIsIsoCounit.full
  have : (proEtaleRingedDirectImage i R).Faithful := ai.fullyFaithfulROfIsIsoCounit.faithful
  have : (proEtaleRingModuleDirectImage i R S c).Full := Functor.Full.of_iso d
  have : (proEtaleRingModuleDirectImage i R S c).Faithful := Functor.Faithful.of_iso d
  exact ⟨preservesFiniteLimits_of_natIso d, preservesFiniteColimits_of_natIso d,
    (proEtaleRingModuleAdjunction i R S c).counit_isIso_of_R_fully_faithful⟩

/-- The open and closed factors of extension have their exactness and normalized
adjunction isomorphisms with any identified inverse-image coefficient rings. The closed
comparison is the counit of the specified actual tensor-pullback/direct-image adjunction.

Source: Stacks Project, Tags 03DI, 03DJ, 09AA, 09BM, 09BN and 09AH
(blueprint: lem-sfb-proetale-identified-open-closed).

Proof: transport the ringed open/closed theorem along scalar restriction equivalences.
For the open factor compose scalar transport, the slice equivalence and the sheafified
extension presheaf. Uniqueness of scalar extension as a left adjoint identifies its right
adjoint with the specified tensor pullback. Its left adjoint is fully faithful, since
slice extension has invertible unit. For the closed factor scalar transport followed by
ringed direct image agrees sectionwise with actual identified-coefficient direct image:
both retain the original sections and their linear maps, and their scalar actions agree
by the coefficient adjunction unit. Equivalences and ringed direct image are exact, so
this direct image is exact. The ringed counit makes ringed direct image fully faithful;
scalar equivalence and the sectionwise comparison make actual direct image fully faithful.
Therefore the counit of its specified adjunction is invertible. Ringed cross-vanishing
and scalar transport make the closed restriction of every open extension zero. If a
module sheaf has zero closed restriction, the localization sequence gives an invertible
ringed open counit. The scalar and slice equivalences then exhibit the sheaf in the
actual open extension's essential image, making its specified counit invertible. -/
theorem proEtaleIdentifiedOpenClosed
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Si : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (Su : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Si)
    (cu : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj R ≅ Su) :
    PreservesFiniteLimits (proEtaleRingModuleDirectImage i R Si ci) ∧
      PreservesFiniteColimits (proEtaleRingModuleDirectImage i R Si ci) ∧
        IsIso (proEtaleRingModuleAdjunction i R Si ci).counit ∧
          ∃ F : proEtaleRingModules U.left Su ⥤ proEtaleRingModules X R,
            F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
              ∃ adj : F ⊣ proEtaleRingModulePullback U.hom R Su cu, IsIso adj.unit ∧
                (∀ N, IsZero ((proEtaleRingModulePullback i R Si ci).obj (F.obj N))) ∧
                ∀ M, IsZero ((proEtaleRingModulePullback i R Si ci).obj M) →
                  IsIso (adj.counit.app M) := by
  obtain ⟨hl, hc, hu⟩ := identifiedClosedImage i U hU R Si ci
  exact ⟨hl, hc, hu, identifiedOpenExtension i U hU R Su cu Si ci⟩

end AlgebraicGeometry.Scheme
