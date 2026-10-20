/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.StrictTowerOperations

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed

/-!
# Exact extension along an arbitrary locally closed immersion

Source: Stacks Project, Tags 09AA, 09BN, 09AH, 03DI and 03DJ
(blueprint: lem-sfb-proetale-locally-closed-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every closed-then-open factorization gives an exact module extension with an
invertible restriction comparison, using the actual composite coefficient identification.
This is a restriction comparison, not a composite adjunction.

Source: Stacks Project, Tags 09AA, 09BN, 09AH, 03DI and 03DJ
(blueprint: lem-sfb-proetale-locally-closed-extension).

Proof: realize the complement of the outer open by its vanishing-ideal subscheme and
use the inner closed immersion's open complement. Since the ambient scheme is Noetherian,
the source of the outer open and every open in it are Noetherian spaces. Thus both opens
are quasi-compact. The identified-coefficient open/closed theorem supplies exact closed
direct image and exact open extension. Compose them. The inverse unit of the open
adjunction and the counit of the closed adjunction, together with the specified inverse
image composition comparison, give the restriction isomorphism. The composite preserves
finite limits and finite colimits and is additive. Its factors are fully faithful by
the invertible open unit and closed counit, so their composite is fully faithful. -/
private theorem closedOpenExtension
    {X V S : Scheme.{u}} [IsNoetherian X]
    (c : S ⟶ V) [IsClosedImmersion c] (v : V ⟶ X) [IsOpenImmersion v]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Rv : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (Rs : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (cv : (proEtaleSheafInverseImage v CommRingCat.{u + 1}).obj R ≅ Rv)
    (cc : (proEtaleSheafInverseImage c CommRingCat.{u + 1}).obj Rv ≅ Rs) :
    ∃ F : proEtaleRingModules S Rs ⥤ proEtaleRingModules X R,
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
        F.Full ∧ F.Faithful ∧
        Nonempty (F ⋙ proEtaleRingModulePullback (c ≫ v) R Rs
          (proEtaleRingCompositeCoefficients c v R Rv Rs cv cc) ≅ 𝟭 _) := by
  let : NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  let : QuasiCompact v := inferInstance
  let Z : TopologicalSpace.Closeds X :=
    ⟨(Set.range v)ᶜ, v.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := IdealSheafData.vanishingIdeal Z
  have hZ : Set.range v = (Set.range I.subschemeι)ᶜ := by
    rw [I.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl (Set.range v)).symm
  let U : X.ProEt := ProEt.mk v
  have : IsOpenImmersion U.hom := ‹IsOpenImmersion v›
  have : QuasiCompact U.hom := ‹QuasiCompact v›
  obtain ⟨_, _, _, O, hOa, hOl, hOc, ao, hOu, _⟩ :=
    proEtaleIdentifiedOpenClosed I.subschemeι U hZ R
      ((proEtaleSheafInverseImage I.subschemeι CommRingCat.{u + 1}).obj R) Rv
      (Iso.refl _) cv
  let W : V.Opens := ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let : NoetherianSpace W.toScheme := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have hW : Set.range W.ι = (Set.range c)ᶜ := W.range_ι
  let U' : V.ProEt := ProEt.mk W.ι
  have : IsOpenImmersion U'.hom := inferInstanceAs (IsOpenImmersion W.ι)
  have : QuasiCompact U'.hom := inferInstanceAs (QuasiCompact W.ι)
  obtain ⟨hGl, hGc, hGu, _⟩ := proEtaleIdentifiedOpenClosed c U' hW Rv Rs
    ((proEtaleSheafInverseImage W.ι CommRingCat.{u + 1}).obj Rv) cc (Iso.refl _)
  let G := proEtaleRingModuleDirectImage c Rv Rs cc
  have : PreservesFiniteLimits G := hGl
  have : PreservesFiniteColimits G := hGc
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts G
  have : G.Additive := G.additive_of_preservesBinaryBiproducts
  have : O.Additive := hOa
  have : PreservesFiniteLimits O := hOl
  have : PreservesFiniteColimits O := hOc
  have : IsIso ao.unit := hOu
  have : IsIso (proEtaleRingModuleAdjunction c Rv Rs cc).counit := hGu
  have : G.Full := (proEtaleRingModuleAdjunction c Rv Rs cc).fullyFaithfulROfIsIsoCounit.full
  have : G.Faithful :=
    (proEtaleRingModuleAdjunction c Rv Rs cc).fullyFaithfulROfIsIsoCounit.faithful
  have : O.Full := ao.fullyFaithfulLOfIsIsoUnit.full
  have : O.Faithful := ao.fullyFaithfulLOfIsIsoUnit.faithful
  let rO : O ⋙ proEtaleRingModulePullback v R Rv cv ≅ 𝟭 _ := (asIso ao.unit).symm
  let rG : G ⋙ proEtaleRingModulePullback c Rv Rs cc ≅ 𝟭 _ :=
    asIso (proEtaleRingModuleAdjunction c Rv Rs cc).counit
  let p := exchangeModuleComposition c v R Rv Rs cv cc
  refine ⟨G ⋙ O, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft (G ⋙ O) p ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft G (Functor.isoWhiskerRight rO _) ≪≫
        Functor.isoWhiskerLeft G (Functor.leftUnitor _) ≪≫ rG

/-- Pointwise exact locally closed extension with actual inverse-image coefficients.
The source coefficient ring may be any specified presentation of inverse image.
The extension is fully faithful on module sheaves.

Source: Stacks Project, Tags 01IO, 09AA, 09BN, 03DI and 03DJ
(blueprint: lem-sfb-proetale-locally-closed-extension).

Proof: factor the immersion as a closed immersion followed by an open immersion. On the
intermediate open use the actual inverse-image coefficient ring. Give the closed factor
its coefficient identification by the inverse of inverse-image composition followed by
the given identification. The composite identification is the original one, by cancellation.
The closed-then-open extension theorem constructs the exact composite functor and its
restriction comparison. Transport that comparison across the coefficient equality. -/
theorem proEtaleLocallyClosedExtension
    {X S : Scheme.{u}} [IsNoetherian X] (f : S ⟶ X) [IsImmersion f]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Rs : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ Rs) :
    ∃ F : proEtaleRingModules S Rs ⥤ proEtaleRingModules X R,
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
        F.Full ∧ F.Faithful ∧
        Nonempty (F ⋙ proEtaleRingModulePullback f R Rs cf ≅ 𝟭 _) := by
  obtain ⟨V, c, v, hc, hv, h⟩ := IsImmersion.isImmersion_iff_exists.mp ‹IsImmersion f›
  subst f
  let := hc
  let := hv
  let Rv := (proEtaleSheafInverseImage v CommRingCat.{u + 1}).obj R
  let cc := ((proEtaleRingInverseImageComp c v).app R).symm ≪≫ cf
  obtain ⟨F, ha, hl, he, hfull, hfaith, ⟨r⟩⟩ := closedOpenExtension c v R Rv Rs (Iso.refl _) cc
  have hp : proEtaleRingCompositeCoefficients c v R Rv Rs (Iso.refl _) cc = cf := by
    dsimp [proEtaleRingCompositeCoefficients, cc]
    simp
  rw [hp] at r
  exact ⟨F, ha, hl, he, hfull, hfaith, ⟨r⟩⟩

end AlgebraicGeometry.Scheme
