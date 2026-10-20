/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.SixFunctors.OpenClosed.Supported
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
import Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Finite duality: comparison for a closed immersion

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph;
Stacks Project, Tags 04CA, 04JC and 014A.
(blueprint: lem-weil-finite-duality-closed-comparison)

The comparison below is formulated with the actual derived direct-image adjunctions.
The isomorphism `δ` is the canonical direct-image comparison of
`lem-weil-pbc-comparison-direct-image-canonical-mate`, transported from its bounded-below
mate along an explicit bounded-below lift by the named Plus/full compatibility isomorphisms.
The transpose formula is the definition of the comparison map `α`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The transpose `α` used in the closed comparison: the `Rₚ ⊣ Iₚ` transpose of
`δ⁻¹` followed by the etale counit.  This is a genuine construction from the two
adjunctions and the named direct-image comparison; no choice or postponed theorem is
used in the definition.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph
(blueprint: lem-weil-finite-duality-closed-comparison). -/
noncomputable def finiteDualityClosedComparisonAlpha
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T U : Scheme.{u}}
    (_i : Z ⟶ T) (_j : U ⟶ T)
    (Rₑ : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Iₑ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Rₚ : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A)))
    (Iₚ : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)))
    (F_T : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A)))
    (F_Z : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)))
    (adjₑ : Rₑ ⊣ Iₑ) (adjₚ : Rₚ ⊣ Iₚ)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (δ : F_T.obj (Rₑ.obj (Iₑ.obj M)) ≅ Rₚ.obj (F_Z.obj (Iₑ.obj M))) :
    F_Z.obj (Iₑ.obj M) ⟶ Iₚ.obj (F_T.obj M) :=
  (adjₚ.homEquiv (F_Z.obj (Iₑ.obj M)) (F_T.obj M))
    (δ.inv ≫ F_T.map (adjₑ.counit.app M))

/-- The canonical component `δ` of the direct-image comparison, transported from the
bounded-below mate `fixedComparisonDirectImageMatePlus`.  The input `e` is the chosen
bounded-below lift of the etale object.  All comparison isomorphisms are the named Plus/full
compatibility isomorphisms, so this is independent of an arbitrary choice of a natural
isomorphism.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph
(blueprint: lem-weil-finite-duality-closed-comparison). -/
noncomputable def finiteDualityClosedComparisonDelta
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory).obj
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj X) ⟶
    ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj X) :=
  let rE := (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility
  let rP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility
  let fT :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusCompatibility
  let fZ :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlusCompatibility
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map e.hom ≫ rE.inv.app L) ≫
    fT.inv.app ((Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus.obj L) ≫
    DerivedCategory.Plus.ι.map
      ((ProEtale.fixedComparisonDirectImageMatePlus A i).app L) ≫
    rP.hom.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
      (fZ.hom.app L ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map e.inv)

set_option backward.isDefEq.respectTransparency false in
/-- The transported canonical closed-comparison component is invertible.

Source: the canonical direct-image mate argument in
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first
paragraph (blueprint: lem-weil-finite-duality-closed-comparison).

Proof plan: unfold the transported component and use the qcqs invertibility
of `ProEtale.fixedComparisonDirectImageMatePlus`; the named Plus/full
compatibility isomorphisms and the isomorphism `e` preserve `IsIso` under
composition and functorial mapping.
-/
theorem isIso_finiteDualityClosedComparisonDelta_proof
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L) :
    IsIso (finiteDualityClosedComparisonDelta i X L e) := by
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus A i
  unfold finiteDualityClosedComparisonDelta
  dsimp -failIfUnchanged only [Etale.rightDerivedLowerStar]
  infer_instance

/- The postponed theorem is registered as an instance directly, so that `asIso` applies
to the canonical component; no further declaration or proof is added. -/
attribute [instance] isIso_finiteDualityClosedComparisonDelta_proof

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedComparisonDelta_naturality
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    {X Y : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (L L' : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L)
    (e' : Y ≅ DerivedCategory.Plus.ι.obj L') (f : X ⟶ Y) :
    finiteDualityClosedComparisonDelta i X L e ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map f) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map f) ≫
      finiteDualityClosedComparisonDelta i Y L' e' := by
  let g : L ⟶ L' := DerivedCategory.Plus.ι.preimage (e.inv ≫ f ≫ e'.hom)
  have hg : DerivedCategory.Plus.ι.map g = e.inv ≫ f ≫ e'.hom :=
    DerivedCategory.Plus.ι.map_preimage _
  let RE := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
  let RP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let FZ := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let b : DerivedCategory.Plus.ι ⋙ RE ⋙ FT ⟶ DerivedCategory.Plus.ι ⋙ FZ ⋙ RP :=
    Functor.whiskerRight
        (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility.inv FT ≫
      Functor.whiskerLeft (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
          ).mapDerivedCategoryPlusCompatibility.inv ≫
      Functor.whiskerRight (ProEtale.fixedComparisonDirectImageMatePlus A i)
        DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) i
          ).rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerRight
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z
        ).mapDerivedCategoryPlusCompatibility.hom RP
  have hf : f = e.hom ≫ DerivedCategory.Plus.ι.map g ≫ e'.inv := by
    rw [hg]
    simp
  rw [hf]
  simpa [finiteDualityClosedComparisonDelta, b, RE, RP, FT, FZ,
    Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ FT.map (RE.map e.hom) ≫ k ≫ RP.map (FZ.map e'.inv))
      (b.naturality g).symm

open Etale in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedLowerStar_isLeftAdjoint
    (A : Type (u + 1)) [Ring A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint := by
  let C := ModuleCat.{u + 1} A
  let W : T.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hji : Disjoint (Set.range W.ι.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  let F := lowerStar C i
  let L := upperStar C i
  let J := upperStar C W.ι
  let adj := upperStarLowerStarAdjunction C W.ι
  have : (lowerStar C W.ι).Full :=
    (openImmersionRestrictionLowerStarAdjunction C W.ι).full_R_of_isSplitMono_counit_app
  have : (lowerStar C W.ι).Faithful :=
    (openImmersionRestrictionLowerStarAdjunction C W.ι).faithful_R_of_epi_counit_app
  -- Restriction kills the kernel of its unit.
  let K (N : Sheaf T.smallEtaleTopology C) := kernel (adj.unit.app N)
  have hK (N : Sheaf T.smallEtaleTopology C) : IsZero (J.obj (K N)) := by
    have : IsIso (J.map (adj.unit.app N)) := inferInstance
    exact (isZero_kernel_of_mono (J.map (adj.unit.app N))).of_iso
      (PreservesKernel.iso J (adj.unit.app N))
  let adjI := upperStarLowerStarAdjunction C i
  have hunit (N : Sheaf T.smallEtaleTopology C) : IsIso (adjI.unit.app (K N)) :=
    (adjI.isIso_unit_app_iff_mem_essImage).mpr
      (mem_essImage_lowerStar_of_isZero_upperStar i hij (hK N))
  -- Maps out of a closed pushforward vanish after restriction to the open part.
  have hz (M : Sheaf Z.smallEtaleTopology C) (N : Sheaf T.smallEtaleTopology C)
      (f : F.obj M ⟶ N) : f ≫ adj.unit.app N = 0 := by
    apply (adj.homEquiv (F.obj M) (J.obj N)).symm.injective
    exact (isZero_upperStar_lowerStar_of_disjoint_range C W.ι i hji M).eq_of_src _ _
  -- Factor through the kernel, identify it with a closed pushforward, then use fullness.
  let e (M : Sheaf Z.smallEtaleTopology C) (N : Sheaf T.smallEtaleTopology C) :
      (F.obj M ⟶ N) ≃ (M ⟶ L.obj (K N)) :=
    { toFun := fun f ↦ F.preimage
        (kernel.lift (adj.unit.app N) f (hz M N f) ≫ adjI.unit.app (K N))
      invFun := fun g ↦ F.map g ≫ inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N)
      left_inv := by
        intro f
        simp
      right_inv := by
        intro g
        apply F.map_injective
        simp only [Functor.map_preimage]
        rw [← cancel_mono (inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N))]
        simp }
  have he : ∀ M' M N f g, e M' N (F.map f ≫ g) = f ≫ e M N g := by
    intro M' M N f g
    apply F.map_injective
    simp only [Functor.map_comp]
    apply (cancel_mono (inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N))).1
    simp [e]
  exact (Adjunction.adjunctionOfEquivRight e he).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedRightAdjoint_boundedBelow
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    letI : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
    ∃ L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Nonempty ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint.obj M ≅
        DerivedCategory.Plus.ι.obj L) := by
  letI : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) i
  letI : F.IsLeftAdjoint := closedLowerStar_isLeftAdjoint A i
  let adj := Adjunction.ofIsLeftAdjoint F
  letI : F.rightAdjoint.Additive := adj.right_adjoint_additive
  let adjD := adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    F.rightDerivedFunctorIsoMapDerivedCategory.symm
  let e := (Adjunction.ofIsLeftAdjoint F.rightDerivedFunctor).rightAdjointUniq adjD
  let Mplus : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨M, hM⟩
  exact ⟨F.rightAdjoint.rightDerivedFunctorPlus.obj Mplus,
    ⟨e.app M ≪≫ (F.rightAdjoint.rightDerivedFunctorPlusCompatibility.app Mplus).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedComparisonAlpha_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    [hRE : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint]
    [QuasiCompact i] [QuasiSeparated i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint.obj M ≅
      DerivedCategory.Plus.ι.obj L)
    [hδ : IsIso (finiteDualityClosedComparisonDelta i _ L e)] :
    IsIso (finiteDualityClosedComparisonAlpha i j
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i)
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
      (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
      (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i))
      (ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij) M
      (asIso (finiteDualityClosedComparisonDelta i _ L e))) := by
  let C := ModuleCat.{u + 1} A
  let RE := Etale.rightDerivedLowerStar C i
  let RP := (ProEtale.lowerStar C i).rightDerivedFunctor
  let IP := (ProEtale.closedUpperShriek C i j).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar C T).mapDerivedCategory
  let adjE := Adjunction.ofIsLeftAdjoint RE
  let adjP := ProEtale.derivedLowerStarClosedUpperShriekAdjunction (R := A) i j hij
  let JP := (ProEtale.upperStar C j).mapDerivedCategory
  let GP := (ProEtale.lowerStar C j).rightDerivedFunctor
  let adjj := (ProEtale.upperStarLowerStarAdjunction C j
    ).mapDerivedCategoryRightDerivedAdjunction
  letI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  have hz (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) :
      IsZero (JP.obj (RP.obj P)) := by
    have hz' : IsZero (JP.obj ((ProEtale.lowerStar C i).mapDerivedCategory.obj P)) :=
      (Functor.isZero_mapDerivedCategory_obj (ProEtale.lowerStar C i ⋙
        ProEtale.upperStar C j) P
        (fun n ↦ ProEtale.isZero_upperStar_lowerStar_of_disjoint C i j hij.disjoint
          ((DerivedCategory.homologyFunctor _ n).obj P))).of_iso
          (((ProEtale.lowerStar C i).mapDerivedCategoryCompIso
            (ProEtale.upperStar C j)).symm.app P)
    exact hz'.of_iso (JP.mapIso
      ((ProEtale.lowerStar C i).rightDerivedFunctorIsoMapDerivedCategory.app P))
  have hkill (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U) C)) :
      IsZero (IP.obj (GP.obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (adjP.homEquiv _ _).symm.injective
    letI : Subsingleton (JP.obj (RP.obj (IP.obj (GP.obj N))) ⟶ N) :=
      ⟨fun f g ↦ (hz _).eq_of_src f g⟩
    haveI : Subsingleton (RP.obj (IP.obj (GP.obj N)) ⟶ GP.obj N) :=
      (adjj.homEquiv (RP.obj (IP.obj (GP.obj N))) N).symm.subsingleton
    exact Subsingleton.elim _ _
  let JE := (Etale.upperStar C j).mapDerivedCategory
  let GE := Etale.rightDerivedLowerStar C j
  let Mplus : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C) := ⟨M, hM⟩
  let Lopen := (Etale.upperStar C j).mapDerivedCategoryPlus.obj Mplus
  let eopen : JE.obj M ≅ DerivedCategory.Plus.ι.obj Lopen :=
    ((Etale.upperStar C j).mapDerivedCategoryPlusCompatibility.app Mplus).symm
  have hopen : IsZero (IP.obj (FT.obj (GE.obj (JE.obj M)))) :=
    (hkill _).of_iso (IP.mapIso
      (asIso (finiteDualityClosedComparisonDelta j (JE.obj M) Lopen eopen)))
  obtain ⟨w, hw⟩ := Etale.exists_etale_closedSupportTriangle A i j hij.eq_compl
  have hdist := IP.map_distinguished _ (FT.map_distinguished _ (hw M))
  have hc : IsIso (IP.map (FT.map (adjE.counit.app M))) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hdist).1 hopen
  unfold finiteDualityClosedComparisonAlpha
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  infer_instance

/-!
The closed finite-duality comparison.  The hypotheses on the structure morphisms record
the finite-type, separated finite-field setting of the source; the bounded-below lift is
the first clause of the conclusion, and `δ` is the named canonical direct-image comparison.
-/
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- For a separated finite-type scheme over an algebraically closed finite-field fibre,
the ambient etale and pro-etale closed right adjoints agree on bounded constructible
complexes through the canonical comparison mate.  The mate is invertible, satisfies the
exceptional-counit normalization, and is natural in the complex.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph;
Stacks Project, Tags 04CA, 04JC and 014A.
(blueprint: lem-weil-finite-duality-closed-comparison)

Proof plan recorded for the postponed theorem: (1) finiteness of `A` and Noetherian finite-type
hypotheses give the required qcqs maps; (2) the etale support triangle and exact inverse image
show `Iₑ.obj M` is bounded below; (3) the closed pro-etale direct image is exact and fully
faithful after passage to derived categories; (4) the canonical Plus mate is transported to the
full derived category by the named Plus/full compatibility isomorphisms; (5) the etale and
pro-etale support triangles and the open comparison give the counit normalization and
invertibility; (6) naturality follows from naturality of the mate and adjunction transpose
injectivity. These are exactly the six steps of the source proof.
-/
theorem finiteDualityClosedComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hne : l ≠ D.p) [Fact l.Prime]
    (T Z U : Scheme.{u})
    (aT : T ⟶ Spec (.of D.k))
    (aZ : Z ⟶ Spec (.of D.k))
    (aU : U ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (i : Z ⟶ T) [IsClosedImmersion i] [QuasiCompact i] [QuasiSeparated i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (_hi : i ≫ aT = aZ) (_hj : j ≫ aT = aU)
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (n : ℕ) (hn : 1 ≤ n)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    :
    let A := Padic.coefficientExtensionRing l E n
    letI : Finite A := Padic.finite_coefficientExtensionRing l E n hn
    let Rₑ := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
    letI : Rₑ.IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
    let Iₑ := Rₑ.rightAdjoint
    let Rₚ := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
    let Iₚ := (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
    let F_T := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
    let F_Z := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
    let adjₑ : Rₑ ⊣ Iₑ := Adjunction.ofIsLeftAdjoint Rₑ
    let adjₚ : Rₚ ⊣ Iₚ :=
      ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij
    ∀ (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_hM : Etale.DerivedCategory.isBoundedConstructible A T M),
      (∃ L : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Nonempty (Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L)) ∧
      (∀ (L : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (e : Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L),
        let δ := finiteDualityClosedComparisonDelta i (Iₑ.obj M) L e
        let δIso : F_T.obj (Rₑ.obj (Iₑ.obj M)) ≅
            Rₚ.obj (F_Z.obj (Iₑ.obj M)) := asIso δ
        let α := finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
          adjₑ adjₚ M δIso
        IsIso α ∧
        (δ ≫ Rₚ.map α ≫ adjₚ.counit.app (F_T.obj M) =
          F_T.map (adjₑ.counit.app M)) ∧
        (∀ (N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (h : M ⟶ N) (_hN : Etale.DerivedCategory.isBoundedConstructible A T N)
          (L' : DerivedCategory.Plus
            (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (e' : Iₑ.obj N ≅ DerivedCategory.Plus.ι.obj L'),
          let δ' := finiteDualityClosedComparisonDelta i (Iₑ.obj N) L' e'
          let δIso' : F_T.obj (Rₑ.obj (Iₑ.obj N)) ≅
              Rₚ.obj (F_Z.obj (Iₑ.obj N)) := asIso δ'
          F_Z.map (Iₑ.map h) ≫
              finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
                adjₑ adjₚ N δIso' =
            finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
              adjₑ adjₚ M δIso ≫ Iₚ.map (F_T.map h))) := by
  clear hne
  let A := Padic.coefficientExtensionRing l E n
  letI : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let RE := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
  letI : RE.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
  let IE := RE.rightAdjoint
  let RP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
  let IP := (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let FZ := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let adjE : RE ⊣ IE := Adjunction.ofIsLeftAdjoint RE
  let adjP : RP ⊣ IP := ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij
  dsimp only
  intro M hM
  have hMplus : DerivedCategory.TStructure.t.plus M := by
    obtain ⟨a, b, _, hv⟩ := hM.2
    exact ⟨a, (DerivedCategory.isGE_iff M a).2 (fun q hq ↦ hv q (Or.inl hq))⟩
  refine ⟨closedRightAdjoint_boundedBelow A i M hMplus, ?_⟩
  intro L e
  let d := finiteDualityClosedComparisonDelta i (IE.obj M) L e
  letI : IsIso d := isIso_finiteDualityClosedComparisonDelta_proof i (IE.obj M) L e
  let a := finiteDualityClosedComparisonAlpha i j RE IE RP IP FT FZ adjE adjP M (asIso d)
  change IsIso a ∧
    (d ≫ RP.map a ≫ adjP.counit.app (FT.obj M) = FT.map (adjE.counit.app M)) ∧ _
  refine ⟨closedComparisonAlpha_isIso A i j hij M hMplus L e, ?_, ?_⟩
  · have hc : RP.map a ≫ adjP.counit.app (FT.obj M) =
        (asIso d).inv ≫ FT.map (adjE.counit.app M) := by
      exact (adjP.homEquiv_counit (FZ.obj (IE.obj M)) (FT.obj M) a).symm.trans
        ((adjP.homEquiv _ _).symm_apply_apply _)
    simpa [Category.assoc] using congrArg (fun k ↦ d ≫ k) hc
  · intro N h hN L' e'
    let d' := finiteDualityClosedComparisonDelta i (IE.obj N) L' e'
    change FZ.map (IE.map h) ≫
        (adjP.homEquiv _ _) ((asIso d').inv ≫ FT.map (adjE.counit.app N)) =
      (adjP.homEquiv _ _) ((asIso d).inv ≫ FT.map (adjE.counit.app M)) ≫ IP.map (FT.map h)
    apply (adjP.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hd := closedComparisonDelta_naturality i L L' e e' (IE.map h)
    have hi : RP.map (FZ.map (IE.map h)) ≫ (asIso d').inv =
        (asIso d).inv ≫ FT.map (RE.map (IE.map h)) := by
      apply (cancel_epi d).1
      apply (cancel_mono d').1
      simpa [Category.assoc] using hd
    rw [reassoc_of% hi, ← FT.map_comp]
    rw [adjE.counit_naturality h]
    simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry
