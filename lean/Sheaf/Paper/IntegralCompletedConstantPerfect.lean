/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.CompletedConstantConstructibility
public import Sheaf.Paper.AdicStratifiedPerfect
public import Sheaf.AlgebraicGeometry.IntegralConstantCompletion

import Sheaf.Paper.IntegralPerfectCohomology
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingTriangleClosure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Integral completed coefficient local models

Source: Bhatt--Scholze, Proposition 6.8.11(3).
(blueprint: lem-sfb-integral-completed-constant-single-perfect).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite SheafOfModules
open scoped ZeroObject ChangeOfRings

namespace DerivedCategory
private theorem finiteProjectiveSingle
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : ModuleCat.{u} A) [Module.Projective A M] [Module.Finite A M] :
    IsPerfectRingComplex ((singleFunctor _ 0).obj M) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  refine ⟨P, 0, 0, inferInstance, inferInstance, ?_,
    ⟨(singleFunctorIsoCompQ _ 0).app M⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩
  · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    constructor <;> infer_instance
private theorem perfectShift
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K : DerivedCategory (ModuleCat.{u} A)} (h : IsPerfectRingComplex K) (n : ℤ) :
    IsPerfectRingComplex (K⟦n⟧) := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := h
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  refine ⟨P⟦n⟧, a - n, b - n, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun i ↦ hP (i + n)
  · exact ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩
private theorem pidFiniteSinglePerfect
    {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    IsPerfectRingComplex ((singleFunctor _ 0).obj M) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' A M
  have hS := LinearMap.shortExact_shortComplexKer hg
  have : Module.Finite A g.ker := inferInstance
  have : Module.Free A g.ker := inferInstance
  exact isPerfectRingComplex_obj₂_of_distTriang hS.singleTriangle.rotate
    (rot_of_distTriang _ hS.singleTriangle_distinguished)
    (finiteProjectiveSingle _) (perfectShift (finiteProjectiveSingle _) 1)
end DerivedCategory

namespace AlgebraicGeometry.Scheme

/-- Canonical coefficient-sized pro-etale sheafification instance.
Source: Stacks Tag 03DA (blueprint: lem-sfb-integral-completed-constant-single-perfect). -/
instance (priority := 3000) integralCompletedConstantPerfectWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

private def realizedSingleIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} A)]
    (M : ModuleCat.{u + 1} A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : (DerivedCategory.singleFunctor _ 0).obj M ≅ DerivedCategory.Q.obj P) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((completedAdicChange X (CompletedConstantReduction.base X I)).obj
        ((adicLisseConstantModules X A).obj M)) ≅ sfbCompletedModel X I P := by
  let C := adicLisseConstantModules X A
  let E := completedAdicChange X (CompletedConstantReduction.base X I)
  have hC := commutativeSiteConstantModuleFunctor_exact (ProEt.topology X) A
  have : C.Additive := hC.1
  have : PreservesFiniteLimits C := hC.2.1
  have : PreservesFiniteColimits C := hC.2.2
  have hE := completedConstantChange_exact X I
  have : PreservesFiniteLimits E := hE.1
  have : PreservesFiniteColimits E := hE.2
  let F := C ⋙ E
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  exact ((F.mapDerivedCategorySingleFunctor 0).app M).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P
private def identityExtensionIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) : changeOfRings.{u, u + 1, u + 1} (𝟙 R) M ≅ M := by
  let e : changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙 R) M ≅ M.val :=
    PresheafOfModules.isoMk (fun V ↦ (ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj V)).app
      (M.val.obj V)) (by
        intro V W f
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        symm
        change M.val.map f ((ModuleCat.extendScalarsId.{u + 1, u + 1}
          (R.obj.obj V)).hom.app _ ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V, RingHom.id _] m)) = _
        rw [ModuleCat.extendScalarsId_hom_app_one_tmul]
        change M.val.map f m =
          (ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj W)).hom.app _
            (changeOfRingsMap (𝟙 R) M f
              ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V, RingHom.id _] m))
        erw [(exists_changeOfRingsMap (𝟙 R) M f).choose_spec (1 : R.obj.obj V) m]
        simp only [map_one]
        rw [ModuleCat.extendScalarsId_hom_app_one_tmul])
  exact (PresheafOfModules.sheafification (𝟙 ((adicLisseForget X).obj R).obj)).mapIso e ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget X).obj R).obj)).counit).app M
private def localRestrictionComparison {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :
    let R' := (adicLisseForget S).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
    letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
    letI := (ringedOverFunctor_exactGeneral R' U).1
    letI := (ringedOverFunctor_exactGeneral R' U).2.1
    letI := (ringedOverFunctor_exactGeneral R' U).2.2
    sfbLocalRestriction i R U K ≅
      (SheafOfModules.overFunctor.{u + 1} R' U).mapDerivedCategory.obj
        ((proEtaleRingModulePullback i R
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
            (Iso.refl _)).mapDerivedCategory.obj K) := by
  let R' := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  let F := proEtaleRingModulePullback i R
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} R' U
  have := (ringedOverFunctor_exactGeneral R' U).1
  have := (ringedOverFunctor_exactGeneral R' U).2.1
  have := (ringedOverFunctor_exactGeneral R' U).2.2
  exact (G.mapDerivedCategoryFactors.app _).symm ≪≫
    G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso _)
private def localRestrictionMapIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    {K L : DerivedCategory (proEtaleRingModules X R)} (e : K ≅ L) :
    sfbLocalRestriction i R U K ≅ sfbLocalRestriction i R U L := by
  let R' := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  let F := proEtaleRingModulePullback i R
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} R' U
  have := (ringedOverFunctor_exactGeneral R' U).1
  have := (ringedOverFunctor_exactGeneral R' U).2.1
  have := (ringedOverFunctor_exactGeneral R' U).2.2
  exact localRestrictionComparison i R U K ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso e) ≪≫
      (localRestrictionComparison i R U L).symm
private def localSingleIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (M : proEtaleRingModules X R) :
    let R' := (adicLisseForget S).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
    letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
    sfbLocalRestriction i R U ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((SheafOfModules.overFunctor.{u + 1} R' U).obj
          ((proEtaleModuleInverseImage i R).obj M)) := by
  let R' := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  let F := proEtaleRingModulePullback i R
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} R' U
  have := (ringedOverFunctor_exactGeneral R' U).1
  have := (ringedOverFunctor_exactGeneral R' U).2.1
  have := (ringedOverFunctor_exactGeneral R' U).2.2
  exact localRestrictionComparison i R U _ ≪≫
    G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (F.obj M) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (G.mapIso (identityExtensionIso S _ _))

/-- A constructible completed-constant module placed in degree zero has stratified
perfect coefficient models, allowing torsion in its finitely presented scalar modules.
Source: Bhatt--Scholze, Proposition 6.8.11(3), finite projective dimension over a DVR.
(blueprint: lem-sfb-integral-completed-constant-single-perfect).
Proof: keep the finite constructible stratification and its covering sieves supplied by
constructibility. For each finitely presented scalar module P choose a finite free module
surjecting onto P. Its kernel is finite over the Noetherian DVR and torsion-free, hence
finite free. The rotated short-exact-sequence triangle, shift closure and perfect triangle
closure yield a bounded finite-projective complex representing P in degree zero. Exact
constant-module realization and completed scalar extension carry its derived isomorphism
to the completed constant module. Immersion and slice restriction are exact, so this
isomorphism restricts to every object of the given covering sieve. Compose with the given
local module isomorphism. The perfect complex supplies all bounds and projectivity witnesses
required by IsSfbStratifiedPerfect. -/
theorem integral_completed_constant_single_perfect
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : proEtaleRingModules X
      (adicLisseCompletedRing X (ProEtale.IntegralConstantCompletion.ideal l E)))
    (hM : IsCompletedConstantStratified X
      (ProEtale.IntegralConstantCompletion.ideal l E) M) :
    IsSfbStratifiedPerfect X (ProEtale.IntegralConstantCompletion.ideal l E)
      ((DerivedCategory.singleFunctor _ 0).obj M)  := by
  let R := Padic.coefficientExtensionIntegers l E
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  let A := ProEtale.IntegralConstantCompletion.integers l E
  let I := ProEtale.IntegralConstantCompletion.ideal l E
  let : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv.symm : R ≃+* A) ULift.ringEquiv.symm.surjective
  let : IsDomain A := MulEquiv.isDomain R ULift.ringEquiv.toMulEquiv
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  obtain ⟨s, hs, hM⟩ := hM
  let t : LocallyClosedStratification X :=
    { n := s.n
      stratum := s.stratum
      isLocallyClosed_stratum := s.isLocallyClosed_stratum
      isConstructible_stratum := hs
      iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
      domain := s.domain
      immersion := s.immersion
      isImmersion := s.isImmersion
      range_immersion := s.range_immersion }
  refine ⟨t, hs, ?_⟩
  intro α
  obtain ⟨V, hV, hM⟩ := hM α
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, hP, ⟨e⟩⟩ := hM U f hf
  have := hP
  obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ := DerivedCategory.pidFiniteSinglePerfect P
  refine ⟨F, a, b, ⟨F, a, b, ha, hb, hF, ⟨Iso.refl _⟩⟩, ha, hb, hF, ⟨?_⟩⟩
  let B := adicLisseCompletedRing X I
  let R' := (adicLisseForget (s.domain α)).obj
    ((proEtaleSheafInverseImage (s.immersion α) CommRingCat.{u + 1}).obj B)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  exact localSingleIso (s.immersion α) B U M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
    (localSingleIso (s.immersion α) B U _).symm ≪≫
    localRestrictionMapIso (s.immersion α) B U (realizedSingleIso X I P F eF)

end AlgebraicGeometry.Scheme
