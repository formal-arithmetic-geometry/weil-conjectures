/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # The arbitrary-ring-sheaf closed support adjoint

Source: Stacks Project, proetale.tex, Tags 09AA, 09BM, 09BN and 09AH; derived.tex,
Tags 070I, 070K and 08BJ (blueprint: lem-sf-ringed-closed-kernel-adjoint).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The natural kernel of the open adjunction unit, formed in the functor category.
Evaluation identifies it with `ker(N → j_*j^*N)`, including the kernel inclusion.
Source: Stacks, Tag 09AH (blueprint: lem-sf-ringed-closed-kernel-adjoint). -/
noncomputable def ringedSupportKernel {X U : Scheme.{u}} (j : U ⟶ X)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B) :
    proEtaleRingModules X B ⥤ proEtaleRingModules X B :=
  kernel aj.unit

/-- The closed inverse image of the support kernel: the actual underived `i!_0`.
Source: Stacks, Tags 09AA and 09AH (blueprint: lem-sf-ringed-closed-kernel-adjoint). -/
noncomputable def ringedClosedKernelShriek {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B) :=
  ringedSupportKernel j B aj ⋙ proEtaleModuleInverseImage i B

/-- The specified computation on any K-injective resolution, obtained by localizing
its quasi-isomorphism and using the canonical K-injective derived comparison.
Source: Stacks, Tags 070I and 070K (blueprint: lem-sf-ringed-closed-kernel-adjoint). -/
noncomputable def ringedClosedKernelResolutionIso {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B)
    [(ringedClosedKernelShriek i j B aj).Additive]
    {K I : CochainComplex (proEtaleRingModules X B) ℤ}
    (r : K ⟶ I) [QuasiIso r] [I.IsKInjective] :
    (ringedClosedKernelShriek i j B aj).rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ringedClosedKernelShriek i j B aj).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  (ringedClosedKernelShriek i j B aj).rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map r)) ≪≫
    (ringedClosedKernelShriek i j B aj).rightDerivedFunctorObjQIso I

/-- Closed support for arbitrary ring-sheaf coefficients, and all four ambient derived
adjunctions. The comparison with the kernel and the K-injective counit formula fix the
ordinary and derived counits. All module categories use the original small pro-etale
sites, with object universe `u+1`, morphism universe `u`, and module universe `u+1`.

Source: Stacks, Tags 09AA, 09BM, 09BN, 09AH, 070I, 070K, 08BJ and 079P
(blueprint: lem-sf-ringed-closed-kernel-adjoint).

Proof plan:
1. The ringed-topos module adjunction (lem-weil-pbc-ringed-topoi-module-adjunction),
   with the identity coefficient map, gives i* ⊣ i_* and j* ⊣ j_*. The ringed open-closed
   theorem gives exact i_* and j_!, the invertible closed counit and j*i_*=0.
   The immersion limit-preservation theorem makes both inverse images exact.
2. The open comparison (lem-weil-pbc-proetale-ringed-open-comparison) evaluates the open
   counit as the identity on an object already over U. Thus j* of the open unit is invertible.
3. Exact j* kills the kernel H of that unit. Apply the open-closed short exact sequence
   to H. Its left term vanishes, so the closed unit H → i_*i*H is an isomorphism.
   Kernel functoriality and the closed unit make this identification natural.
4. A module map i_*P → N factors uniquely through H_N since its composite with the open
   unit is zero. Closed inverse image and the inverse closed counit give P → i*H_N.
   Conversely use i_*, the inverse supported unit and the kernel inclusion. Naturality
   and the closed triangle identities show these operations are inverse. The adjunct
   of the identity is the inverse supported unit followed by the kernel inclusion.
5. Small-site K-injective resolutions exist by prop-pur-kinjective-resolutions-exist.
   The exact-functor factorization theorem descends the four exact functors termwise
   to the unbounded derived categories.
6. The support functor is additive and right adjoint to exact i_*, hence preserves
   K-injectives by lem-weil-pbc-right-adjoint-preserves-kinjective. Apply
   lem-weil-pbc-kinjective-total-derived to its termwise homotopy functor.
7. Compute Hom into a K-injective resolution using lem-weil-pbc-kinjective-hom-derived,
   the termwise homotopy adjunction, and K-injective preservation. This gives the
   derived support adjunction. Its counit on a K-injective is the termwise sheaf counit;
   for any resolution compose with the inverse of the localized resolution map.
8. Repeat the same Hom calculation for (j_!,j*), (i*,i_*) and (j*,j_*). The exact-functor
   derived theorem identifies the derived exact right adjoints with termwise descent.
9. The closed counit is invertible degreewise. The open derived counit is represented
   on a K-injective by the invertible ordinary open counit. Finally j*i_*=0 degreewise
   descends to the zero derived composite. No supported triangle is used. -/
theorem proEtale_ringed_closed_kernel_adjoint {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ (ai : proEtaleModuleInverseImage i B ⊣ proEtaleRingedDirectImage i B)
      (aj : proEtaleModuleInverseImage U.hom B ⊣ proEtaleRingedDirectImage U.hom B)
      (_ : (proEtaleModuleInverseImage i B).Additive)
      (_ : (proEtaleModuleInverseImage U.hom B).Additive)
      (_ : (proEtaleRingedDirectImage i B).Additive)
      (_ : (proEtaleRingedDirectImage U.hom B).Additive)
      (_ : PreservesFiniteLimits (proEtaleModuleInverseImage i B))
      (_ : PreservesFiniteColimits (proEtaleModuleInverseImage i B))
      (_ : PreservesFiniteLimits (proEtaleModuleInverseImage U.hom B))
      (_ : PreservesFiniteColimits (proEtaleModuleInverseImage U.hom B))
      (_ : PreservesFiniteLimits (proEtaleRingedDirectImage i B))
      (_ : PreservesFiniteColimits (proEtaleRingedDirectImage i B))
      (_ : (ringedClosedKernelShriek i U.hom B aj).Additive)
      (a0 : proEtaleRingedDirectImage i B ⊣ ringedClosedKernelShriek i U.hom B aj)
      (eH : ringedSupportKernel U.hom B aj ≅
        ringedClosedKernelShriek i U.hom B aj ⋙ proEtaleRingedDirectImage i B),
      eH.hom = Functor.whiskerLeft (ringedSupportKernel U.hom B aj) ai.unit ∧
      eH.hom ≫ a0.counit = kernel.ι aj.unit ∧
      (∀ P, IsIso (ai.counit.app P)) ∧
      (∀ P, IsIso (aj.counit.app P)) ∧
      ∃ (q : proEtaleRingModules U.left
          ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj B) ≌
          SheafOfModules.{u + 1} ((proEtaleModuleCoefficients B).over U))
        (_eq : proEtaleModuleInverseImage U.hom B ⋙ q.functor ≅
          SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients B) U)
        (_ : (q.functor ⋙ proEtaleRingedExtensionByZero U B).Additive)
        (_ : PreservesFiniteLimits (q.functor ⋙ proEtaleRingedExtensionByZero U B))
        (_ : PreservesFiniteColimits (q.functor ⋙ proEtaleRingedExtensionByZero U B))
        (_aBang : q.functor ⋙ proEtaleRingedExtensionByZero U B ⊣
          proEtaleModuleInverseImage U.hom B)
        (d0 : (proEtaleRingedDirectImage i B).mapDerivedCategory ⊣
          (ringedClosedKernelShriek i U.hom B aj).rightDerivedFunctor)
        (di : (proEtaleModuleInverseImage i B).mapDerivedCategory ⊣
          (proEtaleRingedDirectImage i B).mapDerivedCategory)
        (dj : (proEtaleModuleInverseImage U.hom B).mapDerivedCategory ⊣
          (proEtaleRingedDirectImage U.hom B).rightDerivedFunctor),
        Nonempty ((q.functor ⋙ proEtaleRingedExtensionByZero U B).mapDerivedCategory ⊣
          (proEtaleModuleInverseImage U.hom B).mapDerivedCategory) ∧
        (∀ P, IsIso (di.counit.app P)) ∧
        (∀ P, IsIso (dj.counit.app P)) ∧
        (∀ P, IsZero ((proEtaleModuleInverseImage U.hom B).mapDerivedCategory.obj
          ((proEtaleRingedDirectImage i B).mapDerivedCategory.obj P))) ∧
        (∀ (I : CochainComplex (proEtaleRingModules Z
            ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj B)) ℤ),
          di.counit.app (DerivedCategory.Q.obj I) =
            (proEtaleModuleInverseImage i B).mapDerivedCategory.map
              ((proEtaleRingedDirectImage i B).mapDerivedCategoryFactors.hom.app I) ≫
            (proEtaleModuleInverseImage i B).mapDerivedCategoryFactors.hom.app
              (((proEtaleRingedDirectImage i B).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((ai.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)) ∧
        (∀ (I : CochainComplex (proEtaleRingModules U.left
            ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj B)) ℤ) [I.IsKInjective],
          dj.counit.app (DerivedCategory.Q.obj I) =
            (proEtaleModuleInverseImage U.hom B).mapDerivedCategory.map
              ((proEtaleRingedDirectImage U.hom B).rightDerivedFunctorObjQIso I).hom ≫
            (proEtaleModuleInverseImage U.hom B).mapDerivedCategoryFactors.hom.app
              (((proEtaleRingedDirectImage U.hom B).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((aj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)) ∧
        (∀ (K I : CochainComplex (proEtaleRingModules X B) ℤ)
          (r : K ⟶ I) [QuasiIso r] [I.IsKInjective],
          d0.counit.app (DerivedCategory.Q.obj K) =
            (proEtaleRingedDirectImage i B).mapDerivedCategory.map
              (ringedClosedKernelResolutionIso i U.hom B aj r).hom ≫
            (proEtaleRingedDirectImage i B).mapDerivedCategoryFactors.hom.app
              (((ringedClosedKernelShriek i U.hom B aj).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((a0.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) ≫
            inv (DerivedCategory.Q.map r))
        := by
  sorry

end AlgebraicGeometry.Scheme
