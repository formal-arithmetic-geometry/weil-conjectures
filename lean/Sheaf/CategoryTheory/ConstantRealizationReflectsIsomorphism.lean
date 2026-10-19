/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Constant realization reflects derived isomorphisms on a nonempty pro-étale object

Source: literature/stacks-project/sites-modules.tex, Tag 093J and Section 03DH
(blueprint: lem-sfb-constant-realization-reflects-isomorphism).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wR wS wU

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace CategoryTheory

/-- Constant realization commutes with cohomology and reflects isomorphisms after
restriction to a nonempty object of the small pro-étale site.

Source: Stacks Project, Sites, Tag 093J; Modules on Sites, Section 03DH;
derived.tex, Tags 05RU and 05RT (blueprint: lem-sfb-constant-realization-reflects-isomorphism).
Proof: the constant module functor and slice restriction are exact, so their derived
functors commute with homology. Naturality descends through the localization defining
the derived category. If the restricted realization of a morphism is invertible,
exactness identifies the restrictions of the kernel and cokernel of each cohomology
map with zero. Constant-module detection on the nonempty object forces those modules
to vanish, hence every cohomology map is invertible; the unbounded derived
cohomology criterion then gives invertibility of the original morphism. -/
theorem constantRealizationReflectsIsomorphism
    {X : Scheme.{u}} (U : X.ProEt) (R : Type (u + 1)) [CommRing R]
    [Nonempty U.left]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u + 1}
        ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u + 1}
        (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of R)).over U))] :
    (∀ i : ℤ,
      Nonempty ((siteDerivedConstantModuleFunctor.{u + 1, u, wR, wS} (Scheme.ProEt.topology X) R ⋙
          ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, wS, wU}
            ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u + 1}
              (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
                (RingCat.of R)).over U)) i) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i ⋙
          siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R ⋙
          SheafOfModules.overFunctor
            ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U))) ∧
      (∀ {C D : DerivedCategory (ModuleCat.{u + 1} R)} (f : C ⟶ D),
        IsIso ((ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, wS, wU}
          ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U).map
          ((siteDerivedConstantModuleFunctor.{u + 1, u, wR, wS}
            (Scheme.ProEt.topology X) R).map f)) →
          IsIso f) := by
  let F := siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R
  let S := (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)
  let G := SheafOfModules.overFunctor.{u + 1} S U
  have : F.Additive := (siteConstantModuleFunctorGeneral_exact.{u + 1, u}
    (Scheme.ProEt.topology X) R).1
  have : PreservesFiniteLimits F := (siteConstantModuleFunctorGeneral_exact.{u + 1, u}
    (Scheme.ProEt.topology X) R).2.1
  have : PreservesFiniteColimits F := (siteConstantModuleFunctorGeneral_exact.{u + 1, u}
    (Scheme.ProEt.topology X) R).2.2
  have : G.Additive := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} S U).1
  have : PreservesFiniteLimits G :=
    (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} S U).2.1
  have : PreservesFiniteColimits G :=
    (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} S U).2.2
  have comparison (i : ℤ) :
      Nonempty ((F.mapDerivedCategory ⋙ G.mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ i) ≅
        (DerivedCategory.homologyFunctor _ i ⋙ F ⋙ G)) := by
    exact ⟨Functor.isoWhiskerLeft _ (G.mapDerivedCategoryHomologyFunctorIso i).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapDerivedCategoryHomologyFunctorIso i).symm _ ≪≫
      Functor.associator _ _ _⟩
  refine ⟨comparison, ?_⟩
  intro C D f hf
  change IsIso (G.mapDerivedCategory.map (F.mapDerivedCategory.map f)) at hf
  have := hf
  apply (DerivedCategory.isIso_iff (ModuleCat.{u + 1} R) f).2
  intro i
  let g := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).map f
  have : IsIso ((F ⋙ G).map g) :=
    (NatIso.isIso_map_iff (comparison i).some f).1 (by
      change IsIso ((DerivedCategory.homologyFunctor _ i).map
        (G.mapDerivedCategory.map (F.mapDerivedCategory.map f)))
      infer_instance)
  have hk : IsZero ((F ⋙ G).obj (kernel g)) :=
    (isZero_kernel_of_mono ((F ⋙ G).map g)).of_iso (PreservesKernel.iso (F ⋙ G) g)
  have hc : IsZero ((F ⋙ G).obj (cokernel g)) :=
    (isZero_cokernel_of_epi ((F ⋙ G).map g)).of_iso (PreservesCokernel.iso (F ⋙ G) g)
  have : Mono g := Preadditive.mono_of_isZero_kernel g
    ((AlgebraicGeometry.ProEtale.constantRealization_detects_zero X R (kernel g) U).2.2 hk)
  have : Epi g := Preadditive.epi_of_isZero_cokernel g
    ((AlgebraicGeometry.ProEtale.constantRealization_detects_zero X R (cokernel g) U).2.2 hc)
  exact isIso_of_mono_of_epi g

end CategoryTheory
