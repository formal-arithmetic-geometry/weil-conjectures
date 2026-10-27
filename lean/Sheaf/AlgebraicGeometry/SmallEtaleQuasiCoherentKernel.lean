/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Mathlib.Algebra.Exact.Basic

import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Kernels of quasi-coherent modules on the small étale site

Source: Stacks Project, Descent, Tag 0GNB(3), via Tag 06VE(1),(5)
(blueprint: lem-trf-scheme-etale-quasi-coherent-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem restriction_additive (T : Scheme.{u}) (c : ZariskiEtaleModuleContext T) :
    c.restriction.Additive := by
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  rfl

private noncomputable def extension_kernel_isLimit (T : Scheme.{u})
    (c : ZariskiEtaleModuleContext T)
    (e : ∀ (F : T.Modules) [F.IsQuasicoherent],
      (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj (c.extension.obj F) ≅
        etaleTensorSectionsSheaf F)
    (he : ∀ (F G : T.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
        (f : F ⟶ G) (V : T.Etale),
      ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
        (c.extension.map f)).hom.app (op V) ≫ (e G).hom.hom.app (op V) =
          (e F).hom.hom.app (op V) ≫ ((tensorPullback V.hom).map f).app ⊤)
    {F G : T.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    IsLimit (KernelFork.ofι (f := c.extension.map f) (c.extension.map (kernel.ι f)) (by
      have : c.restriction.Additive := restriction_additive T c
      have : c.extension.Additive := c.adjunction.left_adjoint_additive
      simp only [← Functor.map_comp, kernel.condition, Functor.map_zero])) := by
  have : c.restriction.Additive := restriction_additive T c
  have : c.extension.Additive := c.adjunction.left_adjoint_additive
  have : (kernel f).IsQuasicoherent := isQuasicoherent_kernel f
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let S' := S.map c.extension
  let A := SheafOfModules.toSheaf (smallEtaleModuleRing T) ⋙
    sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}
  apply isLimitOfReflects A
  apply evaluationJointlyReflectsLimits
  intro V
  let E := A ⋙ (CategoryTheory.evaluation T.Etaleᵒᵖ AddCommGrpCat.{u}).obj V
  have : (tensorPullback V.unop.hom).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction V.unop.hom)).left_adjoint_additive
  have : PreservesFiniteLimits (tensorPullback V.unop.hom) :=
    (flat_module_pullback_exact_pushforward_injective V.unop.hom).1.1
  let D := tensorPullback V.unop.hom ⋙ globalSectionsFunctor V.unop.left
  have hD : IsLimit ((KernelFork.ofι (kernel.ι f) (kernel.condition f)).map D) := by
    have hp := (KernelFork.ofι (kernel.ι f) (kernel.condition f)).mapIsLimit
      (kernelIsKernel f) (tensorPullback V.unop.hom)
    have := (globalSectionsFunctor_additive_leftExact V.unop.left).2
      ((tensorPullback V.unop.hom).map f)
    exact ((KernelFork.ofι (kernel.ι f) (kernel.condition f)).map
      (tensorPullback V.unop.hom)).mapIsLimit hp (globalSectionsFunctor V.unop.left)
  have hSD : (S.map D).Exact ∧ Mono (S.map D).f :=
    ⟨(S.map D).exact_of_f_is_kernel hD, mono_of_isLimit_fork hD⟩
  let i : S'.map E ≅ S.map D := ShortComplex.isoMk
    ((CategoryTheory.evaluation T.Etaleᵒᵖ AddCommGrpCat.{u}).obj V |>.mapIso
      ((sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}).mapIso (e (kernel f))))
    ((CategoryTheory.evaluation T.Etaleᵒᵖ AddCommGrpCat.{u}).obj V |>.mapIso
      ((sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}).mapIso (e F)))
    ((CategoryTheory.evaluation T.Etaleᵒᵖ AddCommGrpCat.{u}).obj V |>.mapIso
      ((sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}).mapIso (e G)))
    (he _ _ (kernel.ι f) V.unop).symm (he _ _ f V.unop).symm
  have hSE := (ShortComplex.exact_and_mono_f_iff_of_iso i).mpr hSD
  have : Mono (S'.map E).f := hSE.2
  change IsLimit (E.mapCone (KernelFork.ofι S'.f S'.zero))
  exact (KernelFork.isLimitMapConeEquiv (KernelFork.ofι S'.f S'.zero) E).symm
    hSE.1.fIsKernel

/-- A kernel of quasi-coherent small étale modules is quasi-coherent. On every étale object,
its canonical inclusion identifies its sections with the kernel of the component map.
Here `smallEtaleModuleRing T` has section ring `Γ(U.left, ⊤)` at `U : T.Etale`.
Source: Stacks Project, Descent, Tag 0GNB(3), and Tag 06VE(1),(5)
(blueprint: lem-trf-scheme-etale-quasi-coherent-kernel).

Proof:
1. Restrict M and N to quasi-coherent Zariski modules F and G using
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. Restrict φ to f : F → G.
   The counit isomorphisms identify the extension of f with φ. The same theorem
   identifies the sections of each extended module H with Γ(U, u^*H), naturally in H.
2. Form the Zariski kernel i : K → F. By lem-weil-pbc-quasi-coherent-module-kernel,
   K is quasi-coherent; its étale extension is quasi-coherent by the equivalence.
3. For every étale u : U → T, u is flat. The proved result
   lem-weil-pbc-flat-module-pullback-exact-pushforward-injective says that tensor
   pullback preserves finite limits. Its adjunction makes it additive. Composing
   with the kernel-preserving global sections functor gives an exact section
   complex Γ(U, u^*K) → Γ(U, u^*F) → Γ(U, u^*G), with monic first arrow.
4. The natural section isomorphisms identify this complex with the evaluated
   extended kernel complex. Evaluations jointly reflect presheaf limits, and the
   forgetful functor from module sheaves to additive presheaves reflects limits.
   Therefore the extension of i is a kernel of the extension of f. Uniqueness of
   kernels and the counit isomorphisms identify the extension of K with ker φ.
   Transport quasi-coherence across that isomorphism. Finally evaluation preserves
   the actual kernel fork of φ, giving the asserted sectionwise injectivity and
   exactness. -/
theorem isQuasicoherent_smallEtale_kernel (T : Scheme.{u})
    {M N : ringedSiteModules.{u} (smallEtaleModuleRing T)}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (kernel φ).IsQuasicoherent ∧
      ∀ U : T.Etale,
        Function.Injective ((kernel.ι φ).val.app (op U)) ∧
          Function.Exact ((kernel.ι φ).val.app (op U)) (φ.val.app (op U)) := by
  constructor
  · obtain ⟨c, hL, hR, e, _, he, _⟩ := scheme_zariski_etale_quasiCoherent_equivalence
    have : ∀ V : T.Etale, HasSheafify (T.smallEtaleTopology.over V) AddCommGrpCat.{u} :=
      fun V ↦ (Scheme.Etale.overEquiv V).hasSheafify (T.smallEtaleTopology.over V)
        V.left.smallEtaleTopology AddCommGrpCat.{u}
    let F := (c T).restriction.obj M
    let G := (c T).restriction.obj N
    have : F.IsQuasicoherent := (hR T M).1
    have : G.IsQuasicoherent := (hR T N).1
    have : IsIso ((c T).adjunction.counit.app M) := (hR T M).2
    have : IsIso ((c T).adjunction.counit.app N) := (hR T N).2
    let f : F ⟶ G := (c T).restriction.map φ
    have : (kernel f).IsQuasicoherent := isQuasicoherent_kernel f
    let k := extension_kernel_isLimit T (c T) (e T) (he T) f
    let ik : (c T).extension.obj (kernel f) ≅ kernel ((c T).extension.map f) :=
      k.conePointUniqueUpToIso (limit.isLimit _)
    let j : kernel ((c T).extension.map f) ≅ kernel φ :=
      kernel.mapIso _ _ (asIso ((c T).adjunction.counit.app M))
        (asIso ((c T).adjunction.counit.app N))
        ((c T).adjunction.counit.naturality φ)
    exact (SheafOfModules.isQuasicoherent (smallEtaleModuleRing T)).prop_of_iso
      (ik ≪≫ j) (hL T (kernel f)).1
  · intro U
    let E := SheafOfModules.evaluation (smallEtaleModuleRing T) (op U)
    have hlim : IsLimit (KernelFork.ofι (E.map (kernel.ι φ))
        (by simpa [E] using (E.map_comp (kernel.ι φ) φ).symm)) := by
      exact (KernelFork.ofι (kernel.ι φ) (kernel.condition φ)).mapIsLimit
        (kernelIsKernel φ) E
    let S : ShortComplex (ModuleCat.{u} ((smallEtaleModuleRing T).obj.obj (op U))) :=
      ShortComplex.mk (E.map (kernel.ι φ)) (E.map φ) (by
        simpa [E] using (E.map_comp (kernel.ι φ) φ).symm)
    have hS : S.Exact := S.exact_of_f_is_kernel hlim
    have hfun : Function.Exact S.f S.g :=
      (LinearMap.exact_iff).mpr hS.moduleCat_range_eq_ker.symm
    have hmono : Function.Injective S.f :=
      ModuleCat.mono_iff_injective _ |>.mp (mono_of_isLimit_fork hlim)
    exact ⟨hmono, hfun⟩

end AlgebraicGeometry.Scheme.Modules
