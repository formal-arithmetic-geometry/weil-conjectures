/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-! # Small models of quotient maps from a fixed module sheaf

Source: Stacks Project, Modules, Tag 01BC, proof of
`lemma-set-isomorphism-classes-finite-type-modules`: parametrization by kernel
subsheaves, generalized from a finite free source to a fixed module sheaf
(blueprint: lem-weil-pbc-module-quotient-map-small-models).

The index is the type of literal restriction-stable submodules whose underlying
presheaves satisfy the sheaf axiom. It lies in the same universe as the points and
sections. The quotient maps are cokernels of the actual inclusions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace SheafOfModules

/-- Quotient maps from a fixed module sheaf have small models indexed by its literal
subsheaves, and those maps may be taken to be cokernels of the inclusions.

Source: Stacks Project, Modules, Tag 01BC, proof of
`lemma-set-isomorphism-classes-finite-type-modules`, generalized to a fixed source
(blueprint: lem-weil-pbc-module-quotient-map-small-models).

Proof:
1. The opens of X and all section sets lie in the fixed universe. Families of subsets
   of these section sets form a type in that universe. The submodule, restriction
   stability and sheaf conditions select its subtype of literal module subsheaves.
2. For each such K, sheafify the sectionwise quotient M/K. By the abelian module-sheaf
   category of `def-weil-sheaf-of-modules-category` (Stacks 03DA), this is a cokernel
   of the inclusion, in the same universe. Cokernel uniqueness makes its map epic;
   cokernels also exist by `def-sp-abelian`.
3. For an epimorphism p from M to N, the sectionwise kernels are submodules stable
   under restriction. Compatible sections glue in M and their image is zero by
   separatedness of N. Thus they define a literal subsheaf K and its inclusion is
   the categorical kernel of p.
4. By `def-sp-abelian`, p is a cokernel of some a. Factor a through K. Any map killing
   K kills a, so the cokernel universal property of p makes p a cokernel of K as well.
5. The two cokernel properties give mutually inverse comparison maps between Q_K
   and N. Their defining factorization equations give q_K followed by psi equal to p.
   This proves representation with the same quotient maps, including the cokernel clause.
-/
theorem exists_quotient_map_small_models (X : RingedSpace.{u})
    (M : ringedSiteModules.{u} (moduleRings X)) :
    ∃ (Q : {K : M.val.Submodule //
          Presheaf.IsSheaf (Opens.grothendieckTopology X)
            K.toPresheafOfModules.presheaf} → ringedSiteModules.{u} (moduleRings X))
      (q : ∀ K, M ⟶ Q K),
      (∀ K, Epi (q K)) ∧
      (∀ K, ∃ h :
        (⟨K.val.ι⟩ :
          (⟨K.val.toPresheafOfModules, K.property⟩ :
            ringedSiteModules.{u} (moduleRings X)) ⟶ M) ≫ q K = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ (q K) h))) ∧
      (∀ (N : ringedSiteModules.{u} (moduleRings X)) (p : M ⟶ N),
        Epi p → ∃ K, ∃ ψ : Q K ≅ N, q K ≫ ψ.hom = p) := by
  classical
  let T := {K : M.val.Submodule //
    Presheaf.IsSheaf (Opens.grothendieckTopology X) K.toPresheafOfModules.presheaf}
  let incl (K : T) :
      (⟨K.val.toPresheafOfModules, K.property⟩ :
        ringedSiteModules.{u} (moduleRings X)) ⟶ M := ⟨K.val.ι⟩
  refine ⟨(fun K ↦ cokernel (incl K)), (fun K ↦ cokernel.π (incl K)),
    (fun K ↦ inferInstance), (fun K ↦ ⟨cokernel.condition _, ⟨cokernelIsCokernel _⟩⟩), ?_⟩
  intro N p hp
  let A := kernel p
  let i : A ⟶ M := kernel.ι p
  have : Mono i.val := by
    change Mono ((forget (moduleRings X)).map (kernel.ι p))
    infer_instance
  have hi (U) : Function.Injective (i.val.app U) := by
    apply PresheafOfModules.injective_of_mono
  let K : M.val.Submodule :=
    { obj U := LinearMap.range (i.val.app U).hom
      map := by
        intro U V f x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨A.val.map f y, PresheafOfModules.naturality_apply i.val f y⟩ }
  let e : A.val ≅ K.toPresheafOfModules :=
    PresheafOfModules.isoMk
      (fun U ↦ (LinearEquiv.ofInjective (i.val.app U).hom (hi U)).toModuleIso)
      (by
        intro U V f
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply i.val f x)
  have hK : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      K.toPresheafOfModules.presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso e)).mp A.isSheaf
  let k : T := ⟨K, hK⟩
  let e' : A ≅ (⟨K.toPresheafOfModules, hK⟩ :
      ringedSiteModules.{u} (moduleRings X)) := (fullyFaithfulForget _).preimageIso e
  have he' : e'.hom ≫ incl k = i := by
    ext U x
    rfl
  have he : e'.inv ≫ i = incl k := by
    rw [← he', Iso.inv_hom_id_assoc]
  have hk := IsKernel.isoKernel p (incl k) (kernelIsKernel p) e'.symm he
  let hc := Abelian.epiIsCokernelOfKernel _ hk
  refine ⟨k, (cokernelIsCokernel (incl k)).coconePointUniqueUpToIso hc, ?_⟩
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _ hc WalkingParallelPair.one

end SheafOfModules
