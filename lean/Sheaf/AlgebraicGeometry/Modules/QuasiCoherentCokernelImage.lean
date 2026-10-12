/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Mathlib.LinearAlgebra.Isomorphisms
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Cokernels and images of quasi-coherent modules

Source: Stacks Project, Schemes, Tags 01IC, 01IB, 01LB; Modules, Tag 01AH
(blueprint: lem-weil-pbc-quasi-coherent-module-cokernel-image).

The categorical cokernel is the sheafified presheaf quotient (Mathlib's module
sheafification adjunction and colimit construction). The abelian image is its kernel;
the local-image formula below identifies it with the subsheaf in the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem surjective_affine_of_epi {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Epi f] [M.IsQuasicoherent] [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective (f.app U) := by
  have := isQuasicoherent_kernel f
  let S := ShortComplex.kernelSequence (C := SheafOfModules.{u} X.ringCatSheaf) f
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := by dsimp [S, ShortComplex.kernelSequence]; infer_instance }
  exact surjective_app_of_cechAcyclicOnAffines
    (hS.map_of_exact (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
    (cechAcyclicOnAffines_of_isQuasicoherent (kernel f)) hU

/-- Cokernels and local images of maps of quasi-coherent modules are quasi-coherent,
and their sections on affine opens are the module cokernel and image.
Source: Stacks Project, Schemes, Tags 01IC, 01IB, 01LB; Modules, Tag 01AH
(blueprint: lem-weil-pbc-quasi-coherent-module-cokernel-image).

Proof:
1. Restrict to an affine open using
`lem-weil-pbc-module-restriction-open-immersion-colimits`: restriction preserves
cokernels and quasi-coherence (pqf-def-coherent).
2. On Spec R, use lem-weil-pbc-affine-tilde-gamma-adjunction, clauses (3), (4), (2),
and lem-weil-pbc-spec-module-tilde-sections. The tilde/global-sections identifications
turn the map into an R-linear map; tilde preserves its cokernel. Its global sections
are the quotient by the range, with surjective projection and precisely that kernel.
3. Affine neighbourhoods cover the scheme. Quasi-coherence is local, so the cokernel
is quasi-coherent; lem-weil-pbc-quasi-coherent-module-kernel gives quasi-coherence
of the kernel of its projection.
4. By lem-weil-pbc-sheaf-cokernel-local-image and def-weil-pbc-sheafification, a
section of this kernel is exactly a section locally in the image. This identifies
the abelian image with the local-image subsheaf, gives the factorization and the
epimorphic quotient map annihilating the original map, and the affine formulas
from step 2 give all the sectionwise conclusions. -/
theorem quasiCoherent_cokernel_image {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Mono (Abelian.image.ι φ) ∧
    (∀ W : X.Opens,
      LinearMap.range ((Abelian.image.ι φ).val.app (op W)).hom =
        LinearMap.ker ((cokernel.π φ).val.app (op W)).hom) ∧
    (∀ (W : X.Opens) (s : Γ(G, W)),
      s ∈ Set.range ((Abelian.image.ι φ).app W) ↔
        ∀ x : X, x ∈ W → ∃ (V : X.Opens) (h : V ≤ W),
          x ∈ V ∧ ∃ t : Γ(F, V), φ.app V t = G.presheaf.map (homOfLE h).op s) ∧
    Abelian.factorThruImage φ ≫ Abelian.image.ι φ = φ ∧
    Epi (cokernel.π φ) ∧ φ ≫ cokernel.π φ = 0 ∧
    (cokernel φ).IsQuasicoherent ∧ (Abelian.image φ).IsQuasicoherent ∧
    (∀ U : X.affineOpens,
      Set.range ((Abelian.image.ι φ).app U.1) = Set.range (φ.app U.1) ∧
      Function.Surjective ((cokernel.π φ).app U.1) ∧
      LinearMap.ker ((cokernel.π φ).val.app (op U.1)).hom =
        LinearMap.range (φ.val.app (op U.1)).hom ∧
      ∃ e : (Γ(G, U.1) ⧸ LinearMap.range (φ.val.app (op U.1)).hom) ≃ₗ[Γ(X, U.1)]
          Γ(cokernel φ, U.1),
        ∀ s : Γ(G, U.1),
          e ((LinearMap.range (φ.val.app (op U.1)).hom).mkQ s) =
            (cokernel.π φ).app U.1 s) := by
  have := isQuasicoherent_cokernel φ
  have := isQuasicoherent_kernel (cokernel.π φ)
  have hr (W : X.Opens) :
      LinearMap.range ((Abelian.image.ι φ).val.app (op W)).hom =
        LinearMap.ker ((cokernel.π φ).val.app (op W)).hom := by
    ext s
    exact Set.ext_iff.mp (range_map_kernelι W (cokernel.π φ)) s
  refine ⟨inferInstance, hr, ?_, Abelian.image.fac φ, inferInstance,
    cokernel.condition φ, inferInstance, inferInstance, ?_⟩
  · intro W s
    constructor
    · rintro ⟨t, rfl⟩
      have hepi : Epi
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map (Abelian.factorThruImage φ)) :=
        Functor.map_epi _ _
      have hloc : TopCat.Presheaf.IsLocallySurjective
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map (Abelian.factorThruImage φ)).hom :=
        (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hepi
      intro x hx
      obtain ⟨V, hVW, ⟨a, ha⟩, hxV⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff _).mp hloc W t x hx
      refine ⟨V, hVW, hxV, a, ?_⟩
      change (Abelian.factorThruImage φ).app V a =
        (Abelian.image φ).presheaf.map (homOfLE hVW).op t at ha
      conv_lhs => rw [← Abelian.image.fac φ, Hom.comp_app, ConcreteCategory.comp_apply]
      rw [ha, Hom.app_presheaf_map]
    · intro h
      have hz : (cokernel.π φ).app W s = 0 := by
        classical
        choose V hVW hxV a ha using fun x : W ↦ h x.1 x.2
        refine TopCat.Sheaf.eq_of_locally_eq' ⟨(cokernel φ).presheaf,
          (cokernel φ).isSheaf⟩ V W (fun x ↦ homOfLE (hVW x)) ?_ _ _ ?_
        · intro x hx
          exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
        · intro x
          rw [map_zero, ← Hom.app_presheaf_map, ← ha x,
            ← ConcreteCategory.comp_apply, ← Hom.comp_app, cokernel.condition, Hom.zero_app]
          rfl
      exact (Set.ext_iff.mp (range_map_kernelι W (cokernel.π φ)) s).mpr hz
  · intro U
    have hp := surjective_affine_of_epi (Abelian.factorThruImage φ) U.2
    have hq := surjective_affine_of_epi (cokernel.π φ) U.2
    have hri : Set.range ((Abelian.image.ι φ).app U.1) = Set.range (φ.app U.1) := by
      conv_rhs => rw [← Abelian.image.fac φ, Hom.comp_app]
      ext s
      constructor
      · rintro ⟨t, rfl⟩
        obtain ⟨a, rfl⟩ := hp t
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨(Abelian.factorThruImage φ).app U.1 a, rfl⟩
    have hk : LinearMap.ker ((cokernel.π φ).val.app (op U.1)).hom =
        LinearMap.range (φ.val.app (op U.1)).hom := by
      rw [← hr U.1]
      ext s
      exact Set.ext_iff.mp hri s
    refine ⟨hri, hq, hk, ?_⟩
    let q := ((cokernel.π φ).val.app (op U.1)).hom
    let e := (Submodule.quotEquivOfEq _ _ hk.symm).trans
      (q.quotKerEquivOfSurjective hq)
    refine ⟨e, fun s ↦ ?_⟩
    exact q.quotKerEquivOfSurjective_apply_mk hq s

end AlgebraicGeometry.Scheme.Modules
