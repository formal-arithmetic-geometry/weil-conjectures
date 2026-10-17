/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Sections with support in a closed part

We work in an abstract *open–closed situation*: abelian categories `𝒳`, `𝒵`, `𝒱` (sheaves on
`X`, on a closed part `Z` and on its open complement `V`), with adjunctions `i^* ⊣ i_*` and
`j^* ⊣ j_*` such that

* `i^*`, `j^*` are exact and `i_*` is exact,
* the counits `i^* i_* ⟶ 𝟭` and `j^* j_* ⟶ 𝟭` are invertible (`i_*`, `j_*` fully faithful),
* `j^* i_* = 0`, and `i^*`, `j^*` jointly detect zero objects.

The functor of *sections with support in `Z`* is `Γ_Z(M) = i^* ker(M ⟶ j_* j^* M)`
(`CategoryTheory.SectionsWithSupport.functor`). We show (blueprint
`det-lem-formal-closed-support-adjunction`, whose proof only uses these properties):

1. `ker(M ⟶ j_* j^* M) ≅ i_* Γ_Z(M)` and `Γ_Z` is right adjoint to `i_*`
   (`CategoryTheory.SectionsWithSupport.adjunction`); in particular it is left exact;
2. `RΓ_Z` is right adjoint to `i_*` on the derived categories
   (`CategoryTheory.SectionsWithSupport.derivedAdjunction`);
3. given moreover an exact left adjoint `j_! ⊣ j^*` with invertible unit and `i^* j_! = 0`, the
   unit `I ⟶ j_* j^* I` is an epimorphism for every injective `I`
   (`CategoryTheory.SectionsWithSupport.epi_unit_app_of_injective`);
4. the counit `i_* RΓ_Z K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a distinguished
   triangle, with a unique third map, natural in `K`
   (`CategoryTheory.SectionsWithSupport.existsUnique_distTriang`), and
   `RΓ_Z K ≅ i^* fib(K ⟶ Rj_* j^* K)`
   (`CategoryTheory.SectionsWithSupport.nonempty_iso_upperStar_fib`).
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.SectionsWithSupport

variable {𝒳 𝒵 𝒱 : Type*} [Category 𝒳] [Category 𝒵] [Category 𝒱] [Abelian 𝒳] [Abelian 𝒵]
  [Abelian 𝒱] {iUp : 𝒳 ⥤ 𝒵} {iLow : 𝒵 ⥤ 𝒳} {jUp : 𝒳 ⥤ 𝒱} {jLow : 𝒱 ⥤ 𝒳}
  (adjI : iUp ⊣ iLow) (adjJ : jUp ⊣ jLow)
  [iUp.Additive] [iLow.Additive] [jUp.Additive] [jLow.Additive]
  [PreservesFiniteLimits iUp] [PreservesFiniteColimits iUp]
  [PreservesFiniteLimits jUp] [PreservesFiniteColimits jUp]
  [IsIso adjI.counit] [IsIso adjJ.counit]

section Sheaves

include adjI in
/-- An exact functor sends the kernel of a morphism `u` to the kernel of its image; if the image
of `u` is a monomorphism, the image of `kernel u` is zero. -/
lemma isZero_obj_kernel_of_mono {F : 𝒳 ⥤ 𝒵} [F.Additive] [PreservesFiniteLimits F] {M N : 𝒳}
    (u : M ⟶ N) [Mono (F.map u)] : IsZero (F.obj (kernel u)) :=
  (isZero_kernel_of_mono (F.map u)).of_iso (PreservesKernel.iso F u)

/-- If the counit of `j^* ⊣ j_*` is invertible, `j^*` inverts the unit `M ⟶ j_* j^* M`. -/
lemma isIso_map_unit_app (M : 𝒳) : IsIso (jUp.map (adjJ.unit.app M)) := by
  have : IsIso (jUp.map (adjJ.unit.app M) ≫ adjJ.counit.app (jUp.obj M)) := by
    rw [adjJ.left_triangle_components M]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adjJ.counit.app _)

variable {adjJ} in
include adjI in
/-- A morphism of `𝒳` inverted by `i^*` and `j^*` is an isomorphism, when `i^*` and `j^*` are
exact and jointly detect zero objects. -/
lemma isIso_of_isIso_map (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F)
    {M N : 𝒳} (u : M ⟶ N) [IsIso (iUp.map u)] [IsIso (jUp.map u)] : IsIso u := by
  have hk : IsZero (kernel u) := hdet _
    ((isZero_kernel_of_mono (iUp.map u)).of_iso (PreservesKernel.iso iUp u))
    ((isZero_kernel_of_mono (jUp.map u)).of_iso (PreservesKernel.iso jUp u))
  have hc : IsZero (cokernel u) := hdet _
    ((isZero_cokernel_of_epi (iUp.map u)).of_iso (PreservesCokernel.iso iUp u))
    ((isZero_cokernel_of_epi (jUp.map u)).of_iso (PreservesCokernel.iso jUp u))
  have := Preadditive.mono_of_isZero_kernel u hk
  have := Preadditive.epi_of_isZero_cokernel u hc
  exact isIso_of_mono_of_epi u

include adjJ in
/-- An object `N` with `j^* N = 0` is `i_*` of `i^* N`: the unit `N ⟶ i_* i^* N` is an
isomorphism. -/
lemma isIso_unit_app_of_isZero (h₀ : ∀ A, IsZero (jUp.obj (iLow.obj A)))
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F) {N : 𝒳}
    (hN : IsZero (jUp.obj N)) : IsIso (adjI.unit.app N) := by
  have : IsIso (iUp.map (adjI.unit.app N)) := by
    have : IsIso (iUp.map (adjI.unit.app N) ≫ adjI.counit.app (iUp.obj N)) := by
      rw [adjI.left_triangle_components N]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adjI.counit.app _)
  have : IsIso (jUp.map (adjI.unit.app N)) :=
    isIso_of_source_target_iso_zero _ hN.isoZero (h₀ _).isoZero
  exact isIso_of_isIso_map adjI hdet _

/-- `j^*` kills the kernel of the unit `M ⟶ j_* j^* M`. -/
lemma isZero_upperStar_kernel (M : 𝒳) : IsZero (jUp.obj (kernel (adjJ.unit.app M))) :=
  have := isIso_map_unit_app adjJ M
  (isZero_kernel_of_mono (jUp.map (adjJ.unit.app M))).of_iso (PreservesKernel.iso jUp _)

include adjI in
/-- A morphism `i_* A ⟶ M` composes to zero with the unit `M ⟶ j_* j^* M`. -/
lemma comp_unit_app_eq_zero (h₀ : ∀ A, IsZero (jUp.obj (iLow.obj A))) {A : 𝒵} {M : 𝒳}
    (f : iLow.obj A ⟶ M) : f ≫ adjJ.unit.app M = 0 := by
  rw [← adjJ.unit_naturality f, ((jLow.map_isZero (h₀ A)).eq_of_tgt
    (adjJ.unit.app (iLow.obj A)) 0), zero_comp]

variable (h₀ : ∀ A, IsZero (jUp.obj (iLow.obj A)))
  (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F)

/-- The bijection `Hom(i_* A, M) ≃ Hom(A, i^* ker(M ⟶ j_* j^* M))`. -/
noncomputable def homEquiv (A : 𝒵) (M : 𝒳) :
    (iLow.obj A ⟶ M) ≃ (A ⟶ iUp.obj (kernel (adjJ.unit.app M))) :=
  have := isIso_unit_app_of_isZero adjI adjJ h₀ hdet (isZero_upperStar_kernel adjJ M)
  { toFun f := adjI.fullyFaithfulROfIsIsoCounit.preimage
      (kernel.lift _ f (comp_unit_app_eq_zero adjI adjJ h₀ f) ≫
        adjI.unit.app (kernel (adjJ.unit.app M)))
    invFun g := iLow.map g ≫ inv (adjI.unit.app (kernel (adjJ.unit.app M))) ≫ kernel.ι _
    left_inv f := by simp
    right_inv g := by
      apply adjI.fullyFaithfulROfIsIsoCounit.map_injective
      simp only [Functor.FullyFaithful.map_preimage]
      have : kernel.lift (adjJ.unit.app M) (iLow.map g ≫
          inv (adjI.unit.app (kernel (adjJ.unit.app M))) ≫ kernel.ι _)
          (by simp [comp_unit_app_eq_zero adjI adjJ h₀]) =
          iLow.map g ≫ inv (adjI.unit.app (kernel (adjJ.unit.app M))) := by
        ext; simp
      simp [this] }

/-- **Sections with support in the closed part** (blueprint
`det-lem-formal-closed-support-adjunction`): the functor `Γ_Z(M) = i^* ker(M ⟶ j_* j^* M)`,
right adjoint to `i_*`. -/
noncomputable def functor : 𝒳 ⥤ 𝒵 :=
  Adjunction.rightAdjointOfEquiv (G_obj := fun M ↦ iUp.obj (kernel (adjJ.unit.app M)))
    (homEquiv adjI adjJ h₀ hdet) (fun A A' M f g ↦ by
      apply adjI.fullyFaithfulROfIsIsoCounit.map_injective
      simp only [homEquiv, Equiv.coe_fn_mk, Functor.FullyFaithful.map_preimage, Functor.map_comp]
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      ext
      simp)

/-- The value of `Γ_Z` on `M` is `i^* ker(M ⟶ j_* j^* M)`. -/
lemma functor_obj (M : 𝒳) : (functor adjI adjJ h₀ hdet).obj M = iUp.obj (kernel (adjJ.unit.app M)) :=
  rfl

/-- **`i_* ⊣ Γ_Z`** (blueprint `det-lem-formal-closed-support-adjunction` (1)). -/
noncomputable def adjunction : iLow ⊣ functor adjI adjJ h₀ hdet :=
  Adjunction.adjunctionOfEquivRight _ _

/-- `Γ_Z` is left exact, being a right adjoint. -/
lemma preservesFiniteLimits_functor : PreservesFiniteLimits (functor adjI adjJ h₀ hdet) :=
  (adjunction adjI adjJ h₀ hdet).rightAdjoint_preservesLimits.preservesFiniteLimits

/-- **`ker(M ⟶ j_* j^* M) ≅ i_* Γ_Z(M)`** (blueprint `det-lem-formal-closed-support-adjunction`
(1)). -/
noncomputable def kernelIso (M : 𝒳) :
    kernel (adjJ.unit.app M) ≅ iLow.obj ((functor adjI adjJ h₀ hdet).obj M) :=
  have := isIso_unit_app_of_isZero adjI adjJ h₀ hdet (isZero_upperStar_kernel adjJ M)
  asIso (adjI.unit.app (kernel (adjJ.unit.app M)))

end Sheaves

end CategoryTheory.SectionsWithSupport
