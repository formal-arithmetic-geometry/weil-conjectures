/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingSections
public import WeilConjectures.SixFunctors.ProEtale.CoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Mathlib.Algebra.Category.Grp.Zero
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.WeaklyContractibleSections

/-!
# Sections of tensor products over w-contractible objects

Let `W ≅ Spec R` be an object of the small pro-étale site of a scheme `T`, where every faithfully
flat ind-étale `R`-algebra has a retraction (for instance `R` w-contractible). Every covering
sieve of `W` contains a decomposition of `W` into disjoint opens, so a section over `W` of the
sheafification of a presheaf comes, on such a decomposition, from sections of the presheaf.
Applied to the tensor product of sheaves of abelian groups, the sheafification of the objectwise
tensor product, this shows:

- `AlgebraicGeometry.ProEtale.subsingleton_tensor_obj_of_forall_exists_retraction`: if `Z(W) = 0`
  then `(F ⊗ Z)(W) = 0`;
- `AlgebraicGeometry.ProEtale.subsingleton_modSections_tensor`: the same for the relative tensor
  product of module objects over a commutative monoid object `B`;
- `AlgebraicGeometry.ProEtale.bijective_modSections_whiskerLeft`: if a morphism `φ` of module
  objects is bijective on sections over `W`, so is `M ◁ φ`, for every module object `M`. In other
  words the sections over `W` of `M ⊗_B N` only depend on the sections of `N` over `W`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {T : Scheme.{u}}

/-- The lax monoidal structure of the forgetful functor from sheaves to presheaves is locally
surjective: it is the unit of sheafification followed by an isomorphism. -/
instance isLocallySurjective_μ_sheafToPresheaf
    (F G : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
      (μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}) F G) := by
  simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit,
    sheafificationAdjunction_unit_app]
  have : IsIso ((sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
      (Functor.OplaxMonoidal.δ (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        ((sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj F)
        ((sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj G) ≫
        ((sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).counit.app F ⊗ₘ
          (sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).counit.app G))) :=
    inferInstance
  exact Presheaf.isLocallySurjective_comp _ _ _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {T : Scheme.{u}}

/-- If `W` is the disjoint union of two opens `O` and `O'`, a sheaf with subsingleton sections
over `W` has subsingleton sections over `O`. -/
lemma subsingleton_obj_ofOpenImmersion_of_isCompl {W : T.ProEt}
    (Z : Sheaf (ProEt.topology T) Ab.{u + 1}) (O O' : W.left.Opens) (hdisj : Disjoint O O')
    (hcov : O ⊔ O' = ⊤) (hZ : Subsingleton (Z.obj.obj (op W))) :
    Subsingleton (Z.obj.obj (op (ProEt.ofOpenImmersion W O.ι))) := by
  let P : ULift.{u} Bool → W.left.Opens := fun b ↦ cond b.down O O'
  have hcol := (nonempty_isColimit_cofanMk_of (fun b ↦ (P b).ι) (by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ O ⊔ O' := by rw [hcov]; trivial
    rcases hx with hx | hx
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨true⟩, by simpa [P] using hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨false⟩, by simpa [P] using hx⟩)
    (by
      rintro ⟨i⟩ ⟨j⟩ hij
      cases i <;> cases j
      · exact absurd rfl hij
      · simpa [P, Function.onFun] using hdisj.symm
      · simpa [P, Function.onFun] using hdisj
      · exact absurd rfl hij)).some
  have hlim := ProEtale.isLimitSectionsFanOfIsColimitCofan Z
    (fun b ↦ ProEt.ofOpenImmersionHom W (P b).ι) hcol
  have hbij := bijective_of_isLimit_fan _ hlim
  refine ⟨fun z₁ z₂ ↦ ?_⟩
  suffices h : ∀ z : ToType (Z.obj.obj (op (ProEt.ofOpenImmersion W O.ι))), z = 0 by
    rw [h z₁, h z₂]
  intro z
  let t : ∀ b : ULift.{u} Bool,
      ToType (Z.obj.obj (op (ProEt.ofOpenImmersion W (P b).ι))) := fun b ↦
    match b with
    | ⟨true⟩ => z
    | ⟨false⟩ => 0
  obtain ⟨x, hx⟩ := hbij.2 t
  have hx0 : x = 0 := Subsingleton.elim _ _
  have := congrFun hx ⟨true⟩
  simp only [hx0, map_zero] at this
  exact this.symm

/-- Let `W ≅ Spec R` be an object of the small pro-étale site, where every faithfully flat
ind-étale `R`-algebra has a retraction (e.g. `R` is w-contractible). If a sheaf of abelian groups
`Z` has subsingleton sections over `W`, so has `F ⊗ Z` for every `F`: a section of `F ⊗ Z` over
`W` comes, on a cover of `W` by disjoint opens `O i`, from the presheaf tensor product
`F(O i) ⊗ Z(O i)`, and `Z(O i)` vanishes with `Z(W)`. -/
theorem subsingleton_tensor_obj_of_forall_exists_retraction {W : T.ProEt} {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) (F Z : Sheaf (ProEt.topology T) Ab.{u + 1})
    (hZ : Subsingleton (Z.obj.obj (op W))) :
    Subsingleton ((F ⊗ Z).obj.obj (op W)) := by
  suffices h : ∀ s : ToType ((F ⊗ Z).obj.obj (op W)), s = 0 from
    ⟨fun a b ↦ by rw [h a, h b]⟩
  intro s
  have hS := Presheaf.imageSieve_mem (ProEt.topology T)
    (μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}) F Z) s
  obtain ⟨κ, O, hdisj, hcov, hSO⟩ :=
    ProEt.exists_disjoint_opens_of_forall_exists_retraction hR e hS
  have hzero (i : κ) : (F ⊗ Z).obj.map (ProEt.ofOpenImmersionHom W (O i).ι).op s = 0 := by
    obtain ⟨p, hp⟩ := hSO i
    have hZi : Subsingleton (Z.obj.obj (op (ProEt.ofOpenImmersion W (O i).ι))) :=
      subsingleton_obj_ofOpenImmersion_of_isCompl Z (O i) (⨆ (j : κ) (_ : j ≠ i), O j)
        (by
          rw [disjoint_iSup_iff]
          intro j
          rw [disjoint_iSup_iff]
          intro hji
          exact hdisj i j (Ne.symm hji))
        (by
          rw [eq_top_iff]
          intro x _
          obtain ⟨j, hj⟩ := hcov x
          by_cases hji : j = i
          · subst hji
            exact Or.inl hj
          · exact Or.inr (TopologicalSpace.Opens.mem_iSup.2 ⟨j,
              TopologicalSpace.Opens.mem_iSup.2 ⟨hji, hj⟩⟩)) hZ
    have hzero : IsZero ((F.obj ⊗ Z.obj).obj (op (ProEt.ofOpenImmersion W (O i).ι))) := by
      have hZ' : IsZero (Z.obj.obj (op (ProEt.ofOpenImmersion W (O i).ι))) :=
        AddCommGrpCat.isZero_of_subsingleton _
      rw [IsZero.iff_id_eq_zero]
      change 𝟙 (F.obj.obj _ ⊗ Z.obj.obj _) = 0
      rw [← whiskerLeft_id, hZ'.eq_of_src (𝟙 _) 0, MonoidalPreadditive.whiskerLeft_zero]
    have hp0 : p = 0 := (AddCommGrpCat.subsingleton_of_isZero hzero).elim _ _
    subst hp0
    exact hp.symm.trans (map_zero _)
  have hcov' : Sieve.ofArrows _ (fun i ↦ ProEt.ofOpenImmersionHom W (O i).ι) ∈
      ProEt.topology T W :=
    ProEt.mem_topology_of_openImmersion _ (fun i ↦ (O i).ι) (fun x ↦ by
      obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, by simpa using hi⟩) (fun i ↦ Sieve.ofArrows_mk _ _ i)
  refine Sheaf.isSeparated (F ⊗ Z) _ _ hcov' _ _ ?_
  rintro Y g ⟨_, a, _, ⟨i⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    hzero i, map_zero, map_zero, map_zero]


section Mod

variable {B : Sheaf (ProEt.topology T) Ab.{u + 1}} [MonObj B] [IsCommMonObj B]

/-- The sections over `W` of the underlying sheaf of a module object. -/
noncomputable abbrev modSections (W : T.ProEt) :
    Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B ⥤ Ab.{u + 1} :=
  Mod.forget B ⋙ sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W)


omit [IsCommMonObj B] in
/-- Taking sections over a weakly contractible object is exact on module objects. -/
lemma preservesHomology_modSections {W : T.ProEt}
    (hW : (ProEt.topology T).IsWeaklyContractible.{u + 1} W) :
    (modSections (B := B) W).PreservesHomology := by
  have : (modSections (B := B) W).PreservesEpimorphisms := ⟨fun {M N} φ _ ↦ by
    have : Epi φ.hom := (Mod.forget _).map_epi φ
    exact (AddCommGrpCat.epi_iff_surjective _).2
      (surjective_app_of_isWeaklyContractible_ab hW φ.hom)⟩
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

variable {W : T.ProEt} {R : CommRingCat.{u}}
  (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
    [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
  (e : W.left ≅ Spec R)

include hR e in
/-- The relative tensor product of module objects with a module with subsingleton sections over
`W` has subsingleton sections over `W`. -/
lemma subsingleton_modSections_tensor (M N : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)
    (hN : Subsingleton ((modSections W).obj N)) :
    Subsingleton ((modSections W).obj (M ⊗ N)) := by
  have hW := ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e
  have := subsingleton_tensor_obj_of_forall_exists_retraction hR e M.X N.X hN
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a', rfl⟩ := surjective_app_of_isWeaklyContractible_ab hW (Mod.tensorObjπ M N) a
  obtain ⟨b', rfl⟩ := surjective_app_of_isWeaklyContractible_ab hW (Mod.tensorObjπ M N) b
  rw [Subsingleton.elim a' b']

include hR e in
/-- Tensoring a morphism `f` of module objects whose cokernel has subsingleton sections over `W`
gives a morphism which is surjective on sections over `W`. -/
lemma surjective_modSections_whiskerLeft (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)
    {N₁ N₂ : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B} (f : N₁ ⟶ N₂)
    (hf : Subsingleton ((modSections W).obj (cokernel f))) :
    Function.Surjective ((modSections W).map (M ◁ f)) := by
  have := preservesHomology_modSections (B := B)
    (ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e)
  have hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) (tensorLeft M)
  have hex := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk ((tensorLeft M).map f) ((tensorLeft M).map (cokernel.π f))
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])) hc).map
    (modSections W)
  rw [ShortComplex.ab_exact_iff] at hex
  intro x
  exact hex x (@Subsingleton.elim _
    (subsingleton_modSections_tensor hR e M (cokernel f) hf) _ _)

include hR e in
/-- Tensoring an epimorphism `p` of module objects whose kernel has subsingleton sections over
`W` gives a morphism which is injective on sections over `W`. -/
lemma injective_modSections_whiskerLeft_of_epi
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)
    {N₁ N₂ : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B} (p : N₁ ⟶ N₂) [Epi p]
    (hp : Subsingleton ((modSections W).obj (kernel p))) :
    Function.Injective ((modSections W).map (M ◁ p)) := by
  have := preservesHomology_modSections (B := B)
    (ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e)
  have hc := CokernelCofork.mapIsColimit _
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)) (tensorLeft M)
  have hex := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk ((tensorLeft M).map (kernel.ι p)) ((tensorLeft M).map p)
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])) hc).map
    (modSections W)
  rw [ShortComplex.ab_exact_iff] at hex
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hex x hx
  have : y = 0 := @Subsingleton.elim _
    (subsingleton_modSections_tensor hR e M (kernel p) hp) _ _
  rw [this, map_zero]

include hR e in
/-- Tensoring a monomorphism `i` of module objects whose cokernel has subsingleton sections over
`W` gives a morphism which is injective on sections over `W`. This is a diagram chase using an
epimorphism `π : P ⟶ M` from a flat module, for which `P ◁ i` stays a monomorphism. -/
lemma injective_modSections_whiskerLeft_of_mono
    [Abelian.HasFunctorialFlatResolution (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)]
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)
    {N₁ N₂ : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B} (i : N₁ ⟶ N₂) [Mono i]
    (hi : Subsingleton ((modSections W).obj (cokernel i))) :
    Function.Injective ((modSections W).map (M ◁ i)) := by
  have hW := ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e
  have := preservesHomology_modSections (B := B) hW
  obtain ⟨Λ⟩ := (inferInstance :
    Abelian.HasFunctorialFlatResolution (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B))
  let P := (Λ.F.obj M).obj
  let π : P ⟶ M := Λ.π.app M
  have hP : ObjectProperty.flat P := (Λ.F.obj M).property
  have := hP.tensorLeft.preservesFiniteLimits
  have hPi : Mono (P ◁ i) := (tensorLeft P).map_mono i
  have hPi' : Function.Injective ((modSections W).map (P ◁ i)) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  -- the right exact row `K ⊗ N ⟶ P ⊗ N ⟶ M ⊗ N ⟶ 0`
  have hrow (N : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B) :
      ((ShortComplex.mk ((tensorRight N).map (kernel.ι π)) ((tensorRight N).map π)
        (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])).map
          (modSections W)).Exact :=
    (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk ((tensorRight N).map (kernel.ι π)) ((tensorRight N).map π)
        (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero]))
      (CokernelCofork.mapIsColimit _
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel π)) (tensorRight N))).map _
  have hπ (N : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B) :
      Function.Surjective ((modSections W).map (π ▷ N)) := by
    have : Epi (π ▷ N) := (tensorRight N).map_epi π
    have : Epi (π ▷ N).hom := (Mod.forget B).map_epi (π ▷ N)
    exact surjective_app_of_isWeaklyContractible_ab hW (π ▷ N).hom
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ N₁ x
  have h₁ : (modSections W).map (π ▷ N₂) ((modSections W).map (P ◁ i) y) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, whisker_exchange,
      Functor.map_comp, ConcreteCategory.comp_apply]
    exact hx
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1 (hrow N₂) _ h₁
  obtain ⟨z', rfl⟩ := surjective_modSections_whiskerLeft hR e (kernel π) i hi z
  have h₂ : (modSections W).map (P ◁ i) ((modSections W).map (kernel.ι π ▷ N₁) z') =
      (modSections W).map (P ◁ i) y := by
    have hz' : (modSections W).map (kernel.ι π ▷ N₂) ((modSections W).map (kernel π ◁ i) z') =
        (modSections W).map (P ◁ i) y := hz
    rw [← hz', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← whisker_exchange]
  have h₃ : kernel.ι π ▷ N₁ ≫ π ▷ N₁ = 0 := by
    rw [← comp_whiskerRight, kernel.condition, MonoidalPreadditive.zero_whiskerRight]
  rw [← hPi' h₂, ← ConcreteCategory.comp_apply, ← Functor.map_comp, h₃, Functor.map_zero]
  rfl

include hR e in
/-- **Sections of relative tensor products over a w-contractible object only depend on the
sections.** If a morphism `φ` of module objects is bijective on sections over `W`, so is
`M ◁ φ` for every module object `M`. -/
theorem bijective_modSections_whiskerLeft
    [Abelian.HasFunctorialFlatResolution (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)]
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B)
    {N₁ N₂ : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B} (φ : N₁ ⟶ N₂)
    (hφ : Function.Bijective ((modSections W).map φ)) :
    Function.Bijective ((modSections W).map (M ◁ φ)) := by
  have hW := ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e
  have := preservesHomology_modSections (B := B) hW
  have hinj {X Y : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B} (g : X ⟶ Y) [Mono g] :
      Function.Injective ((modSections W).map g) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hsurj {X Y : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B} (g : X ⟶ Y) [Epi g] :
      Function.Surjective ((modSections W).map g) := by
    have : Epi g.hom := (Mod.forget B).map_epi g
    exact surjective_app_of_isWeaklyContractible_ab hW g.hom
  obtain ⟨I, p, i, _, _, rfl⟩ : ∃ (I : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) B) (p : N₁ ⟶ I)
      (i : I ⟶ N₂), Epi p ∧ Mono i ∧ p ≫ i = φ :=
    ⟨_, _, _, inferInstance, inferInstance, Abelian.image.fac φ⟩
  have hp : Subsingleton ((modSections W).obj (kernel p)) := by
    have h0 (c : ToType ((modSections W).obj (kernel p))) :
        (modSections W).map p ((modSections W).map (kernel.ι p) c) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, kernel.condition, Functor.map_zero]
      rfl
    refine ⟨fun a b ↦ hinj (kernel.ι p) (hφ.1 ?_)⟩
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, h0]
  have hi : Subsingleton ((modSections W).obj (cokernel i)) := by
    refine ⟨fun a b ↦ ?_⟩
    suffices h : ∀ c : ToType ((modSections W).obj (cokernel i)), c = 0 by rw [h a, h b]
    intro c
    obtain ⟨c, rfl⟩ := hsurj (cokernel.π i) c
    obtain ⟨c, rfl⟩ := hφ.2 c
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Category.assoc,
      cokernel.condition, comp_zero, Functor.map_zero]
    rfl
  have hcomp {X Y Z : Ab.{u + 1}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      ⇑(ConcreteCategory.hom (f ≫ g)) = ⇑(ConcreteCategory.hom g) ∘ ⇑(ConcreteCategory.hom f) := by
    ext
    rfl
  rw [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, hcomp]
  exact (Function.Bijective.comp
    ⟨injective_modSections_whiskerLeft_of_mono hR e M i hi,
      surjective_modSections_whiskerLeft hR e M i hi⟩
    ⟨injective_modSections_whiskerLeft_of_epi hR e M p hp,
      surjective_modSections_whiskerLeft hR e M p (by
        have : IsZero (cokernel p) := isZero_cokernel_of_epi p
        exact AddCommGrpCat.subsingleton_of_isZero ((modSections W).map_isZero this))⟩)

end Mod

end AlgebraicGeometry.ProEtale
