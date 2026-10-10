/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Sections of quasi-coherent modules form an fpqc sheaf

For a quasi-coherent module `N` on a scheme `X`, the presheaf `(y : Y ⟶ X) ↦ Γ(y^* N, ⊤)` on
schemes over `X` is a sheaf for the fpqc topology. We state this for sections over an open `O`
of `X` and a sieve on `X` whose restriction to `O` is an fpqc covering.

The proof identifies sections of `y^* N` with morphisms `y^* 𝒪_X ⟶ y^* N`
(`AlgebraicGeometry.Scheme.Modules.homSection`) and uses the fpqc sheaf property of the
presheaf of morphisms (`AlgebraicGeometry.isSheaf_presheafHom`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
lemma isSheafFor_presheafHom_of_mem_fpqcTopology {S : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op S)))
    (hM : (M : S.Modules).IsQuasicoherent) (hN : (N : S.Modules).IsQuasicoherent)
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S) :
    Presieve.IsSheafFor (modulesPseudofunctor.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  have h := bijective_toDescentData_map_of_mem_fpqcTopology
    (fun (i : R.arrows.category) ↦ i.obj.hom)
    (by rwa [Sieve.ofArrows_category', Sieve.generate_sieve]) M N hM hN
  rw [Pseudofunctor.bijective_toDescentData_map_iff] at h
  convert! h
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.mk_surjective X
    obtain rfl : f = Over.homMk g := by ext; simpa using Over.w f
    exact Presieve.ofArrows.mk (ι := R.arrows.category) ⟨Over.mk g, hf⟩
  · rintro _ _ ⟨_, h⟩
    exact h

set_option backward.isDefEq.respectTransparency false in
lemma isSheafFor_presheafHom_of_mem_over {S₀ : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op S₀)))
    (hM : (M : S₀.Modules).IsQuasicoherent) (hN : (N : S₀.Modules).IsQuasicoherent)
    {U : Over S₀} (R : Sieve U) (hR : R ∈ (Scheme.fpqcTopology.over S₀) U) :
    Presieve.IsSheafFor (modulesPseudofunctor.presheafHom M N) R.arrows := by
  obtain ⟨S, a, rfl⟩ := U.mk_surjective
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨R, rfl⟩ := (Sieve.overEquiv (Over.mk a)).symm.surjective R
  rw [OrderIso.apply_symm_apply] at hR
  have h := isSheafFor_presheafHom_of_mem_fpqcTopology
    ((modulesPseudofunctor.map a.op.toLoc).toFunctor.obj M)
    ((modulesPseudofunctor.map a.op.toLoc).toFunctor.obj N)
    (Scheme.Modules.isQuasicoherent_pullback (M := (M : S₀.Modules)) a)
    (Scheme.Modules.isQuasicoherent_pullback (M := (N : S₀.Modules)) a) _ hR
  rw [← Presieve.isSheafFor_iff_of_iso (modulesPseudofunctor.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert! h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    change b.left ≫ 𝟙 _ = _ at fac
    rw [Category.comp_id] at fac
    change R.arrows b.left
    simpa [fac] using R.downward_closed h d.left

/-- For quasi-coherent `M` and `N` on `S`, the presheaf `Hom(- ^* M, - ^* N)` on schemes over `S`
is a sheaf for the fpqc topology. -/
lemma isSheaf_presheafHom {S : Scheme.{u}} (M N : modulesPseudofunctor.obj (.mk (op S)))
    (hM : (M : S.Modules).IsQuasicoherent) (hN : (N : S.Modules).IsQuasicoherent) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (modulesPseudofunctor.presheafHom M N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR
  exact isSheafFor_presheafHom_of_mem_over M N hM hN R hR

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **Sections of a quasi-coherent module are separated for the fpqc topology.** Two sections
of `N` over `O` agree if their pullbacks along all members of a sieve which restricts to an fpqc
covering of `O` agree. -/
theorem sections_ext_of_mem_fpqcTopology (N : X.Modules) [N.IsQuasicoherent] {O : X.Opens}
    (R : Sieve X) (hR : Sieve.pullback O.ι R ∈ Scheme.fpqcTopology O.toScheme)
    {s t : Γ(N, O)}
    (h : ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X), R y →
      pullbackUnitApp y N O s = pullbackUnitApp y N O t) : s = t := by
  sorry

/-- **Sections of a quasi-coherent module glue for the fpqc topology.** A family of sections of
the pullbacks of `N` along the members of a sieve which restricts to an fpqc covering of `O`,
compatible with further pullback, comes from a section of `N` over `O`. -/
theorem exists_sections_of_mem_fpqcTopology (N : X.Modules) [N.IsQuasicoherent] {O : X.Opens}
    (R : Sieve X) (hR : Sieve.pullback O.ι R ∈ Scheme.fpqcTopology O.toScheme)
    (x : ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X), R y → Γ((pullback y).obj N, y ⁻¹ᵁ O))
    (hx : ∀ ⦃Z Z' : Scheme.{u}⦄ (y : Z ⟶ X) (hy : R y) (g : Z' ⟶ Z),
      x (g ≫ y) (R.downward_closed hy g) =
        ((pullbackComp g y).hom.app N).app _ (pullbackUnitApp g _ (y ⁻¹ᵁ O) (x y hy))) :
    ∃ s : Γ(N, O), ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X) (hy : R y),
      pullbackUnitApp y N O s = x y hy := by
  sorry

end Scheme.Modules

end AlgebraicGeometry
