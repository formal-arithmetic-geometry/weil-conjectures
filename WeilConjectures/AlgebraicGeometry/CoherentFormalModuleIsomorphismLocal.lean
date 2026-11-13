/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-!
# Isomorphisms of coherent formal modules are local

Source: Stacks Project, Cohomology of Schemes, Lemma 30.23.2 (Tag 087X),
the locality assertion following the construction of kernels and cokernels.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Isomorphisms in Coh(X,I) are detected on any open covering. The index `op n`
is positive level `n + 1`; restriction is the usual restriction of module sheaves.
Source: Stacks Project, Lemma 30.23.2 (Tag 087X), locality in part (3). -/
theorem coherentFormalModule_isIso_of_isIso_restrict
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    {F G : CoherentFormalModule X I} (α : F ⟶ G)
    (hα : ∀ (j : J) (n : ℕ),
      IsIso ((Scheme.Modules.restrictFunctor (U j).ι).map (α.hom.app (op n)))) :
    IsIso α ∧ ∃ β : G ⟶ F,
      α ≫ β = 𝟙 F ∧ β ≫ α = 𝟙 G ∧
      ∀ n : ℕ, ∃ e : F.obj.obj (op n) ≅ G.obj.obj (op n),
        e.hom = α.hom.app (op n) ∧ e.inv = β.hom.app (op n) := by
  classical
  have hlevel (n : ℕ) : IsIso (α.hom.app (op n)) := by
    suffices IsIso ((Scheme.Modules.toPresheaf X).map (α.hom.app (op n))) by
      exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf X)
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    let φ := (SheafOfModules.toSheaf X.ringCatSheaf).map (α.hom.app (op n))
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    apply TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective φ W.unop
    intro x hx
    have hxcover : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
    have := hα j n
    exact Scheme.Modules.bijective_stalk_of_isIso_restrict (α.hom.app (op n)) x hj
  have : IsIso α.hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact hlevel n.unop
  have : IsIso α := (ObjectProperty.isIso_hom_iff α).mp inferInstance
  refine ⟨inferInstance, inv α, IsIso.hom_inv_id α, IsIso.inv_hom_id α, ?_⟩
  intro n
  refine ⟨asIso (α.hom.app (op n)), rfl, ?_⟩
  simp

end AlgebraicGeometry
