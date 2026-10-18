/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.LinearAlgebra.StdBasis

/-! # Local lifting from a finite free constant sheaf

Source: Stacks Project, Cohomology on Sites, Tag 094G, lifting finitely many
generators through the epimorphism from cycles to cohomology.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- A map from a finite free constant sheaf lifts locally across an epimorphism.

Source: Stacks Project, Cohomology on Sites, Tag 094G, generator-lifting step.
(blueprint: lem-weil-pbc-local-finite-free-epi-lift)

Proof: An epimorphism of module-valued sheaves is locally surjective. Apply this
to the images of the finitely many standard basis vectors at the object T, and
intersect their covering image sieves. On every member of this common covering,
choose preimages and extend them linearly from the free basis. The constant-sheaf
adjunction on that slice turns the resulting linear map into a sheaf map.
The two composites agree on basis vectors by the preimage equations and the
naturality of the original map from the constant presheaf. The adjunction and
its compatibility with the constant-restriction unit give the required equality
of sheaf maps. This also works in rank zero and on empty slices, and requires
neither points nor Noetherianity. -/
theorem exists_local_lift_from_constant_finite_free
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] (T : C) (r : ℕ)
    (F G : Sheaf J (ModuleCat.{u} B)) (p : F ⟶ G) [Epi p]
    (φ : (constantSheaf J (ModuleCat.{u} B)).obj
      (ModuleCat.of B (Fin r → B)) ⟶ G) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f →
      ∃ ψ : (constantSheaf (J.over U) (ModuleCat.{u} B)).obj
          (ModuleCat.of B (Fin r → B)) ⟶ (J.overPullback (ModuleCat.{u} B) U).obj F,
        ψ ≫ (J.overPullback (ModuleCat.{u} B) U).map p =
          constantSheafOverHom J (ModuleCat.{u} B) U
            (ModuleCat.of B (Fin r → B)) ≫
              (J.overPullback (ModuleCat.{u} B) U).map φ := by
  classical
  let M := ModuleCat.of B (Fin r → B)
  let γ := toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ φ.hom
  let s (i : Fin r) := γ.app (op T) (Pi.basisFun B (Fin r) i)
  have hp : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} B) p).2 inferInstance
  have : Presheaf.IsLocallySurjective J p.hom := hp
  let S (i : Fin r) := Presheaf.imageSieve p.hom (s i)
  refine ⟨⨅ i, S i, J.iInf_mem S (fun i ↦ Presheaf.imageSieve_mem J p.hom (s i)), ?_⟩
  intro U f hf
  have hz (i : Fin r) := (iInf_le S i) f hf
  choose z hz using hz
  let l : (Fin r → B) →ₗ[B] F.obj.obj (op U) :=
    (Pi.basisFun B (Fin r)).constr B z
  let adj := constantSheafAdj (J.over U) (ModuleCat.{u} B) Over.mkIdTerminal
  let ψ := (adj.homEquiv M ((J.overPullback (ModuleCat.{u} B) U).obj F)).symm
    (ModuleCat.ofHom l)
  refine ⟨ψ, ?_⟩
  apply (adj.homEquiv M _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [ψ, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right,
    constantSheafAdj_homEquiv_constantSheafOverHom]
  change ModuleCat.ofHom l ≫ p.hom.app (op U) = γ.app (op U)
  apply ModuleCat.hom_ext
  apply (Pi.basisFun B (Fin r)).ext
  intro i
  change p.hom.app (op U) (l (Pi.basisFun B (Fin r) i)) =
    γ.app (op U) (Pi.basisFun B (Fin r) i)
  rw [Module.Basis.constr_basis]
  apply (hz i).trans
  have hn := γ.naturality f.op
  change (𝟙 M) ≫ γ.app (op U) = γ.app (op T) ≫ G.obj.map f.op at hn
  rw [Category.id_comp] at hn
  exact (congrArg (fun q ↦ q (Pi.basisFun B (Fin r) i)) hn).symm

end CategoryTheory
