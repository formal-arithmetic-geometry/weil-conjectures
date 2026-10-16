/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Directed colimits of faithfully flat algebras

Source: Stacks Project, Algebra, Tag 090N, `lemma-colimit-faithfully-flat`
(blueprint: lem-weil-pbc-directed-colimit-faithfully-flat-algebras).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

open scoped TensorProduct in
/-- A nonempty directed colimit of faithfully flat commutative `R`-algebras is
faithfully flat over `R`. No condition is imposed on the transition algebra maps.

Source: Stacks Project, Algebra, Tag 090N, `lemma-colimit-faithfully-flat`
(blueprint: lem-weil-pbc-directed-colimit-faithfully-flat-algebras).

Proof:
1. Each stage is flat by `def-weil-pbc-faithfully-flat-ring-map`. Forgetting the
   algebra colimit to modules and applying `lem-weil-pbc-filtered-colimit-flat-modules`
   makes the colimit flat over `R`.
2. For every maximal ideal `m` of `R`, every stage quotient by `m` is nonzero by
   `lem-weil-pbc-faithfully-flat-maximal-ideal-nonzero`. Apply
   `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` with `R / m`.
   If the class of one vanished in the colimit quotient, it would vanish at a
   later stage. Unitality of the transition maps contradicts the nonzero stage
   quotients. Thus the colimit quotient by `m` is nonzero.
3. Apply `lem-weil-pbc-flat-faithfully-flat-maximal-ideals` to the flat colimit
   and these nonzero maximal-ideal quotients to obtain faithful flatness. -/
theorem directedColimit_faithfullyFlat
    (R : Type u) [CommRing R]
    {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ CommAlgCat.{v, u} R) [HasColimit F]
    (hfaithful : ∀ i : I, Module.FaithfullyFlat R (F.obj i)) :
    Module.FaithfullyFlat R (colimit F : CommAlgCat.{v, u} R) :=
  set_option linter.style.haveILetI false in by
  let G : I ⥤ ModuleCat.{v} R :=
    { obj := fun i => ModuleCat.of R (F.obj i)
      map := fun f => ModuleCat.ofHom (F.map f).hom.toLinearMap
      map_id := by
        intro i
        apply ModuleCat.hom_ext
        simp
      map_comp := by
        intro i j k f g
        apply ModuleCat.hom_ext
        simp }
  let c : Cocone G :=
    { pt := ModuleCat.of R ((colimit F : CommAlgCat.{v, u} R) : Type v)
      ι :=
        { app := fun i => ModuleCat.ofHom (colimit.ι F i).hom.toLinearMap
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            exact LinearMap.ext fun x => ConcreteCategory.congr_hom (colimit.w F f) x } }
  have hc : IsColimit c := by
    apply IsColimit.ofExistsUnique
    intro s
    let fs : ∀ i : I, (F.obj i : Type v) →ₗ[R] (s.pt : Type v) :=
      fun i => (s.ι.app i).hom
    obtain ⟨l, hl, hu⟩ := filtered_colimit_algebras_underlying_module F s.pt fs (by
      intro i j f
      apply LinearMap.ext
      intro x
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (s.w f)) x)
    refine ⟨ModuleCat.ofHom l, ?_, ?_⟩
    · intro i
      apply ModuleCat.hom_ext
      exact hl i
    · intro m hm
      apply ModuleCat.hom_ext
      apply hu
      intro i
      exact congrArg ModuleCat.Hom.hom (hm i)
  have hflatG : Module.Flat R ((colimit G : ModuleCat.{v} R) : Type v) :=
    ModuleCat.filteredColimit_flat G (fun i => (hfaithful i).toFlat)
  let e : colimit G ≅ c.pt := (colimit.isColimit G).coconePointUniqueUpToIso hc
  have hflat : Module.Flat R ((colimit F : CommAlgCat.{v, u} R) : Type v) := by
    change Module.Flat R (c.pt : Type v)
    letI : Module.Flat R ((colimit G : ModuleCat.{v} R) : Type v) := hflatG
    exact Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  letI : Module.Flat R ((colimit F : CommAlgCat.{v, u} R) : Type v) := hflat
  refine Module.FaithfullyFlat.of_nontrivial_tensor_quotient (R := R) ?_
  intro m hm
  have hstage : ∀ i : I, Nontrivial ((R ⧸ m) ⊗[R] (F.obj i : Type v)) := by
    intro i
    have hne : m • (⊤ : Submodule R (F.obj i : Type v)) ≠ ⊤ :=
      (hfaithful i).submodule_ne_top hm
    have hq : Nontrivial ((F.obj i : Type v) ⧸ m • (⊤ : Submodule R (F.obj i : Type v))) :=
      not_subsingleton_iff_nontrivial.mp ((Submodule.Quotient.subsingleton_iff).not.mpr hne)
    have hnt : ¬ Subsingleton ((R ⧸ m) ⊗[R] (F.obj i : Type v)) := by
      intro h
      letI : Subsingleton ((R ⧸ m) ⊗[R] (F.obj i : Type v)) := h
      have hq' : Subsingleton ((F.obj i : Type v) ⧸ m • (⊤ : Submodule R (F.obj i : Type v))) :=
        (TensorProduct.quotTensorEquivQuotSMul (F.obj i : Type v) m).symm.injective.subsingleton
      exact (not_subsingleton_iff_nontrivial.mpr hq) hq'
    exact not_subsingleton_iff_nontrivial.mp hnt
  let i : I := Classical.choice (inferInstance : Nonempty I)
  let t : (F.obj i : Type v) ⊗[R] (R ⧸ m) :=
    (1 : F.obj i) ⊗ₜ[R] (1 : R ⧸ m)
  by_contra hnon
  let S : CommAlgCat.{v, u} R := colimit F
  have hnon' : ¬ Nontrivial ((R ⧸ m) ⊗[R] (S : Type v)) := by
    simpa [S] using hnon
  have hs : Subsingleton ((R ⧸ m) ⊗[R] (S : Type v)) := by
    by_contra hns
    exact hnon' (not_subsingleton_iff_nontrivial.mp hns)
  letI : Subsingleton ((R ⧸ m) ⊗[R] (S : Type v)) := hs
  have hs' : Subsingleton ((S : Type v) ⊗[R] (R ⧸ m)) :=
    (TensorProduct.comm R (S : Type v) (R ⧸ m)).injective.subsingleton
  have htzero : LinearMap.rTensor (R ⧸ m) (colimit.ι F i).hom.toLinearMap t = 0 := by
    exact hs'.elim _ _
  obtain ⟨j, f, hfj⟩ :=
    (filteredColimit_tensorProduct_elementwise R F (R ⧸ m)).2 i t htzero
  obtain ⟨φ, hφ⟩ :=
    (filteredColimit_tensorProduct_ringHom R F (R ⧸ m)).2 i j f
  have hone : φ t = 1 := by
    rw [hφ]
    simp [t, Algebra.TensorProduct.one_def]
  have hntj : ¬ Subsingleton ((F.obj j : Type v) ⊗[R] (R ⧸ m)) := by
    intro h
    letI : Subsingleton ((F.obj j : Type v) ⊗[R] (R ⧸ m)) := h
    have hqj : Subsingleton ((R ⧸ m) ⊗[R] (F.obj j : Type v)) :=
      (TensorProduct.comm R (F.obj j : Type v) (R ⧸ m)).symm.injective.subsingleton
    exact (not_subsingleton_iff_nontrivial.mpr (hstage j)) hqj
  letI : Nontrivial ((F.obj j : Type v) ⊗[R] (R ⧸ m)) :=
    not_subsingleton_iff_nontrivial.mp hntj
  have hcontra : (1 : (F.obj j : Type v) ⊗[R] (R ⧸ m)) = 0 := by
    rw [← hone, hφ, hfj]
  exact one_ne_zero hcontra

end CommAlgCat
