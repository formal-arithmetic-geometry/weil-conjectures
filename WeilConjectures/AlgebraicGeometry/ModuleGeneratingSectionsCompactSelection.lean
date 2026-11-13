/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.AlgebraicGeometry.ModuleGeneratingSectionsLocalSelection
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Selecting generators on a compact open

## References

* [Stacks, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem epi_overMap_iff_local_lifts
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    {F G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)} (φ : F ⟶ G) :
    Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map φ) ↔
      ∀ (W : X.Opens) (hWK : W ≤ K)
        (t : G.val.obj (.op (Over.mk (homOfLE (hWK.trans hKV)))))
        (x : X), x ∈ W →
        ∃ (Z : X.Opens) (hZW : Z ≤ W), x ∈ Z ∧
          ∃ s : F.val.obj (.op (Over.mk (homOfLE (hZW.trans (hWK.trans hKV))))),
            φ.val.app _ s = G.val.map
              (Over.homMk (homOfLE hZW)).op t := by
  let T := SheafOfModules.toSheaf.{u} ((moduleRings X.toRingedSpace).over K)
  let ψ := (overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map φ
  rw [← T.epi_map_iff_epi ψ, ← CategoryTheory.Sheaf.isLocallySurjective_iff_epi']
  constructor
  · intro h W hWK t x hx
    have hh := CategoryTheory.Presheaf.imageSieve_mem
      ((Opens.grothendieckTopology X).over K) (T.map ψ).hom
      (U := .op (Over.mk (homOfLE hWK))) t
    change Sieve.overEquiv (Over.mk (homOfLE hWK)) _ ∈
      Opens.grothendieckTopology X W at hh
    obtain ⟨Z, f, hf, hxZ⟩ := hh x hx
    rw [Sieve.overEquiv_iff] at hf
    exact ⟨Z, leOfHom f, hxZ, hf⟩
  · intro h
    constructor
    intro W t
    change Sieve.overEquiv W _ ∈ Opens.grothendieckTopology X W.left
    intro x hx
    obtain ⟨Z, hZW, hxZ, s, hs⟩ := h W.left (leOfHom W.hom) t x hx
    refine ⟨Z, homOfLE hZW, ?_, hxZ⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨s, hs⟩

-- Elaborating free coproduct maps across slice restriction needs additional steps.
set_option backward.isDefEq.respectTransparency false in
private theorem freeMap_subset_epi
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (σ : (H.over V).GeneratingSections) (S T : Finset σ.I) (hST : S ⊆ T)
    (hS : Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).map
      (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → σ.I) ≫ σ.π))) :
    Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).map
      (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : T → σ.I) ≫ σ.π)) := by
  let f : S → T := fun i ↦ ⟨i.val, hST i.property⟩
  have hf : freeMap (R := (moduleRings X.toRingedSpace).over V) f ≫
      freeMap ((↑) : T → σ.I) = freeMap ((↑) : S → σ.I) := by
    apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext (isColimitFreeCofan S)
    intro i
    simp [f]
  let F := overMap (moduleRings X.toRingedSpace) (homOfLE hUV)
  have hfac : F.map (freeMap f) ≫ F.map (freeMap ((↑) : T → σ.I) ≫ σ.π) =
      F.map (freeMap ((↑) : S → σ.I) ≫ σ.π) := by
    rw [← F.map_comp, ← Category.assoc, hf]
  have := hS
  exact epi_of_epi_fac hfac

set_option maxHeartbeats 500000 in
-- The slice-site section types require additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- A specified global generating family has a finite subfamily generating on a
compact open where the module is of finite type. No affineness or quasi-coherence
is assumed (Stacks, Tag 01BB). -/
theorem exists_finset_generatingSections_on_compact
    (X : Scheme.{u}) (V K : X.Opens) (hK : IsCompact (K : Set X)) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType] (σ : (H.over V).GeneratingSections) :
    ∃ S : Finset σ.I,
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map
        (SheafOfModules.freeMap (R := (moduleRings X.toRingedSpace).over V)
          ((↑) : S → σ.I) ≫ σ.π)) := by
  classical
  choose U hUK hx S hS using exists_finset_generatingSections_near_point X V K hKV H σ
  have hcover : (K : Set X) ⊆ ⋃ x : K, (U x : Set X) := by
    intro x hxK
    exact Set.mem_iUnion.mpr ⟨⟨x, hxK⟩, hx ⟨x, hxK⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) hcover
  let T : Finset σ.I := t.biUnion S
  refine ⟨T, (epi_overMap_iff_local_lifts X V K hKV _).mpr ?_⟩
  intro W hWK a x hxW
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (ht (hWK hxW))
  obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
  have hST : S i ⊆ T := fun j hj ↦ Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
  have he := freeMap_subset_epi X V (U i) ((hUK i).trans hKV) H σ (S i) T hST (hS i)
  let Q := W ⊓ U i
  have hQV : Q ≤ V := inf_le_left.trans (hWK.trans hKV)
  let b : (H.over V).val.obj (.op (Over.mk (homOfLE hQV))) :=
    (H.over V).val.map (Over.homMk (homOfLE (show Q ≤ W from inf_le_left))).op a
  obtain ⟨Z, hZQ, hxZ, z, hz⟩ :=
    (epi_overMap_iff_local_lifts X V (U i) ((hUK i).trans hKV) _).mp he
      Q inf_le_right b x ⟨hxW, hxi⟩
  refine ⟨Z, hZQ.trans inf_le_left, hxZ, z, ?_⟩
  change _ = (H.over V).val.presheaf.map (Over.homMk (homOfLE hZQ)).op
    ((H.over V).val.presheaf.map
      (Over.homMk (homOfLE (show Q ≤ W from inf_le_left))).op a) at hz
  change _ = (H.over V).val.presheaf.map
    (Over.homMk (homOfLE (hZQ.trans inf_le_left))).op a
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← Over.homMk_comp, homOfLE_comp] using hz

end AlgebraicGeometry.Scheme.Modules
