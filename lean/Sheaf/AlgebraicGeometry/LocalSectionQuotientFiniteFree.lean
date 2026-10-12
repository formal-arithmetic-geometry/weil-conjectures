module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-!
# Local sections of finite locally free quotients

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-sc-riemann-roch.md, Proof of (*), determinant paragraph: local splitting
(blueprint: lem-sc-local-section-quotient-finite-free)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Opposite TopologicalSpace SheafOfModules

private theorem section_transport {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (η : F ≅ G) {M N : C} (φ : M ⟶ N)
    (s : F.obj N ⟶ F.obj M) (hs : s ≫ F.map φ = 𝟙 _) :
    (η.inv.app N ≫ s ≫ η.hom.app M) ≫ G.map φ = 𝟙 _ := by
  rw [Category.assoc, Category.assoc, ← η.hom.naturality φ,
    ← Category.assoc s, hs, Category.id_comp, η.inv_hom_id_app]

set_option backward.isDefEq.respectTransparency false in
private theorem finite_free_lift {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) [Epi φ] (V : X.Opens) (x : X) (hx : x ∈ V)
    (I : Type u) [Finite I] (α : free (R := X.ringCatSheaf.over V) I ⟶ N.over V) :
    ∃ (U : X.Opens) (hUV : U ≤ V), x ∈ U ∧
      ∃ β : (overMap.{u} X.ringCatSheaf (homOfLE hUV)).obj
          (free (R := X.ringCatSheaf.over V) I) ⟶ M.over U,
        β ≫ φ.over U =
          (overMap.{u} X.ringCatSheaf (homOfLE hUV)).map α ≫
            (overFunctorMap.{u} X.ringCatSheaf (homOfLE hUV)).hom.app N := by
  classical
  let t (i : I) : N.val.obj (op V) :=
    ((N.over V).freeHomEquiv α i).val (op (Over.mk (𝟙 V)))
  have hlift (i : I) : ∃ (W : X.Opens) (hWV : W ≤ V) (b : M.val.obj (op W)),
      x ∈ W ∧ φ.val.app (op W) b = N.val.map (homOfLE hWV).op (t i) := by
    have hl := ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1
      M N φ).2.mpr inferInstance V (t i)
    obtain ⟨J, W, hWV, b, hc, hb⟩ := hl
    have hx' : x ∈ ⨆ j, W j := by rw [hc]; exact hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx'
    exact ⟨W j, hWV j, b j, hj, hb j⟩
  choose W hWV b hxW hb using hlift
  let U : X.Opens := V ⊓ ⨅ i, W i
  have hUV : U ≤ V := inf_le_left
  have hUW (i : I) : U ≤ W i := inf_le_right.trans (iInf_le W i)
  have hxU : x ∈ U := by
    refine ⟨hx, ?_⟩
    simpa only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter] using hxW
  let bU (i : I) : M.val.obj (op U) := M.val.map (homOfLE (hUW i)).op (b i)
  have hbU (i : I) : φ.val.app (op U) (bU i) =
      N.val.map (homOfLE hUV).op (t i) := by
    rw [PresheafOfModules.naturality_apply, hb i]
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  let bs (i : I) : (M.over U).sections := (M.over U).val.sectionsMk
    (fun A ↦ M.val.map A.unop.hom.op (bU i)) (by
      intro A B f
      change M.val.map f.unop.left.op (M.val.map A.unop.hom.op (bU i)) = _
      rw [← PresheafOfModules.map_comp_apply]
      rfl)
  let F := overMap.{u} X.ringCatSheaf (homOfLE hUV)
  let e := mapFreeIso F I (overMapUnitIso (R := X.ringCatSheaf) (homOfLE hUV)).symm
  let δ : free (R := X.ringCatSheaf.over U) I ⟶ M.over U :=
    (M.over U).freeHomEquiv.symm bs
  have hδ : δ ≫ φ.over U =
      e.hom ≫ F.map α ≫ (overFunctorMap.{u} X.ringCatSheaf (homOfLE hUV)).hom.app N := by
    apply (N.over U).freeHomEquiv.injective
    funext i
    apply PresheafOfModules.sections_ext
    intro A
    simp only [freeHomEquiv_comp_apply, δ, Equiv.apply_symm_apply]
    change φ.val.app (op A.unop.left) (M.val.map A.unop.hom.op (bU i)) = _
    rw [PresheafOfModules.naturality_apply, hbU i]
    change _ = ((N.over U).unitHomEquiv
      (ιFree i ≫ e.hom ≫ F.map α ≫
        (overFunctorMap.{u} X.ringCatSheaf (homOfLE hUV)).hom.app N)).val A
    rw [ιFree_mapFreeIso_hom_assoc]
    rw [← F.map_comp_assoc]
    change _ = ((N.over V).freeHomEquiv α i).val
      (op (Over.mk (A.unop.hom ≫ homOfLE hUV)))
    rw [← PresheafOfModules.map_comp_apply]
    let A' : Over V := Over.mk (A.unop.hom ≫ homOfLE hUV)
    let k : A' ⟶ Over.mk (𝟙 V) := Over.homMk A'.hom
    exact ((N.over V).freeHomEquiv α i).property k.op
  refine ⟨U, hUV, hxU, e.inv ≫ δ, ?_⟩
  rw [Category.assoc, hδ, ← Category.assoc, e.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A finite locally free quotient of a short exact sequence admits local sections.

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-sc-riemann-roch.md, Proof of (*), determinant paragraph: local splitting.
The proof fixes a point, trivializes the finite locally free quotient, lifts finitely many
basis sections locally using local surjectivity of an epimorphism of sheaves, intersects the
resulting finitely many neighbourhoods, and defines the section by the lifted basis. The
rank-zero case uses the zero section.
(blueprint: lem-sc-local-section-quotient-finite-free)
-/
-- The original signature reversed the section equation; see the change record.
theorem exists_local_section_of_shortExact_finiteLocallyFree
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {d : ℕ} (hE₃ : S.X₃.IsFiniteLocallyFreeOfRank d) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj S.X₃ ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj S.X₂,
        s ≫ (Scheme.Modules.restrictFunctor U.ι).map S.g = 𝟙 _ := by
  classical
  let : Epi S.g := hS.epi_g
  obtain ⟨q, hq, hr⟩ := hE₃.exists_localGeneratorsData
  let := hq
  intro x
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  let V := q.X i
  let G := q.generators i
  let : Finite G.I := Finite.of_equiv _ (hr i).some.symm
  obtain ⟨U, hUV, hxU, β, hβ⟩ := finite_free_lift S.g V x hi G.I G.π
  let F := overMap.{u} X.ringCatSheaf (homOfLE hUV)
  let e : F.obj (free (R := X.ringCatSheaf.over V) G.I) ≅ S.X₃.over U :=
    F.mapIso (asIso G.π) ≪≫ (overFunctorMap.{u} X.ringCatSheaf (homOfLE hUV)).app S.X₃
  have hsec : (e.inv ≫ β) ≫ S.g.over U = 𝟙 _ := by
    calc
      (e.inv ≫ β) ≫ S.g.over U = e.inv ≫ (β ≫ S.g.over U) := Category.assoc _ _ _
      _ = e.inv ≫ e.hom := congrArg (fun k ↦ e.inv ≫ k) hβ
      _ = 𝟙 _ := e.inv_hom_id
  let T := (Scheme.Modules.overEquiv U).functor
  let η := Scheme.Modules.overFunctorEquiv U
  refine ⟨U, hxU, η.inv.app S.X₃ ≫ T.map (e.inv ≫ β) ≫ η.hom.app S.X₂, ?_⟩
  apply section_transport η S.g
  exact (T.map_comp (e.inv ≫ β) (S.g.over U)).symm.trans
    ((congrArg T.map hsec).trans (T.map_id _))

end AlgebraicGeometry
