/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.Topology.FiniteTypeLocalCoefficients
import WeilConjectures.AlgebraicGeometry.LocalModuleEpiGermLift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# A prescribed bound on generators near a point

Source: Stacks Project, Modules, Tag 01B8, lemma-finite-type-surjective-on-stalk.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem finite_module_germ_representatives (X : Scheme.{u}) (F : X.Modules)
    (x : X) {I : Type v} [Finite I] (s : I → F.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (t : I → Γ(F, U)),
      ∀ i, F.presheaf.germ U x hx (t i) = s i := by
  classical
  let := Fintype.ofFinite I
  choose V hx t ht using fun i ↦ F.presheaf.exists_germ_eq (s i)
  let U : X.Opens := ⨅ i, V i
  have hxU : x ∈ U := by
    change x ∈ (↑(⨅ i, V i) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  refine ⟨U, hxU, fun i ↦ F.val.map (homOfLE (iInf_le V i)).op (t i), ?_⟩
  intro i
  exact (F.presheaf.germ_res_apply (homOfLE (iInf_le V i)) x hxU (t i)).trans (ht i)

private theorem finite_ring_germ_representatives (X : Scheme.{u})
    (x : X) {I : Type v} [Finite I] (s : I → X.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (t : I → Γ(X, U)),
      ∀ i, X.presheaf.germ U x hx (t i) = s i := by
  classical
  let := Fintype.ofFinite I
  choose V hx t ht using fun i ↦ X.presheaf.exists_germ_eq (s i)
  let U : X.Opens := ⨅ i, V i
  have hxU : x ∈ U := by
    change x ∈ (↑(⨅ i, V i) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  refine ⟨U, hxU, fun i ↦ X.presheaf.map (homOfLE (iInf_le V i)).op (t i), ?_⟩
  intro i
  exact (X.presheaf.germ_res_apply (homOfLE (iInf_le V i)) x hxU (t i)).trans (ht i)

private theorem finite_span_spreads (X : Scheme.{u}) (F : X.Modules) (x : X)
    (r n : ℕ) (U V : X.Opens) (hxU : x ∈ U) (hxV : x ∈ V)
    (t : Fin r → Γ(F, U)) (a : Fin n → Γ(F, V))
    (hspan : Submodule.span (X.presheaf.stalk x)
      (Set.range fun j ↦ F.presheaf.germ U x hxU (t j)) = ⊤) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V)
      (c : Fin n → Fin r → Γ(X, W)),
      ∀ i, F.val.map (homOfLE hWV).op (a i) =
        ∑ j, c i j • F.val.map (homOfLE hWU).op (t j) := by
  classical
  have hmem (i : Fin n) : F.presheaf.germ V x hxV (a i) ∈
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun j ↦ F.presheaf.germ U x hxU (t j)) := by
    rw [hspan]
    trivial
  choose c hc using fun i ↦
    (Submodule.mem_span_range_iff_exists_fun (X.presheaf.stalk x)).mp (hmem i)
  obtain ⟨Z, hxZ, b, hb⟩ := finite_ring_germ_representatives X x
    (fun ij : Fin n × Fin r ↦ c ij.1 ij.2)
  let W : X.Opens := U ⊓ V ⊓ Z
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxZ⟩
  have hWU : W ≤ U := inf_le_left.trans inf_le_left
  have hWV : W ≤ V := inf_le_left.trans inf_le_right
  have hWZ : W ≤ Z := inf_le_right
  let d (i : Fin n) (j : Fin r) := X.presheaf.map (homOfLE hWZ).op (b (i, j))
  let z (i : Fin n) : Γ(F, W) :=
    ∑ j, d i j • F.val.map (homOfLE hWU).op (t j)
  have heq (i : Fin n) : F.presheaf.germ W x hxW (z i) =
      F.presheaf.germ W x hxW (F.val.map (homOfLE hWV).op (a i)) := by
    dsimp only [z]
    rw [map_sum]
    change (∑ j, F.presheaf.germ W x hxW
      (d i j • F.presheaf.map (homOfLE hWU).op (t j))) =
      F.presheaf.germ W x hxW (F.presheaf.map (homOfLE hWV).op (a i))
    simp_rw [germ_smul, F.presheaf.germ_res_apply]
    change (∑ j, X.presheaf.germ W x hxW
      (X.presheaf.map (homOfLE hWZ).op (b (i, j))) •
      F.presheaf.germ U x hxU (t j)) = F.presheaf.germ V x hxV (a i)
    simp_rw [X.presheaf.germ_res_apply, hb]
    exact hc i
  choose Y hxY i₁ i₂ hY using fun i ↦
    F.presheaf.germ_eq x hxW hxW (z i)
      (F.val.map (homOfLE hWV).op (a i)) (heq i)
  let W' : X.Opens := W ⊓ ⨅ i, Y i
  have hxW' : x ∈ W' := by
    refine ⟨hxW, ?_⟩
    change x ∈ (↑(⨅ i, Y i) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxY
  have hWW : W' ≤ W := inf_le_left
  have hWY (i : Fin n) : W' ≤ Y i := inf_le_right.trans (iInf_le Y i)
  refine ⟨W', hxW', hWW.trans hWU, hWW.trans hWV,
    fun i j ↦ X.presheaf.map (homOfLE hWW).op (d i j), ?_⟩
  intro i
  have h := congrArg (F.presheaf.map (homOfLE (hWY i)).op) (hY i)
  change F.presheaf.map (homOfLE (hWY i)).op
      (F.presheaf.map (i₁ i).op (z i)) =
    F.presheaf.map (homOfLE (hWY i)).op
      (F.presheaf.map (i₂ i).op (F.presheaf.map (homOfLE hWV).op (a i))) at h
  simp only [← Functor.map_comp_apply] at h
  have hz : F.val.map (homOfLE hWW).op (z i) =
      F.val.map (homOfLE (hWW.trans hWV)).op (a i) := by
    exact h
  rw [← hz]
  dsimp only [z]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [F.val.map_smul, ← PresheafOfModules.map_comp_apply]
  rfl

private theorem freeHom_basis_apply
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) {I : Type u} (s : I → M.sections)
    (i : I) (V : Cᵒᵖ) (a : R.obj.obj V) :
    (M.freeHomEquiv.symm s).val.app V ((SheafOfModules.ιFree i).val.app V a) =
      a • (show M.val.obj V from (s i).val V) := by
  have h : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s =
      M.unitHomEquiv.symm (s i) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  change (SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s).val.app V a = _
  rw [h]
  have hs : (M.unitHomEquiv.symm (s i)).val.app V (1 : R.obj.obj V) =
      (s i).val V := congrArg (fun t : M.sections ↦ t.val V)
        (M.unitHomEquiv.apply_symm_apply (s i))
  have hlin := ((M.unitHomEquiv.symm (s i)).val.app V).hom.map_smul a
    (1 : R.obj.obj V)
  simpa only [smul_eq_mul, mul_one, hs] using hlin

private theorem neighbourhood_germs_span (X : Scheme.{u}) (F : X.Modules)
    (x : X) (r : ℕ) (U : X.Opens) (hx : x ∈ U)
    (s : ULift.{u} (Fin r) → (F.over U).sections)
    [Epi ((F.over U).freeHomEquiv.symm s)] :
    ∃ t : Fin r → (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
      Submodule.span (X.presheaf.stalk x) (Set.range t) = ⊤ := by
  classical
  let Z : Over U := Over.mk (𝟙 U)
  let t (i : Fin r) := F.presheaf.germ U x hx ((s ⟨i⟩).val (op Z))
  refine ⟨t, top_unique ?_⟩
  intro z _
  obtain ⟨V, hVU, hxV, a, ha⟩ := F.presheaf.exists_le_germ_eq z hx
  let p := (F.over U).freeHomEquiv.symm s
  obtain ⟨W, hxW, j, b, hb⟩ := RingedSpace.exists_local_module_epi_germ_lift
    X.toRingedSpace F x U (SheafOfModules.free (ULift.{u} (Fin r))) p
      V (homOfLE hVU) hxV a
  let V' : (Over U)ᵒᵖ := op (Over.mk (j ≫ homOfLE hVU))
  have heq : b = ∑ i : ULift.{u} (Fin r),
      (SheafOfModules.ιFree i).val.app V' ((SheafOfModules.freeπ i).val.app V' b) :=
    ((SheafOfModules.freeSectionsLinearEquiv (R := X.ringCatSheaf.over U)
      (ULift.{u} (Fin r)) V').symm_apply_apply b).symm
  change F.presheaf.germ W x hxW (p.val.app V' b) =
    F.presheaf.germ V x hxV a at hb
  rw [← ha, ← hb, heq, map_sum, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [freeHom_basis_apply]
  erw [PresheafOfModules.germ_smul (R := X.presheaf) F.val]
  apply Submodule.smul_mem
  have hres : (s i).val V' =
      F.val.map (j ≫ homOfLE hVU).op ((s i).val (op Z)) := by
    let k : V'.unop ⟶ Z := Over.homMk (j ≫ homOfLE hVU) (by simp [Z, V'])
    exact (PresheafOfModules.sections_property (s i) k.op).symm
  rw [hres]
  change F.presheaf.germ W x hxW
    (F.presheaf.map (j ≫ homOfLE hVU).op ((s i).val (op Z))) ∈ _
  rw [F.presheaf.germ_res_apply]
  exact Submodule.subset_span ⟨i.down, rfl⟩

/-- For a finite type module sheaf, a bound on the number of generators of one stalk
holds on some neighbourhood. No quasi-coherence or finite presentation is required.
Source: Stacks Project, Modules, Tag 01B8, lemma-finite-type-surjective-on-stalk,
together with the representation of germs by sections.
(blueprint: lem-trf-finite-stalk-generators-neighbourhood)

Proof: Represent the finitely many stalk generators on a common open U. Their germs
span the stalk, so the morphism from the free sheaf on these sections is surjective
at that stalk. Shrink U by 01B8 to make this morphism an epimorphism. In detail,
choose finitely many local generators of F from finite type, express their germs
as linear combinations of the prescribed germs, represent the finitely many
coefficients, and shrink until these finitely many equalities hold as sections.
The prescribed sections then generate because the original local generators do.
Conversely an epimorphism from a finite free sheaf is surjective on stalks. The
images of the finitely many basis germs therefore span the target stalk. Reindex
ULift (Fin r) by Fin r. For r = 0 the same argument says the stalk, and then the
sheaf on a neighbourhood, is zero. There is no point to check on an empty scheme. -/
theorem finite_stalk_generators_iff_neighbourhood (X : Scheme.{u}) (F : X.Modules)
    [F.IsFiniteType] (x : X) (r : ℕ) :
    (∃ s : Fin r → (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
      Submodule.span (X.presheaf.stalk x) (Set.range s) = ⊤) ↔
    ∃ U : X.Opens, x ∈ U ∧
      ∃ s : ULift.{u} (Fin r) → (F.over U).sections,
        Epi ((F.over U).freeHomEquiv.symm s) := by
  classical
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨U, hxU, t, ht⟩ := finite_module_germ_representatives X F x g
    obtain ⟨V, hxV, n, a, ha⟩ :=
      RingedSpace.exists_finite_type_local_coefficients X.toRingedSpace F x
    have hspan : Submodule.span (X.presheaf.stalk x)
        (Set.range fun j ↦ F.presheaf.germ U x hxU (t j)) = ⊤ := by
      simpa only [ht] using hg
    obtain ⟨W, hxW, hWU, hWV, c, hc⟩ :=
      finite_span_spreads X F x r n U V hxU hxV t a hspan
    let s (j : ULift.{u} (Fin r)) : (F.over W).sections :=
      PresheafOfModules.sectionsMk
        (fun Z ↦ F.val.map (Z.unop.hom ≫ homOfLE hWU).op (t j.down))
        (by
          intro A B f
          change F.presheaf.map f.unop.left.op
              (F.presheaf.map (A.unop.hom ≫ homOfLE hWU).op (t j.down)) =
            F.presheaf.map (B.unop.hom ≫ homOfLE hWU).op (t j.down)
          rw [← Functor.map_comp_apply]
          congr 2)
    let R := X.ringCatSheaf.over W
    let G := SheafOfModules.free (R := R) (ULift.{u} (Fin r))
    let p : G ⟶ F.over W := (F.over W).freeHomEquiv.symm s
    let Z₀ : Over W := Over.mk (𝟙 W)
    let l (i : Fin n) : G.val.obj (op Z₀) :=
      ∑ j : Fin r, (SheafOfModules.ιFree (⟨j⟩ : ULift.{u} (Fin r))).val.app
        (op Z₀) (c i j)
    have hl (i : Fin n) : p.val.app (op Z₀) (l i) =
        F.val.map (homOfLE hWV).op (a i) := by
      dsimp only [l]
      rw [map_sum]
      change (∑ j : Fin r, ((F.over W).freeHomEquiv.symm s).val.app (op Z₀)
        ((SheafOfModules.ιFree (⟨j⟩ : ULift.{u} (Fin r))).val.app (op Z₀) (c i j))) = _
      simp_rw [freeHom_basis_apply]
      exact (hc i).symm
    refine ⟨W, hxW, s, ?_⟩
    suffices Epi ((SheafOfModules.toSheaf R).map p) by
      let := this
      constructor
      intro N f g hfg
      apply (SheafOfModules.toSheaf R).map_injective
      apply (cancel_epi ((SheafOfModules.toSheaf R).map p)).mp
      simpa only [← Functor.map_comp] using
        congrArg (fun q ↦ (SheafOfModules.toSheaf R).map q) hfg
    have hsurj : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p) := by
      constructor
      intro Z z
      rw [GrothendieckTopology.mem_over_iff]
      intro y hy
      obtain ⟨V', hV', hyV', b, hb⟩ :=
        ha Z.left (Z.hom.le.trans hWV) z y hy
      let j : V' ⟶ Z.left := homOfLE hV'
      let k : Over.mk (j ≫ Z.hom) ⟶ Z₀ := Over.homMk (j ≫ Z.hom) (by simp [Z₀])
      refine ⟨V', j, (Sieve.overEquiv_iff _ j).mpr ?_, hyV'⟩
      refine ⟨∑ i, b i • G.val.map k.op (l i), ?_⟩
      change (p.val.app (op (Over.mk (j ≫ Z.hom)))).hom
          (∑ i : Fin n, b i • (G.val.map k.op).hom (l i)) = (F.val.map j.op).hom z
      rw [hb]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.map_smul, PresheafOfModules.naturality_apply, hl]
      apply congrArg (fun z : Γ(F, V') ↦ (show Γ(X, V') from b i) • z)
      change F.presheaf.map (j ≫ Z.hom).op
          (F.presheaf.map (homOfLE hWV).op (a i)) =
        F.presheaf.map (homOfLE (hV'.trans (Z.hom.le.trans hWV))).op (a i)
      rw [← Functor.map_comp_apply]
      rfl
    let := hsurj
    exact Sheaf.epi_of_isLocallySurjective _
  · rintro ⟨U, hxU, s, hs⟩
    let := hs
    exact neighbourhood_germs_span X F x r U hxU s

end AlgebraicGeometry.Scheme.Modules
