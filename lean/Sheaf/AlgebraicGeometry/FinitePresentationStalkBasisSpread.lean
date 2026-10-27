/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.AlgebraicGeometry.FiniteFreeEpiIndependentGerms
import WeilConjectures.Topology.FiniteTypeLocalCoefficients
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Spreading a prescribed finite stalk basis

Source: Stacks Project, Modules, Tag 0B8J, lemma-finite-presentation-stalk-free,
statement and proof with the chosen basis retained.
(blueprint: lem-trf-finite-presentation-stalk-basis-spread)
-/

@[expose] public section

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private theorem finite_module_germ_representatives (X : RingedSpace.{u}) (F : Modules X)
    (x : X) {I : Type v} [Finite I] (s : I → (moduleStalkFunctor X x).obj F) :
    ∃ (U : Opens X) (hx : x ∈ U) (t : I → F.val.obj (op U)),
      ∀ i, TopCat.Presheaf.germ F.val.presheaf U x hx (t i) = s i := by
  classical
  let := Fintype.ofFinite I
  choose V hx t ht using fun i ↦ TopCat.Presheaf.exists_germ_eq F.val.presheaf (s i)
  let U : Opens X := ⨅ i, V i
  have hxU : x ∈ U := by
    change x ∈ (↑(⨅ i, V i) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  refine ⟨U, hxU, fun i ↦ F.val.map (homOfLE (iInf_le V i)).op (t i), ?_⟩
  intro i
  exact (TopCat.Presheaf.germ_res_apply F.val.presheaf
    (homOfLE (iInf_le V i)) x hxU (t i)).trans (ht i)

private theorem finite_ring_germ_representatives (X : RingedSpace.{u})
    (x : X) {I : Type v} [Finite I] (s : I → X.presheaf.stalk x) :
    ∃ (U : Opens X) (hx : x ∈ U) (t : I → (moduleRings X).obj.obj (op U)),
      ∀ i, X.presheaf.germ U x hx (t i) = s i := by
  classical
  let := Fintype.ofFinite I
  choose V hx t ht using fun i ↦ X.presheaf.exists_germ_eq (s i)
  let U : Opens X := ⨅ i, V i
  have hxU : x ∈ U := by
    change x ∈ (↑(⨅ i, V i) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  refine ⟨U, hxU, fun i ↦ X.presheaf.map (homOfLE (iInf_le V i)).op (t i), ?_⟩
  intro i
  exact (X.presheaf.germ_res_apply (homOfLE (iInf_le V i)) x hxU (t i)).trans (ht i)

private theorem finite_span_spreads (X : RingedSpace.{u}) (F : Modules X) (x : X)
    (r n : ℕ) (U V : Opens X) (hxU : x ∈ U) (hxV : x ∈ V)
    (t : Fin r → F.val.obj (op U)) (a : Fin n → F.val.obj (op V))
    (hspan : Submodule.span (X.presheaf.stalk x)
      (Set.range fun j ↦ TopCat.Presheaf.germ F.val.presheaf U x hxU (t j)) = ⊤) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V)
      (c : Fin n → Fin r → (moduleRings X).obj.obj (op W)),
      ∀ i, F.val.map (homOfLE hWV).op (a i) =
        ∑ j, c i j • F.val.map (homOfLE hWU).op (t j) := by
  classical
  have hmem (i : Fin n) : TopCat.Presheaf.germ F.val.presheaf V x hxV (a i) ∈
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun j ↦ TopCat.Presheaf.germ F.val.presheaf U x hxU (t j)) := by
    rw [hspan]
    trivial
  choose c hc using fun i ↦
    (Submodule.mem_span_range_iff_exists_fun (X.presheaf.stalk x)).mp (hmem i)
  obtain ⟨Z, hxZ, b, hb⟩ := finite_ring_germ_representatives X x
    (fun ij : Fin n × Fin r ↦ c ij.1 ij.2)
  let W : Opens X := U ⊓ V ⊓ Z
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxZ⟩
  have hWU : W ≤ U := inf_le_left.trans inf_le_left
  have hWV : W ≤ V := inf_le_left.trans inf_le_right
  have hWZ : W ≤ Z := inf_le_right
  let d (i : Fin n) (j : Fin r) := X.presheaf.map (homOfLE hWZ).op (b (i, j))
  let z (i : Fin n) : F.val.obj (op W) :=
    ∑ j, d i j • F.val.map (homOfLE hWU).op (t j)
  have heq (i : Fin n) : TopCat.Presheaf.germ F.val.presheaf W x hxW (z i) =
      TopCat.Presheaf.germ F.val.presheaf W x hxW (F.val.map (homOfLE hWV).op (a i)) := by
    dsimp only [z]
    rw [map_sum]
    change (∑ j, TopCat.Presheaf.germ F.val.presheaf W x hxW
      (d i j • F.val.map (homOfLE hWU).op (t j))) =
      TopCat.Presheaf.germ F.val.presheaf W x hxW (F.val.presheaf.map (homOfLE hWV).op (a i))
    simp_rw [PresheafOfModules.germ_smul (R := X.presheaf) F.val,
      TopCat.Presheaf.germ_res_apply F.val.presheaf]
    have hres (j : Fin r) : TopCat.Presheaf.germ F.val.presheaf W x hxW
        (F.val.map (homOfLE hWU).op (t j)) =
          TopCat.Presheaf.germ F.val.presheaf U x hxU (t j) :=
      TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hWU) x hxW (t j)
    simp_rw [hres]
    change (∑ j, X.presheaf.germ W x hxW
      (X.presheaf.map (homOfLE hWZ).op (b (i, j))) •
      TopCat.Presheaf.germ F.val.presheaf U x hxU (t j)) =
        TopCat.Presheaf.germ F.val.presheaf V x hxV (a i)
    simp_rw [X.presheaf.germ_res_apply, hb]
    exact hc i
  choose Y hxY i₁ i₂ hY using fun i ↦
    TopCat.Presheaf.germ_eq F.val.presheaf x hxW hxW (z i)
      (F.val.map (homOfLE hWV).op (a i)) (heq i)
  let W' : Opens X := W ⊓ ⨅ i, Y i
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
  have h := congrArg (F.val.presheaf.map (homOfLE (hWY i)).op) (hY i)
  change F.val.presheaf.map (homOfLE (hWY i)).op
      (F.val.presheaf.map (i₁ i).op (z i)) =
    F.val.presheaf.map (homOfLE (hWY i)).op
      (F.val.presheaf.map (i₂ i).op (F.val.presheaf.map (homOfLE hWV).op (a i))) at h
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


private theorem exists_epi_of_stalk_generators (X : RingedSpace.{u})
    (F : Modules X) [F.IsFiniteType] (x : X) (r : ℕ)
    (g : Fin r → (moduleStalkFunctor X x).obj F)
    (hg : Submodule.span (X.presheaf.stalk x) (Set.range g) = ⊤) :
    ∃ (U : Opens X) (hxU : x ∈ U) (t : Fin r → F.val.obj (op U))
      (p : SheafOfModules.free (R := (moduleRings X).over U)
        (ULift.{u} (Fin r)) ⟶ F.over U),
      (∀ j, TopCat.Presheaf.germ F.val.presheaf U x hxU (t j) = g j) ∧
      (∀ j, ((F.over U).freeHomEquiv p (ULift.up j)).val
        (op (Over.mk (𝟙 U))) = t j) ∧ Epi p := by
  classical
  obtain ⟨U, hxU, t, ht⟩ := finite_module_germ_representatives X F x g
  obtain ⟨V, hxV, n, a, ha⟩ :=
    RingedSpace.exists_finite_type_local_coefficients X F x
  have hspan : Submodule.span (X.presheaf.stalk x)
      (Set.range fun j ↦ TopCat.Presheaf.germ F.val.presheaf U x hxU (t j)) = ⊤ := by
    simpa only [ht] using hg
  obtain ⟨W, hxW, hWU, hWV, c, hc⟩ :=
    finite_span_spreads X F x r n U V hxU hxV t a hspan
  let s (j : ULift.{u} (Fin r)) : (F.over W).sections :=
    PresheafOfModules.sectionsMk
      (fun Z ↦ F.val.map (Z.unop.hom ≫ homOfLE hWU).op (t j.down))
      (by
        intro A B f
        change F.val.presheaf.map f.unop.left.op
            (F.val.presheaf.map (A.unop.hom ≫ homOfLE hWU).op (t j.down)) =
          F.val.presheaf.map (B.unop.hom ≫ homOfLE hWU).op (t j.down)
        rw [← Functor.map_comp_apply]
        congr 2)
  let R := (moduleRings X).over W
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
  refine ⟨W, hxW, fun j ↦ F.val.map (homOfLE hWU).op (t j), p, ?_, ?_, ?_⟩
  · intro j
    exact (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hWU) x hxW (t j)).trans (ht j)
  · intro j
    have h := congrArg (fun z ↦ (z (ULift.up j)).val (op Z₀))
      ((F.over W).freeHomEquiv.apply_symm_apply s)
    exact h
  · suffices Epi ((SheafOfModules.toSheaf R).map p) by
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
      apply congrArg (fun z : F.val.obj (op V') ↦
        (show (moduleRings X).obj.obj (op V') from b i) • z)
      change F.val.presheaf.map (j ≫ Z.hom).op
          (F.val.presheaf.map (homOfLE hWV).op (a i)) =
        F.val.presheaf.map (homOfLE (hV'.trans (Z.hom.le.trans hWV))).op (a i)
      rw [← Functor.map_comp_apply]
      rfl
    let := hsurj
    exact Sheaf.epi_of_isLocallySurjective _

/-- A prescribed finite basis of a finitely presented module stalk extends to sections
whose induced finite free map is an isomorphism on an open neighbourhood.
The last equality specifies the images of the standard free generators: a compatible
section on the slice site is evaluated at its terminal object `V → V`.

Source: Stacks Project, Modules, Tag 0B8J, lemma-finite-presentation-stalk-free,
statement and proof with the prescribed basis retained.
(blueprint: lem-trf-finite-presentation-stalk-basis-spread)

Proof:
1. Represent the finitely many basis germs by sections on one common neighbourhood U,
using def-weil-pbc-module-stalk. The induced free map sends the standard stalk basis
to the prescribed basis, hence is bijective on the stalk. Finite tuples of germs and
their equalities can be represented on common neighbourhoods. For rank zero use U = Y.
2. Finite presentation implies finite type and restricts to opens, directly from the
finite presentations in def-weil-pbc-module-finite-type-presentation.
3. Apply lem-weil-pbc-module-finite-type-surjective-on-stalk to shrink U so that the
free map is surjective as a sheaf map. Restricting the sections preserves their germs.
4. Apply lem-weil-pbc-finite-presentation-kernel-surjection-finite-type: the kernel K
of this finite free surjection onto the finitely presented restriction is finite type.
5. A kernel germ has finite coordinates a_i with sum (a_i)_y b_i = 0. Basis independence
makes every coordinate germ zero; shrinking finitely many times makes the section zero.
Thus K_y = 0, also for the empty tuple when the rank is zero.
6. Apply lem-weil-pbc-module-finite-type-surjective-on-stalk to 0 → K. After shrinking
again the kernel vanishes, so the free map is injective on sections. Its local preimages
glue uniquely, giving the inverse sheaf morphism, compatible with scalars and restrictions
as in def-weil-sheaf-of-modules-category. The final restricted sections retain their germs.
For rank zero this is an isomorphism from the zero sheaf to the restriction of G. -/
theorem exists_free_neighbourhood_prescribed_stalk_basis
    (Y : RingedSpace.{u}) (G : ringedSiteModules (moduleRings Y))
    [G.IsFinitePresentation] (y : Y) (r : ℕ)
    (b : Module.Basis (Fin r) (Y.presheaf.stalk y) ((moduleStalkFunctor Y y).obj G)) :
    ∃ (V : Opens Y) (hyV : y ∈ V) (t : Fin r → G.val.obj (op V))
      (ψ : SheafOfModules.free (R := (moduleRings Y).over V) (ULift.{u} (Fin r)) ⟶
        G.over V),
      (∀ i : Fin r, TopCat.Presheaf.germ G.val.presheaf V y hyV (t i) = b i) ∧
      IsIso ψ ∧
      ∀ i : Fin r,
        ((G.over V).freeHomEquiv ψ (ULift.up i)).val (op (Over.mk (𝟙 V))) = t i := by
  classical
  obtain ⟨U, hyU, t, p, ht, hp, hpepi⟩ :=
    exists_epi_of_stalk_generators Y G y r b b.span_eq
  let := hpepi
  have hind : LinearIndependent (Y.presheaf.stalk y) (fun j : Fin r ↦
      TopCat.Presheaf.germ G.val.presheaf U y hyU
        (((G.over U).freeHomEquiv p (ULift.up j)).val (op (Over.mk (𝟙 U))))) := by
    simpa only [hp, ht] using b.linearIndependent
  obtain ⟨V, hVU, hyV, hinj⟩ :=
    exists_injective_neighbourhood_of_independent_free_epi Y G U y hyU r p hind
  let i : V ⟶ U := homOfLE hVU
  let H := SheafOfModules.overMap (moduleRings Y) i
  let e := SheafOfModules.mapFreeIso H (ULift.{u} (Fin r))
    (SheafOfModules.overMapUnitIso i).symm
  let c := (SheafOfModules.overFunctorMap (moduleRings Y) i).app G
  let q := e.hom ≫ H.map p ≫ c.hom
  have hm : Mono (H.map p) := by
    constructor
    intro N f g hfg
    ext W z
    apply hinj W.unop.left W.unop.hom.le
    exact congrArg (fun k ↦ k.val.app W z) hfg
  let := hm
  have hq : IsIso q := by
    dsimp only [q]
    exact isIso_of_mono_of_epi _
  have hres (j : Fin r) :
      ((G.over V).freeHomEquiv q (ULift.up j)).val (op (Over.mk (𝟙 V))) =
        G.val.map i.op (t j) := by
    change ((G.over V).unitHomEquiv (SheafOfModules.ιFree (ULift.up j) ≫ q)).val
      (op (Over.mk (𝟙 V))) = _
    dsimp only [q]
    rw [← Category.assoc, ← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom,
      Category.assoc, Category.assoc]
    rw [← Category.assoc (H.map (SheafOfModules.ιFree (ULift.up j))) (H.map p) c.hom,
      ← Functor.map_comp]
    change (((G.over U).freeHomEquiv p (ULift.up j)).val
      (op (Over.mk (𝟙 V ≫ i)))) = _
    have hs := PresheafOfModules.sections_property
      ((G.over U).freeHomEquiv p (ULift.up j))
      (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op
    change G.val.map i.op _ = _ at hs
    rw [hp] at hs
    exact hs.symm
  refine ⟨V, hyV, fun j ↦ G.val.map i.op (t j), q, ?_, hq, hres⟩
  intro j
  exact (TopCat.Presheaf.germ_res_apply G.val.presheaf i y hyV (t j)).trans (ht j)

end AlgebraicGeometry.RingedSpace
