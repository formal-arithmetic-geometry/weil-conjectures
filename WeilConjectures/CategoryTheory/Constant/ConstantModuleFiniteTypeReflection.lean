/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Constant module sheaves reflect finite generation

Source: Stacks Project, Modules on Sites, Tag 093N, assertion (1)
(blueprint: lem-sfb-constant-module-finite-type-reflection).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

private abbrev cmod {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B) :=
  (siteConstantModuleFunctorGeneral J B).obj M

private abbrev cunit {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    : (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat B) AddCommGrpCat).obj M) ⟶
      (cmod J B M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafGeneral (C := C) B).obj M).presheaf

private lemma cunit_restrict {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    {U V : C} (f : V ⟶ U) (m : M) :
    (cmod J B M).val.map f.op ((cunit J B M).app (op U) m) =
      (cunit J B M).app (op V) m := by
  exact (NatTrans.naturality_apply (cunit J B M) f.op m).symm

private lemma cunit_smul {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    (U : C) (b : B) (m : M) :
    (cunit J B M).app (op U) (b • m) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app (op U) b •
        (show (cmod J B M).val.obj (op U) from (cunit J B M).app (op U) m) := by
  exact (((PresheafOfModules.sheafificationAdjunction
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)))).unit.app
      ((siteConstantModulePresheafGeneral (C := C) B).obj M)).app (op U)).hom.map_smul b m

private lemma cunit_map {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] {M N : ModuleCat.{max u v} B}
    (p : M ⟶ N) (U : C) (m : M) :
    ((siteConstantModuleFunctorGeneral J B).map p).val.app (op U)
        ((cunit J B M).app (op U) m) =
      (cunit J B N).app (op U) (p m) := by
  exact (ConcreteCategory.congr_hom (congr_app (toSheafify_naturality J
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := C) B).map p))) (op U)) m).symm

private lemma exists_nondegenerate {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (h : ¬ Nonempty ((⊥_ (Sheaf J (Type (max u v)))) ≅
      (⊤_ (Sheaf J (Type (max u v)))))) : ∃ U, (⊥ : Sieve U) ∉ J U := by
  by_contra! hbot
  have ht : J = ⊤ := by
    apply le_antisymm le_top
    intro U S _
    exact J.superset_covering bot_le (hbot U)
  exact h ⟨(Sheaf.isTerminalOfEqTop ht _).uniqueUpToIso (terminalIsTerminal)⟩

private lemma cover_nondegenerate {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C} (hU : (⊥ : Sieve U) ∉ J U)
    (S : Sieve U) (hS : S ∈ J U) :
    ∃ (V : C) (f : V ⟶ U), S f ∧ (⊥ : Sieve V) ∉ J V := by
  by_contra! h
  apply hU
  exact J.transitive hS ⊥ (fun V f hf ↦ by simpa using h V f hf)

private lemma local_span
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{max u v}} (F : SheafOfModules.{max u v} R)
    (σ : F.GeneratingSections) [Fintype σ.I] (U : D) (s : F.val.obj (op U)) :
    ∃ S ∈ J U, ∀ (V : D) (a : V ⟶ U), S a →
      ∃ c : σ.I → R.obj.obj (op V),
        F.val.map a.op s = ∑ i, c i •
          (show F.val.obj (op V) from (σ.s i).val (op V)) := by
  classical
  let φ := (SheafOfModules.toSheaf R).map σ.π
  have : Epi φ := inferInstance
  have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' _ φ).2
    inferInstance
  have : Presheaf.IsLocallySurjective J φ.hom := inferInstance
  refine ⟨Presheaf.imageSieve φ.hom s, Presheaf.imageSieve_mem J φ.hom s, ?_⟩
  intro V a ha
  obtain ⟨x, hx⟩ := ha
  change σ.π.val.app (op V) x = F.val.map a.op s at hx
  let c := SheafOfModules.freeSectionsLinearEquiv (R := R) σ.I (op V) x
  refine ⟨c, ?_⟩
  have hd := (SheafOfModules.freeSectionsLinearEquiv (R := R) σ.I (op V)).left_inv x
  change (∑ i, (SheafOfModules.ιFree (R := R) i).val.app (op V) (c i)) = x at hd
  rw [← hx, ← hd, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (SheafOfModules.ιFree i ≫ σ.π).val.app (op V) (c i) = _
  have hi : SheafOfModules.ιFree i ≫ σ.π = F.unitHomEquiv.symm (σ.s i) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    congr 1
    exact congrFun (F.freeHomEquiv.apply_symm_apply σ.s) i
  rw [hi]
  rfl

set_option maxHeartbeats 2000000 in
-- Elaborating slice restriction and the module-sheafification unit needs this budget.
private lemma finite_of_constant_finiteType
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    (h_nonempty : ¬ Nonempty ((⊥_ (Sheaf J (Type (max u v)))) ≅
      (⊤_ (Sheaf J (Type (max u v))))))
    (hF : SheafOfModules.IsFiniteType.{max u v, v, u} (cmod J B M)) : Module.Finite B M := by
  classical
  let F := cmod J B M
  let := hF
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨U, hU⟩ := exists_nondegenerate J h_nonempty
  obtain ⟨U₀, a, ha, hU₀⟩ := cover_nondegenerate J hU _ (q.coversTop U)
  obtain ⟨i, ⟨b⟩⟩ := ha
  have hi : (⊥ : Sieve (q.X i)) ∉ J (q.X i) := by
    intro h
    exact hU₀ (by simpa using J.pullback_stable b h)
  let σ := q.generators i
  have : σ.IsFiniteType := hq.isFiniteType i
  let := Fintype.ofFinite σ.I
  obtain ⟨S, hS, hs⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq
    ((forget₂ (ModuleCat B) AddCommGrpCat).obj M)
    (fun j : σ.I ↦ (σ.s j).val (op (Over.mk (𝟙 (q.X i)))))
  obtain ⟨V, f, hf, hV⟩ := cover_nondegenerate J hi S hS
  choose x hx using hs f hf
  have hx' (j : σ.I) : (cunit J B M).app (op V) (x j) =
      (σ.s j).val (op (Over.mk f)) := by
    exact (hx j).trans ((σ.s j).property
      (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 (q.X i))).op)
  -- Kill the fixed lifts, so no constant refinement of local coefficients is needed.
  let N : Submodule B M := Submodule.span B (Set.range x)
  let Q := ModuleCat.of B (M ⧸ N)
  let p : M ⟶ Q := ModuleCat.ofHom N.mkQ
  let ψ := (siteConstantModuleFunctorGeneral J B).map p
  refine Module.finite_def.mpr ?_
  have hN : N = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨T, hT, ht⟩ := local_span (F.over (q.X i)) σ (Over.mk f)
      ((cunit J B M).app (op V) m)
    obtain ⟨W, g, hg, hW⟩ := cover_nondegenerate J hV
      ((Sieve.overEquiv (Over.mk f)) T) hT
    obtain ⟨c, hc⟩ := ht (Over.mk (g ≫ f)) (Over.homMk g rfl)
      ((Sieve.overEquiv_iff T g).mp hg)
    have hs (j : σ.I) : (σ.s j).val (op (Over.mk (g ≫ f))) =
        (cunit J B M).app (op W) (x j) := by
      rw [← cunit_restrict J B M g, hx']
      exact ((σ.s j).property (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f).op).symm
    have hzero : (cunit J B Q).app (op W) (p m) = 0 := by
      have h := congrArg (fun z ↦ ψ.val.app (op W) z) hc
      change ψ.val.app (op W)
        (F.val.map g.op ((cunit J B M).app (op V) m)) = _ at h
      dsimp only [F, ψ] at h
      rw [cunit_restrict J B M g, cunit_map] at h
      rw [h, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul, hs j, cunit_map]
      have hp : p (x j) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr
        (Submodule.subset_span (Set.mem_range_self j))
      rw [hp, map_zero, smul_zero]
    have hinj := J.toSheafify_const_app_injective
      ((forget₂ (ModuleCat B) AddCommGrpCat).obj Q) hW
    have hp : p m = 0 := hinj (hzero.trans (map_zero _).symm)
    exact (Submodule.Quotient.mk_eq_zero N).mp hp
  rw [← hN]
  exact Submodule.fg_span (Set.finite_range x)

private def constant_section_over {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (M : ModuleCat.{max u v} B) (U : C) (m : M) : ((cmod J B M).over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ (cunit J B M).app (op V.unop.left) m)
    (fun {_ _} f ↦ cunit_restrict J B M f.unop.left m)

private def constant_generators_over {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (M : ModuleCat.{max u v} B) (U : C) (t : Finset M)
    (ht : Submodule.span B (t : Set M) = ⊤) : ((cmod J B M).over U).GeneratingSections where
  I := (t : Set M)
  s j := constant_section_over J B M U j.val
  epi := by
    classical
    apply Preadditive.epi_of_cancel_zero
    intro N g hg
    have hgen (j : (t : Set M)) (V : (Over U)ᵒᵖ) :
        g.val.app V ((cunit J B M).app (op V.unop.left) j.val) = 0 := by
      have h := congrArg (fun k ↦
        (SheafOfModules.sectionsMap k (SheafOfModules.freeSection j)).val V) hg
      rw [SheafOfModules.sectionsMap_comp,
        SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection] at h
      exact h
    have hall (V : (Over U)ᵒᵖ) (m : M) :
        g.val.app V ((cunit J B M).app (op V.unop.left) m) = 0 := by
      have hm : m ∈ Submodule.span B (t : Set M) := by rw [ht]; trivial
      induction hm using Submodule.span_induction with
      | mem m hm => exact hgen ⟨m, hm⟩ V
      | zero => rw [map_zero, map_zero]
      | add m n _ _ hm hn => rw [map_add, map_add, hm, hn, add_zero]
      | smul b m _ hm =>
        rw [cunit_smul J B M V.unop.left, map_smul, hm, smul_zero]
    have : Presheaf.IsLocallySurjective J (cunit J B M) :=
      inferInstanceAs (Presheaf.IsLocallySurjective J
        (toSheafify J ((siteConstantModulePresheafGeneral (C := C) B).obj M).presheaf))
    let η := Functor.whiskerLeft (Over.forget U).op (cunit J B M)
    have : Presheaf.IsLocallySurjective (J.over U) η :=
      Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
    ext V z
    have hN := (isSheaf_iff_isSheaf_of_type (J.over U) _).mp
      ((sheafCompose (J.over U) (forget AddCommGrpCat)).obj
        ((SheafOfModules.toSheaf _).obj N)).property
    apply (hN _ (Presheaf.imageSieve_mem (J.over U) η z)).isSeparatedFor.ext
    intro W f hf
    obtain ⟨m, hm⟩ := hf
    change N.val.map f.op (g.val.app V z) = N.val.map f.op 0
    rw [map_zero, ← PresheafOfModules.naturality_apply g.val]
    change (cunit J B M).app (op W.left) m =
      ((cmod J B M).over U).val.map f.op z at hm
    change g.val.app (op W) (((cmod J B M).over U).val.map f.op z) = 0
    rw [← hm]
    exact hall (op W) m

private lemma constant_finiteType_of_finite
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    (h : Module.Finite B M) : SheafOfModules.IsFiniteType.{max u v, v, u} (cmod J B M) := by
  classical
  let := h
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := B) (M := M)
  let q : SheafOfModules.LocalGeneratorsData.{u} (cmod J B M) :=
    { I := C
      X := id
      coversTop := fun V ↦ J.covering_of_eq_top (by simp)
      generators U := constant_generators_over J B M U t ht }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    change (constant_generators_over J B M U t ht).IsFiniteType
    exact ⟨inferInstanceAs (Finite (t : Set M))⟩
  constructor
  exact ⟨q, hq⟩

/-- On a nonempty sheaf topos, the constant module sheaf is of finite type precisely
when its scalar module is finitely generated.
Source: Stacks Project, Modules on Sites, Tag 093N, assertion (1)
(blueprint: lem-sfb-constant-module-finite-type-reflection).

Proof:
1. If every object admitted the empty covering, every set sheaf would be terminal,
contrary to the hypothesis. Every covering of an object without an empty covering
has a member without an empty covering, by transitivity of the topology.
2. The additive sheafification unit is locally bijective. Intersecting finitely many
image sieves makes any finite tuple of sections constant on a common covering.
On an object without an empty covering the unit is injective, since the equalizer
sieve of two distinct constants is empty.
3. Scalar generators give generating constant sections on every slice. A morphism
annihilating those sections annihilates every constant section by span induction,
and then every section by local lifting and separatedness. Thus the associated
finite-free morphism is epi, giving finite-type local generators.
4. Conversely choose one nonempty object in a finite-type local-generators family,
and refine its finite generators to constants on one fixed nonempty member V.
Write x_j for their fixed scalar lifts, N for their scalar span, and Q for M/N.
5. Locally express the unit of any m in the generating tuple on the original slice.
This follows by lifting through its finite-free epimorphism and expanding in finite
free coordinates. Choose one nonempty member W of this covering of V.
6. Apply the map of constant module sheaves induced by M to Q to that expression.
Every generator maps to zero because x_j lies in N. Injectivity of the constant
unit for Q on W gives m in N. Thus N is the top submodule and M is finite.
The argument includes empty tuples, zero modules, and zero coefficient rings. -/
theorem siteConstantModuleFunctorGeneral_isFiniteType_iff
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    (h_nonempty : ¬ Nonempty
      ((⊥_ (Sheaf J (Type (max u v)))) ≅ (⊤_ (Sheaf J (Type (max u v)))))) :
    SheafOfModules.IsFiniteType ((siteConstantModuleFunctorGeneral J B).obj M) ↔
      Module.Finite B M := by
  constructor
  · exact finite_of_constant_finiteType J B M h_nonempty
  · exact constant_finiteType_of_finite J B M

end CategoryTheory
