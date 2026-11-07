/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf


public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.Compactification.FiniteTypeDirected
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-!
# Ideal sheaves of finite type as sheaves of modules

Let `J` be a quasi-coherent ideal sheaf on a scheme `X`, given as a
`AlgebraicGeometry.Scheme.IdealSheafData`, and let `J.toModules` be the corresponding
`𝒪_X`-module. This file relates the ring-theoretic notion of finite type
(`AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType`: the ideal is finitely generated over
every affine open) to the module-theoretic one (`SheafOfModules.IsFiniteType`: locally generated
by finitely many sections), and records the short exact sequence
`0 ⟶ ℐ ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0`. On a quasi-compact quasi-separated scheme, finitely many
sections of an ideal sheaf over quasi-compact opens already lie in a subsheaf of finite type.

## Main statements

- `SheafOfModules.epi_freeHomEquiv_symm_of_locally_mem_span`: a family of global sections
  generates a sheaf of modules as soon as every local section lies, locally, in their span.
- `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_toModules`: an ideal sheaf of finite type
  is of finite type as a sheaf of modules.
- `AlgebraicGeometry.Scheme.IdealSheafData.shortExact_shortComplex`: the sequence
  `0 ⟶ ℐ ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0` is short exact.
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_ofFiniteType_le_mem_idealOfOpens`: a section
  of an ideal sheaf over a quasi-compact open of a qcqs scheme is a section of a finite-type
  subsheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

/-! ### The ideals cut out on arbitrary opens -/

namespace AlgebraicGeometry


namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}


end Scheme.IdealSheafData

end AlgebraicGeometry


namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Local generation criterion.** A family `s` of global sections of a sheaf of modules `M`
generates `M` (i.e. the induced morphism `free I ⟶ M` is an epimorphism) as soon as every
section `m` of `M` over any object `X` lies, after restriction to the members of a covering
presieve of `X`, in the submodule spanned by the restrictions of the `s i`. -/
lemma epi_freeHomEquiv_symm_of_locally_mem_span {M : SheafOfModules.{u} R} {I : Type u}
    (s : I → M.sections)
    (h : ∀ (X : C) (m : M.val.obj (op X)), ∃ S : Presieve X, Sieve.generate S ∈ J X ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → M.val.map f.op m ∈ Submodule.span (R.obj.obj (op Y))
        (Set.range fun i ↦ PresheafOfModules.sections.eval (s i) (op Y))) :
    Epi (M.freeHomEquiv.symm s) := by
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (M.freeHomEquiv.symm s)) := by
    refine ⟨fun {X} m ↦ ?_⟩
    obtain ⟨S, hS, hm⟩ := h X m
    refine J.superset_covering ((Sieve.generate_le_iff _ _).2 fun Y f hf ↦ ?_) hS
    have hle : Submodule.span (R.obj.obj (op Y))
        (Set.range fun i ↦ PresheafOfModules.sections.eval (s i) (op Y)) ≤
          LinearMap.range ((M.freeHomEquiv.symm s).val.app (op Y)).hom := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨(freeSection i).val (op Y), congrArg (fun t : M.sections ↦ t.val (op Y))
        (sectionsMap_freeHomEquiv_symm_freeSection s i)⟩
    obtain ⟨t, ht⟩ := hle (hm f hf)
    exact ⟨t, ht⟩
  exact (SheafOfModules.toSheaf R).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

end SheafOfModules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Let `g` be a finite family generating the ideal `J(U)` over an affine open `U`, and let `m`
be the corresponding sections of the ideal sheaf `J.toModules` over `U`. Then over every basic
open `D(a) ⊆ U`, every section of `J.toModules` is a linear combination of the restrictions of
the `m i`, since `J(D(a)) = J(U)_a`. -/
lemma mem_span_map_of_span_eq (J : X.IdealSheafData) (U : X.affineOpens) {ι : Type*} [Finite ι]
    (g : ι → Γ(X, U.1)) (hg : Ideal.span (Set.range g) = J.ideal U)
    (m : ι → Γ(J.toModules, U.1)) (hm : ∀ i, J.toModulesι.app U.1 (m i) = g i) (a : Γ(X, U.1))
    (n : Γ(J.toModules, X.basicOpen a)) :
    n ∈ Submodule.span Γ(X, X.basicOpen a)
      (Set.range fun i ↦ J.toModules.presheaf.map (homOfLE (X.basicOpen_le a)).op (m i)) := by
  have := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ : ∃ x : Γ(X, X.basicOpen a), J.toModulesι.app _ n = x := ⟨_, rfl⟩
  have hn : x ∈ J.ideal (X.affineBasicOpen a) :=
    (J.range_toModulesι_app (X.affineBasicOpen a)).subset ⟨n, hx⟩
  rw [← J.map_ideal_basicOpen, ← hg, Ideal.map_span, ← Set.range_comp] at hn
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hn
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨c, J.injective_toModulesι_app _ ?_⟩
  rw [map_sum, hx, ← hc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := ConcreteCategory.congr_hom
    (J.toModulesι.mapPresheaf.naturality (homOfLE (X.basicOpen_le a)).op) (m i)
  exact (Modules.Hom.app_smul _ _ _).trans (congrArg (c i * ·) (h.trans (congrArg _ (hm i))))

/-- Over an affine open `U` on which the ideal `J(U)` is finitely generated, the restriction
`J.toModules.over U` is generated by finitely many sections. -/
lemma exists_generatingSections_over (J : X.IdealSheafData) (U : X.affineOpens)
    (hU : (J.ideal U).FG) :
    ∃ σ : (J.toModules.over U.1).GeneratingSections, σ.IsFiniteType := by
  classical
  obtain ⟨t, ht⟩ := hU
  have hmem (g : t) : (g : Γ(X, U.1)) ∈ Set.range (J.toModulesι.app U.1) := by
    rw [J.range_toModulesι_app U, ← ht]
    exact Ideal.subset_span g.2
  choose m hm using hmem
  let T : Over U.1 := Over.mk (𝟙 U.1)
  let s (g : t) : (J.toModules.over U.1).sections :=
    PresheafOfModules.sectionsMk
      (fun W ↦ (J.toModules.over U.1).val.map (Over.homMk W.unop.hom : W.unop ⟶ T).op (m g))
      (fun W W' f ↦ by
        refine (PresheafOfModules.map_comp_apply _ _ _ _).symm.trans ?_
        congr 2)
  refine ⟨⟨t, s, SheafOfModules.epi_freeHomEquiv_symm_of_locally_mem_span s fun W n ↦ ?_⟩,
    ⟨inferInstance⟩⟩
  refine ⟨fun Y f ↦ (J.toModules.over U.1).val.map f.op n ∈ Submodule.span _
    (Set.range fun g ↦ PresheafOfModules.sections.eval (s g) (op Y)), ?_, fun Y f hf ↦ hf⟩
  rw [GrothendieckTopology.mem_over_iff]
  intro x hx
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (W.hom.le hx)
  refine ⟨X.basicOpen a, homOfLE haW, ?_, hxa⟩
  rw [Sieve.overEquiv_iff]
  refine Sieve.le_generate _ _ _ ?_
  exact J.mem_span_map_of_span_eq U Subtype.val (by rw [Subtype.range_coe]; exact ht) m hm a _

/-- **An ideal sheaf of finite type is of finite type as a sheaf of modules.** Over every affine
open `U` the ideal `J(U)` is finitely generated, and the corresponding sections generate the
restriction of `J.toModules` to `U` (`exists_generatingSections_over`). -/
theorem isFiniteType_toModules (J : X.IdealSheafData) (hJ : J.ofFiniteType) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf) J.toModules := by
  choose σ hσ using fun U : X.affineOpens ↦ J.exists_generatingSections_over U (hJ U le_top)
  let q : SheafOfModules.LocalGeneratorsData.{u} J.toModules :=
    { I := X.affineOpens
      X := fun U ↦ U.1
      coversTop := (Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top X)
      generators := σ }
  constructor
  refine ⟨q, ?_⟩
  constructor
  exact hσ

/-- The comparison morphism `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` is an epimorphism: over an affine open the
restriction map to the closed subscheme `V(J)` is surjective. -/
instance epi_toPushforwardSubscheme (J : X.IdealSheafData) : Epi J.toPushforwardSubscheme := by
  refine Modules.epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hx
  obtain ⟨z, hz⟩ := J.subschemeι.app_surjective V hV (J.subscheme.presheaf.map
    ((TopologicalSpace.Opens.map J.subschemeι.base).map (homOfLE hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

/-- The short complex `0 ⟶ ℐ ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0` of `𝒪_X`-modules attached to an
ideal sheaf `J`. -/
noncomputable def shortComplex (J : X.IdealSheafData) : ShortComplex X.Modules :=
  ShortComplex.mk J.toModulesι J.toPushforwardSubscheme (kernel.condition _)


end AlgebraicGeometry.Scheme.IdealSheafData
