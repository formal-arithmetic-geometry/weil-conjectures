/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample

/-!
# Geometric points are not conservative on all pro-étale sheaves

This file proves the warning clause (4) of blueprint `lem-cbc-proetale-stalk-conservative`: for
an algebraically closed field `k` and a nonzero abelian group `M`, there is a sheaf `F` of
abelian groups on the small pro-étale site of `T = Spec k` with `F(T) = 0` but `F ≠ 0`. Since `T`
has a single geometric point and the global sections functor `Γ(T, -)` is exact on `T_proét`,
`Γ(T, -)` is the fibre functor at that point, which is therefore not conservative.

The sheaf `F` is the quotient of the sheaf `V ↦ {functions |V| → M}` of all set-theoretic
functions by the constant sheaf `M` (whose sections are the locally constant functions):

* `F(T) = 0`: the space `|T|` is a point, so every function on it is constant, and `Γ(T, -)`
  preserves epimorphisms (`AlgebraicGeometry.ProEtale.surjective_app_of_epi_of_iso`).
* `F ≠ 0`: the object `U = Spec C_lc(S, k)` of `T_proét`, for an infinite profinite set `S`,
  has a point `x` which is not open. The indicator function of `x` is not locally constant on
  any pro-étale covering of `U`, since the members of a pro-étale covering family are jointly a
  quotient map (`AlgebraicGeometry.Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage`).

The sheaf of all functions `V ↦ {functions |V| → M}` is realised as the sheaf of continuous maps
to `M` with the indiscrete topology, which is a sheaf by
`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheafAb`.

## Main definitions

- `AlgebraicGeometry.ProEtale.functionsSheaf`: the pro-étale sheaf `V ↦ C(|V|, M)`.
- `AlgebraicGeometry.ProEtale.constantToFunctionsSheaf`: the inclusion of the constant sheaf.
- `AlgebraicGeometry.ProEtale.functionsModConstant`: its cokernel.

## Main results

- `AlgebraicGeometry.ProEtale.exists_isZero_obj_mkId_and_not_isZero`: clause (4).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry

namespace ProEtale

open Scheme

section LocallyConstant

variable (k : Type u) [Field k] (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [TotallyDisconnectedSpace S]

/-- The prime ideal of `C_lc(S, k)` of functions vanishing at `s`. -/
noncomputable def locallyConstantEvalPoint (s : S) : PrimeSpectrum (LocallyConstant S k) :=
  ⟨RingHom.ker (LocallyConstant.evalRingHom s), RingHom.ker_isPrime _⟩

lemma locallyConstantEvalPoint_injective :
    Function.Injective (locallyConstantEvalPoint k S) := by
  intro s t hst
  by_contra hne
  obtain ⟨C, hC, hs, ht⟩ := exists_isClopen_of_totally_separated hne
  have h := congrArg (fun P : PrimeSpectrum (LocallyConstant S k) ↦
    LocallyConstant.charFn k hC ∈ P.asIdeal) hst
  simp only [locallyConstantEvalPoint, RingHom.mem_ker, LocallyConstant.evalRingHom_apply,
    LocallyConstant.coe_charFn, Set.indicator_of_mem hs, Set.indicator_of_notMem ht,
    Pi.one_apply] at h
  exact one_ne_zero (h.2 rfl)

/-- For an infinite profinite set `S`, the spectrum of `C_lc(S, k)` has a point which is not
open: it is compact and infinite, hence not discrete. -/
lemma exists_not_isOpen_singleton_locallyConstant [Infinite S] :
    ∃ x : PrimeSpectrum (LocallyConstant S k), ¬ IsOpen ({x} : Set _) := by
  by_contra! h
  have : DiscreteTopology (PrimeSpectrum (LocallyConstant S k)) := ⟨by
    ext U
    exact ⟨fun _ ↦ trivial, fun _ ↦ isOpen_iff_forall_mem_open.2 fun x hx ↦
      ⟨{x}, Set.singleton_subset_iff.2 hx, h x, rfl⟩⟩⟩
  have := finite_of_compact_of_discrete (X := PrimeSpectrum (LocallyConstant S k))
  exact not_finite S (Finite.of_injective _ (locallyConstantEvalPoint_injective k S))

end LocallyConstant

section Functions

variable (X : Scheme.{u}) (M : Type (u + 1)) [AddCommGroup M] [TopologicalSpace M]
  [IndiscreteTopology M]

/-- The pro-étale sheaf `V ↦ C(|V|, M)` of all set-theoretic functions from the underlying
space of `V` to `M`, for `M` with the indiscrete topology (so that every function is
continuous). It is the restriction to the small pro-étale site of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheafAb`. -/
noncomputable def functionsSheaf : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  ⟨(ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheafAb.{u + 1, u} M,
    (ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf (Scheme.ProEt.topology X) proetaleTopology
      ⟨continuousMapPresheafAb.{u + 1, u} M,
        Presheaf.isSheaf_of_le _ proetaleTopology_le_fpqcTopology
          (isSheaf_fpqcTopology_continuousMapPresheafAb M)⟩⟩

/-- The inclusion of the constant presheaf `M` into the sheaf of all functions, as the
constant functions. -/
noncomputable def constantToFunctions :
    (Functor.const _).obj (AddCommGrpCat.of M) ⟶ (functionsSheaf X M).obj where
  app V := AddCommGrpCat.ofHom
    { toFun m := ContinuousMap.const _ m
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma constantToFunctions_app_apply (V : X.ProEtᵒᵖ) (m : M) :
    (constantToFunctions X M).app V m = ContinuousMap.const _ m :=
  rfl

/-- The inclusion of the constant sheaf `M` (the sheafification of the constant presheaf,
whose sections are the locally constant functions) into the sheaf of all functions. -/
noncomputable def constantToFunctionsSheaf :
    (presheafToSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      ((Functor.const _).obj (AddCommGrpCat.of M)) ⟶ functionsSheaf X M :=
  ⟨sheafifyLift _ (constantToFunctions X M) (functionsSheaf X M).property⟩

/-- The pro-étale sheaf of functions modulo locally constant functions: the cokernel of the
inclusion of the constant sheaf into the sheaf of all functions. -/
noncomputable def functionsModConstant : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  cokernel (constantToFunctionsSheaf X M)

/-- On a scheme `X` isomorphic to the spectrum of an algebraically closed field, the global
sections of the sheaf of functions modulo locally constant functions vanish: every function on
the one-point space `|X|` is constant, and `Γ(X, -)` preserves epimorphisms. -/
lemma isZero_functionsModConstant_obj_mkId {K : Type u} [Field K] [IsAlgClosed K]
    (e : X ≅ Spec (.of K)) :
    IsZero ((functionsModConstant X M).obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) := by
  have hsub (x y : X) : x = y := e.hom.homeomorph.injective (Subsingleton.elim _ _)
  have hsurj := surjective_app_of_epi_of_iso e (cokernel.π (constantToFunctionsSheaf X M))
  refine AddCommGrpCat.isZero_of_subsingleton _
  refine ⟨fun a b ↦ ?_⟩
  suffices h : ∀ a, a = 0 by rw [h a, h b]
  intro a
  obtain ⟨g, rfl⟩ := hsurj a
  obtain ⟨x⟩ : Nonempty X := ⟨e.inv (Classical.arbitrary _)⟩
  have hg : g = (constantToFunctions X M).app (op (Scheme.ProEt.mk (𝟙 X))) (g x) :=
    ContinuousMap.ext fun y ↦ by rw [hsub y x]; rfl
  rw [hg, ← toSheafify_sheafifyLift (Scheme.ProEt.topology X) (constantToFunctions X M)
    (functionsSheaf X M).property]
  have := congrArg (fun φ ↦ φ.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
    ((toSheafify _ ((Functor.const _).obj (AddCommGrpCat.of M))).app _ (g x)))
    (cokernel.condition (constantToFunctionsSheaf X M))
  simpa [constantToFunctionsSheaf] using this

/-- If some object `U` of the small pro-étale site of `X` has a point `x` which is not open, the
sheaf of functions modulo locally constant functions does not vanish: the indicator function of
`x` is not locally constant on any pro-étale covering of `U`. -/
lemma not_isZero_functionsModConstant [Nontrivial M] (U : X.ProEt) (x : U.left)
    (hx : ¬ IsOpen ({x} : Set U.left)) :
    ¬ IsZero (functionsModConstant X M) := by
  classical
  intro h
  have : Epi (constantToFunctionsSheaf X M) := epi_of_isZero_cokernel _ h
  have : Sheaf.IsLocallySurjective (constantToFunctionsSheaf X M) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToFunctions X M) := by
    rw [← toSheafify_sheafifyLift (Scheme.ProEt.topology X) (constantToFunctions X M)
      (functionsSheaf X M).property]
    infer_instance
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let f : C(U.left, M) := ⟨fun y ↦ if y = x then m else 0, continuous_of_indiscreteTopology⟩
  obtain ⟨R, hR, hRle⟩ := Scheme.ProEt.mem_topology_iff.1
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) (constantToFunctions X M)
      (U := op U) f)
  obtain ⟨ι, Y, g, rfl⟩ := R.exists_eq_ofArrows
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hR
  refine hx (isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage (fun i ↦ (g i).left) hR _
    fun i ↦ ?_)
  obtain ⟨m', hm'⟩ := hRle _ (Presieve.ofArrows.mk i)
  have hpre : (g i).left.base ⁻¹' {x} = (fun _ ↦ m') ⁻¹' {m} := by
    ext y
    have := congrArg (fun φ : C((Y i).left, M) ↦ φ y) hm'
    simp only [constantToFunctions_app_apply, ContinuousMap.const_apply] at this
    simp only [Set.mem_preimage, Set.mem_singleton_iff, this]
    change _ ↔ (if _ = x then m else 0) = m
    split_ifs with hy
    · simp [hy]
    · simp [hy, hm.symm]
  rw [hpre, Set.preimage_const]
  split_ifs
  · exact isOpen_univ
  · exact isOpen_empty

end Functions

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (4): *warning*. Geometric-point stalks are
not conservative on all pro-étale sheaves. For an algebraically closed field `k` and a nonzero
abelian group `M`, there is a sheaf `F` of abelian groups on the small pro-étale site of
`T = Spec k` with `F(T) = 0` but `F ≠ 0`; as `T` has a single geometric point, at which the
stalk is `Γ(T, -)`, this exhibits a nonzero sheaf all of whose geometric-point stalks vanish.

The sheaf is the quotient of the sheaf of all functions `|U| → M` by the locally constant
ones (`AlgebraicGeometry.ProEtale.functionsModConstant`); it is nonzero on the object
`U = Spec C_lc(S, k)` of `T_proét` attached to the infinite profinite set `S = {0, 1}^ℕ`. -/
theorem exists_isZero_obj_mkId_and_not_isZero (k : Type u) [Field k] [IsAlgClosed k]
    (M : Type (u + 1)) [AddCommGroup M] [Nontrivial M] :
    ∃ F : Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1},
      IsZero (F.obj.obj (op (Scheme.ProEt.mk (𝟙 _)))) ∧ ¬ IsZero F := by
  letI : TopologicalSpace M := ⊤
  let S : Type u := ULift.{u} ℕ → Bool
  obtain ⟨x, hx⟩ := exists_not_isOpen_singleton_locallyConstant k S
  exact ⟨functionsModConstant _ M, isZero_functionsModConstant_obj_mkId _ M (Iso.refl _),
    not_isZero_functionsModConstant _ M (locallyConstantProEt k S) x hx⟩

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (4): *warning*. For an algebraically closed
field `k`, the global sections functor `Γ(T, -)` on abelian sheaves on the small pro-étale site
of `T = Spec k`, which is the stalk functor at the unique geometric point of `T` and is exact,
does not reflect isomorphisms. -/
theorem not_reflectsIsomorphisms_sheafSections_mkId (k : Type u) [Field k] [IsAlgClosed k] :
    ¬ ((sheafSections (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 _)))).ReflectsIsomorphisms := by
  intro hR
  obtain ⟨F, hF, hF'⟩ := exists_isZero_obj_mkId_and_not_isZero k (ULift.{u + 1} (ZMod 2))
  have : IsIso ((sheafSections _ AddCommGrpCat.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 _)))
      |>.map (0 : F ⟶ 0)) :=
    isIso_of_source_target_iso_zero _ hF.isoZero
      ((((sheafSections _ _).obj _).map_isZero (isZero_zero _)).isoZero)
  have := isIso_of_reflects_iso (0 : F ⟶ 0)
    ((sheafSections (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 _))))
  exact hF' ((isZero_zero _).of_iso (asIso (0 : F ⟶ 0)))

end ProEtale

end AlgebraicGeometry
