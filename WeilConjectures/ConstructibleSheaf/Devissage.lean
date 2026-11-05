/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.Topology.StratificationDense

/-!
# Dévissage of a constructible sheaf

A constructible sheaf `F` of `Λ`-modules on a Noetherian scheme `X` has a finite filtration
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_m = F` whose subquotients are extensions by zero of lisse sheaves along
locally closed immersions (`AlgebraicGeometry.Etale.exists_filtration_isFiniteLocallyConstant`,
blueprint `lem-fin-constructible-devissage`). A locally closed immersion is written as a closed
immersion `i : Y ⟶ W` into an open subscheme `W ⊆ X`, and the extension by zero along it is
`(W.ι)_! ∘ i_*`.

The filtration is `F_r = (U_r)_! (U_r)^* F ⊆ F` for a chain of opens
`∅ = U_0 ⊆ U_1 ⊆ ⋯ ⊆ U_m = X` such that each difference `U_r \ U_{r-1}` lies in a stratum of a
stratification trivializing `F`; such a chain exists by Noetherian induction
(`Topology.Stratification.exists_chain_opens`). The subquotients are computed by applying the
exact functor `(U_r)_!` to the open–closed exact sequence on `U_r`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

noncomputable section

namespace CategoryTheory

/-- If two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` have isomorphic right adjoints, their counits at
an object are isomorphic as arrows into that object. -/
lemma Adjunction.exists_iso_counit_app {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) (F : D) :
    ∃ α : L₁.obj (R₁.obj F) ≅ L₂.obj (R₂.obj F),
      adj₁.counit.app F = α.hom ≫ adj₂.counit.app F := by
  let adj' := adj₂.ofNatIsoRight e.symm
  refine ⟨(adj₁.leftAdjointUniq adj').app (R₁.obj F) ≪≫ L₂.mapIso (e.app F), ?_⟩
  rw [← Adjunction.leftAdjointUniq_hom_app_counit adj₁ adj']
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  congr 1

/-- If `f₁ = α ≫ φ ≫ f₂` for monomorphisms `f₁`, `f₂` and an isomorphism `α`, the cokernel of
the inclusion of subobjects `mk f₁ ≤ mk f₂` is the cokernel of `φ`. -/
def Subobject.cokernelOfLEMkIso {C : Type*} [Category C] [HasZeroMorphisms C] [HasCokernels C]
    {B A₁ A₁' A₂ : C} (f₁ : A₁ ⟶ B) (f₂ : A₂ ⟶ B) [Mono f₁] [Mono f₂] (α : A₁ ≅ A₁')
    (φ : A₁' ⟶ A₂) (hφ : f₁ = α.hom ≫ φ ≫ f₂) (h : mk f₁ ≤ mk f₂) :
    cokernel (ofLE _ _ h) ≅ cokernel φ :=
  cokernelIsoOfEq (f := ofLE _ _ h)
      (g := ((underlyingIso f₁).hom ≫ α.hom) ≫ φ ≫ (underlyingIso f₂).inv) (by
        rw [← cancel_mono (mk f₂).arrow, ofLE_arrow, ← underlyingIso_hom_comp_eq_mk]
        simp [← hφ]) ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _

end CategoryTheory

namespace Topology.Stratification

variable {X : Type*} [TopologicalSpace X] (S : Stratification X)

/-- For a proper open subset `U` of a space with a finite stratification, there is a strictly
larger open `U'` such that `U' \ U` lies in a single stratum: some stratum has nonempty interior
in the complement of `U`, the strata being finitely many locally closed subsets covering it. -/
lemma exists_lt_diff_subset_stratum (U : TopologicalSpace.Opens X) (hU : U ≠ ⊤) :
    ∃ U' : TopologicalSpace.Opens X, U < U' ∧ ∃ k, (U' : Set X) \ U ⊆ S.stratum k := by
  set C := (U : Set X)ᶜ
  have hC : C.Nonempty := by
    rw [Set.nonempty_iff_ne_empty, Ne, Set.compl_empty_iff]
    exact fun h ↦ hU (TopologicalSpace.Opens.coe_eq_univ.mp h)
  have : Nonempty C := hC.to_subtype
  let s : Fin S.n → Set C := fun k ↦ Subtype.val ⁻¹' S.stratum k
  obtain ⟨k, hk⟩ : ∃ k, (interior (s k)).Nonempty := by
    by_contra! h
    have hN : IsNowhereDense (⋃ k, s k) := isNowhereDense_iUnion fun k ↦
      ((S.isLocallyClosed_stratum k).preimage
        continuous_subtype_val).isNowhereDense_of_interior_eq_empty (h k)
    have hs : (⋃ k, s k) = Set.univ := by
      simp [s, ← Set.preimage_iUnion, S.iUnion_stratum_eq_univ]
    rw [hs, IsNowhereDense, closure_univ, interior_univ] at hN
    exact Set.univ_nonempty.ne_empty hN
  obtain ⟨N, hN, hNs⟩ := isOpen_induced_iff.mp (isOpen_interior (s := s k))
  refine ⟨U ⊔ ⟨N, hN⟩, ?_, k, ?_⟩
  · obtain ⟨c, hc⟩ := hk
    refine lt_of_le_of_ne le_sup_left fun h ↦ c.2 ?_
    have : c.1 ∈ (U ⊔ ⟨N, hN⟩ : TopologicalSpace.Opens X) := by
      rw [← hNs] at hc
      exact Or.inr hc
    rwa [← h] at this
  · rintro x ⟨hx, hxU⟩
    rcases hx with hx | hx
    · exact absurd hx hxU
    · have : (⟨x, hxU⟩ : C) ∈ interior (s k) := by
        rw [← hNs]
        exact hx
      exact interior_subset (s := s k) this

/-- On a Noetherian space with a finite stratification, every open `U` is the start of a finite
chain of opens `U = V₀ ≤ V₁ ≤ ⋯ ≤ V_m = X` each of whose differences `V_{r+1} \ V_r` lies in a
single stratum. -/
lemma exists_chain_opens [TopologicalSpace.NoetherianSpace X] (U : TopologicalSpace.Opens X) :
    ∃ (m : ℕ) (V : Fin (m + 1) → TopologicalSpace.Opens X), V 0 = U ∧ V (Fin.last m) = ⊤ ∧
      ∀ r : Fin m, V r.castSucc ≤ V r.succ ∧
        ∃ k, (V r.succ : Set X) \ V r.castSucc ⊆ S.stratum k := by
  induction U using WellFoundedGT.induction with
  | _ U ih =>
  by_cases hU : U = ⊤
  · exact ⟨0, fun _ ↦ U, rfl, hU, fun r ↦ r.elim0⟩
  obtain ⟨U', hUU', k, hk⟩ := S.exists_lt_diff_subset_stratum U hU
  obtain ⟨m, V, hV0, hVm, hstep⟩ := ih U' hUU'
  refine ⟨m + 1, Fin.cons U V, rfl, ?_, fun r ↦ ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ, hVm]
  · induction r using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hV0]
      exact ⟨hUU'.le, k, hk⟩
    | succ j =>
      rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hstep j

end Topology.Stratification

namespace AlgebraicGeometry

open Scheme

/-- The complement of the range of an open immersion is the range of a closed immersion (for
instance the reduced induced closed subscheme). -/
lemma exists_isClosedImmersion_range_eq_compl {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i.base = (Set.range j.base)ᶜ := by
  let I := IdealSheafData.vanishingIdeal (⟨(Set.range j.base)ᶜ,
    j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : TopologicalSpace.Closeds X)
  exact ⟨I.subscheme, I.subschemeι, inferInstance, by simp [I, IdealSheafData.range_subschemeι]⟩

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The counit `j_! j^* F ⟶ F` of the extension by zero along an open immersion is a
monomorphism, being the first map of the open–closed short exact sequence. -/
instance Etale.mono_openImmersionLowerShriekUpperStarAdjunction_counit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((Etale.openImmersionLowerShriekUpperStarAdjunction _ j).counit.app F) := by
  obtain ⟨Z, i, _, hi⟩ := exists_isClosedImmersion_range_eq_compl j
  exact (Etale.shortExact_openClosedShortComplex _ j i F hi).mono_f

end AlgebraicGeometry

end
