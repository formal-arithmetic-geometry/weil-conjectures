/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsProjector
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!

# Continuity of the Galois action on noetherian cohomology sheaves of nearby cycles

Let `N` be a model of `X` with special fibre `X'` and `j : N.generic ⟶ N.total` quasi-compact and
quasi-separated, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois extension, `T₀` a finite discrete ring
and `Λ = C(-, T₀)`. Let `C` be such that `Lε^* C` is bounded below of étale origin.

If the cohomology sheaf `Hᵠ(Ψ_{N_Ω} C)` of the nearby cycles of the Galois layer is a noetherian
object, then an open subgroup of `Gal(Ω/L)` acts trivially on it: there is a finite Galois
subextension `L'` such that every `σ` fixing `L'` pointwise acts as the identity
(`NearbyCyclesModel.exists_forall_homology_galoisLayerAction_eq_id`), and similarly for finitely
many degrees at once
(`NearbyCyclesModel.exists_forall_mem_finset_homology_galoisLayerAction_eq_id`).

Indeed by continuity (`NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower`)
`Hᵠ(Ψ_{N_Ω} C)` is the filtered colimit of the cohomology sheaves of the finite layers; since it is
noetherian, the colimit is attained at some level `L'`
(`CategoryTheory.exists_epi_ι_of_isNoetherianObject`), on which `σ` acts through its restriction
to `L'`, i.e. trivially.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)

/-- The coprojections of the cocone of complexes `g_{j*} g_j^* K ⟶ g_{∞*} g_∞^* K` intertwine the
unit transport along an automorphism `σ` of `Y_∞` over `X` covering `a ∈ Γ_j` with the action
of `a` at the level `j`. -/
lemma complexCocone_ι_app_comp_unitTransport (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) (j : T.J)
    (a : T.Γ j) (ha : σ ≫ T.π j = T.π j ≫ T.ρ j a) :
    (T.complexCocone Λ K).ι.app j ≫
        (NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K =
      (NatTrans.mapHomologicalComplex (T.levelAction Λ j a) _).app K ≫
        (T.complexCocone Λ K).ι.app j :=
  HomologicalComplex.hom_ext _ _ fun n ↦ by
    have h := T.infTransport_comp_infAction Λ (K.X n) σ hσ j a ha
    rw [infAction_eq] at h
    exact h

end AlgebraicGeometry.ProEtale.GaloisTower

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
  (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]

omit [IsGalois L Ω] in
/-- An automorphism of `Ω` fixing `L'` pointwise restricts to the identity of `L'`. -/
lemma restrictNormal_eq_one_of_forall_apply_eq (L' : FiniteGaloisIntermediateField L Ω)
    (σ : Ω ≃ₐ[L] Ω) (hσ : ∀ x : L', σ x = x) : σ.restrictNormal L' = 1 :=
  AlgEquiv.ext fun x ↦
    (algebraMap L' Ω).injective ((AlgEquiv.restrictNormal_commutes σ L' x).trans (hσ x))

set_option profiler true in
set_option maxHeartbeats 1600000 in
-- matching the derived functors of the Galois layer with those of the field tower (as in
-- `exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`)
/-- **Continuity of the Galois action on a noetherian cohomology sheaf of nearby cycles**
(torsion coefficients). If `Lε^* C` is bounded below of étale origin and `Hᵠ(Ψ_{N_Ω} C)` is a
noetherian object, there is a finite Galois subextension `L'` of `Ω/L` such that every
`σ ∈ Gal(Ω/L)` fixing `L'` pointwise acts trivially on `Hᵠ(Ψ_{N_Ω} C)`. -/
theorem exists_forall_homology_galoisLayerAction_eq_id [QuasiCompact N.j] [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (q : ℤ) [IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))] :
    ∃ L' : FiniteGaloisIntermediateField L Ω, ∀ σ : Ω ≃ₐ[L] Ω, (∀ x : L', σ x = x) →
      (DerivedCategory.homologyFunctor _ q).map
        (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) = 𝟙 _ := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ _ hC
  choose F₀ hF₀ using hterms
  have hKe (n : ℤ) := essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some
  have hK (n : ℤ) :=
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  obtain ⟨hΦ⟩ := N.nonempty_isColimit_homology_nearbyCycles_galoisTower T₀ h Ω K a hKe q
  have : IsNoetherianObject ((DerivedCategory.Q ⋙
      R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K)).pt :=
    isNoetherianObject_of_mono ((DerivedCategory.homologyFunctor _ q).map
      (L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧).map
        (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧).map
          (GaloisTower.derivedTraceIso _ K a hK _ e).hom) ≫
        (N.galoisLayerExchangeIso h Ω (Profinite.continuousMapRingObj T₀) C).hom))
  obtain ⟨j, hj⟩ := exists_epi_ι_of_isNoetherianObject hΦ
  let L' : FiniteGaloisIntermediateField L Ω := j
  refine ⟨L', fun σ hσ ↦ ?_⟩
  have hU (τ : Ω ≃ₐ[L] Ω) (hτ : ∀ x : L', τ x = x) :=
    (galoisTower Ω h).complexCocone_ι_app_comp_unitTransport _ K _
      (pullbackAction_fst h _ specGaloisAction_comp τ) j 1
      (restrictNormal_eq_one_of_forall_apply_eq Ω L' τ hτ ▸
        pullbackAction_comp_galoisLevelProjection h L' τ)
  have key (τ : Ω ≃ₐ[L] Ω) (hτ : ∀ x : L', τ x = x) := by
    have hτ' := congrArg (DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ DerivedCategory.homologyFunctor _ q).map
        (hU τ hτ)
    rwa [Functor.map_comp, Functor.map_comp] at hτ'
  have hG := (cancel_epi (((DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K)).ι.app j)).1
    ((key σ hσ).trans (key 1 fun _ ↦ rfl).symm)
  simp only [Functor.comp_map] at hG
  have hA : (DerivedCategory.homologyFunctor _ q).map
      (L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧).map
        (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧).map
          (derivedUnitTransport (Profinite.continuousMapRingObj T₀)
            (pullbackAction h _ specGaloisAction_comp σ)
            (pullbackAction_fst h _ specGaloisAction_comp σ)
            (pullbackAction_fst h _ specGaloisAction_comp σ)
            (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))) =
      (DerivedCategory.homologyFunctor _ q).map
      (L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧).map
        (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧).map
          (derivedUnitTransport (Profinite.continuousMapRingObj T₀)
            (pullbackAction h _ specGaloisAction_comp 1)
            (pullbackAction_fst h _ specGaloisAction_comp 1)
            (pullbackAction_fst h _ specGaloisAction_comp 1)
            (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))) := by
    rw [← cancel_epi ((DerivedCategory.homologyFunctor _ q).map
      (L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧).map
        (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧).map
          (GaloisTower.derivedTraceIso _ K a hK _ e).hom)))]
    simp only [← Functor.map_comp, GaloisTower.derivedTraceIso_hom_comp_derivedUnitTransport]
    simp only [Functor.map_comp, hG]
  have hσ1 : (DerivedCategory.homologyFunctor _ q).map
      (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) =
      (DerivedCategory.homologyFunctor _ q).map
      (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω 1
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) := by
    rw [galoisLayerAction, galoisLayerAction, galoisLayerAut_autAction, galoisLayerAut_autAction,
      Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, hA]
  rw [hσ1, galoisLayerAction_one, CategoryTheory.Functor.map_id]

/-- **Continuity of the Galois action on noetherian cohomology sheaves of nearby cycles**, for
finitely many degrees at once: if the `Hᵠ(Ψ_{N_Ω} C)` are noetherian for `q ∈ s`, there is a single
finite Galois subextension `L'` such that every `σ` fixing `L'` pointwise acts trivially on all of
them. -/
theorem exists_forall_mem_finset_homology_galoisLayerAction_eq_id [QuasiCompact N.j]
    [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (s : Finset ℤ) (hs : ∀ q ∈ s, IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω, ∀ q ∈ s, ∀ σ : Ω ≃ₐ[L] Ω, (∀ x : L', σ x = x) →
      (DerivedCategory.homologyFunctor _ q).map
        (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) = 𝟙 _ := by
  choose L' hL' using fun (q : ℤ) (hq : q ∈ s) ↦
    have := hs q hq
    N.exists_forall_homology_galoisLayerAction_eq_id h Ω T₀ C hC q
  refine ⟨s.attach.sup fun q ↦ L' q.1 q.2, fun q hq σ hσ ↦ hL' q hq σ fun x ↦
    hσ ⟨x, Finset.le_sup (f := fun q : s ↦ L' q.1 q.2) (s.mem_attach ⟨q, hq⟩) x.2⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
