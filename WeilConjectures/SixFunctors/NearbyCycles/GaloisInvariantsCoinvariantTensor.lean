/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsCoinvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyTensorColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational

/-!

# The projector onto the invariants of nearby cycles, after a tensor product

Let `N` be a model, `h : N.generic ⟶ Spec L`, `Ω/L` Galois with degrees invertible in a finite
discrete field `T₀`, `Λ = C(-, T₀)` and `C` with `Lε^* C` bounded below of étale origin. The
exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has a retraction `r` whose projector
`r ≫ α` is the projector onto all the invariants in the following form: after pullback along any
`f' : Z ⟶ X'` and tensor product with any bounded below `W`, every map out of
`Hᵠ(Lf'^* Ψ_{N_Ω} C ⊗ W)` invariant under the Galois action (on the first factor) is fixed by
`Hᵠ(Lf'^*(r ≫ α) ⊗ W)`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_tensor`).

This is the coinvariant property used for the projection formula `(E ⊗ B)^P = E^P ⊗ B` in the
generic-slicing step of Gabber's Künneth formula (blueprint `det-nearby-kunneth-invariants`,
`NearbyCyclesModel.isIso_kunnethMap_of_isIso_galoisLayer`). The proof is that of
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant`, with the
continuity of the cohomology sheaves of the tensor product along the finite layers
(`ProEtale.CondensedRing.isColimit_homology_tensorRight_mapCocone`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]

set_option profiler true in
set_option maxHeartbeats 1600000 in
-- the objects of the Galois layer are large terms
/-- **`Ψ_N` is the summand of all the invariants of `Ψ_{N_Ω}`, after a continuous functor**
(SGA 4½, [Th. finitude], Lemme 3.4; torsion coefficients). Let `Ω/L` be Galois with degrees
invertible in `T₀` and `C` bounded below of étale origin on the generic fibre. The pullback
exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has a retraction `r` such that, for every
additive functor `G` to module objects which carries the cocone of the finite layers of every
bounded below complex (after `Li^* Rj_*`) to a colimit, every map out of `G(Ψ_{N_Ω} C)` invariant
under a family `act` of elements of `Gal(Ω/L)` meeting every element of every finite quotient
`Gal(L'/L)` is fixed by `G(r ≫ α)`. For `G = Hᵠ ∘ Lf'^*` this is
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_isColimit
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', act k x = a x) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      ∀ {Z : Scheme.{u}} (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) ⥤
            Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) [G.Additive],
        (∀ (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ) (a : ℤ)
            [K.IsStrictlyGE a], (∀ n, IsColimit ((galoisTower Ω h).abCocone (K.X n).X)) →
          Nonempty (IsColimit ((DerivedCategory.Q ⋙
            R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
              L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ G).mapCocone
                ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K)))) →
        ∀ {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : G.obj (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ⟶ W),
        (∀ k, G.map (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ≫ φ = φ) →
        G.map (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C) ≫ φ = φ := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ _ hC
  choose F₀ hF₀ using hterms
  have hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (M : Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) := fun j M ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) M
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hcab := fun n ↦ (nonempty_isColimit_galoisUpperLowerCocone (Ω := Ω) h (K.X n).X
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)).some
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  have hα := Hom.pullbackExchange_app_of_total_eq_id (Profinite.continuousMapRingObj T₀) N
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) _ rfl
    (N.galoisLayerHom h Ω) rfl rfl C
  simp only [eqToHom_refl, Category.id_comp] at hα
  have hlift : ∀ (j : FiniteGaloisIntermediateField L Ω) (b : (galoisTower Ω h).Γ j), ∃ k,
      pullbackAction h _ specGaloisAction_comp (act k) ≫ (galoisTower Ω h).π j =
        (galoisTower Ω h).π j ≫ (galoisTower Ω h).ρ j b := fun j b ↦ by
    obtain ⟨k, hk⟩ := hact j b
    refine ⟨k, ?_⟩
    have hres : (act k).restrictNormal j = b := by
      ext x
      exact (AlgEquiv.restrictNormal_commutes (act k) (j : IntermediateField L Ω) x).trans (hk x)
    have := pullbackAction_comp_galoisLevelProjection h j (act k)
    rw [hres] at this
    exact this
  have hadj := Adjunction.derivedAdjunction_unit_app_comp_derivedUnitRetraction K a hK
    ((galoisTower Ω h).complexTrace (Profinite.continuousMapRingObj T₀) hd K hc)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))))
    ((galoisTower Ω h).unit_comp_complexTrace (Profinite.continuousMapRingObj T₀) hd K hc)
  have hRC : (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) ≫
      (R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
          Profinite.continuousMapRingObj T₀⟧).map
        (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
          Profinite.continuousMapRingObj T₀⟧).map e.inv) ≫
        Adjunction.derivedUnitRetraction K a hK
          ((galoisTower Ω h).complexTrace (Profinite.continuousMapRingObj T₀) hd K hc) ≫
          e.hom) = 𝟙 _ := by
    have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.naturality e.inv
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    erw [reassoc_of% hadj]
    exact e.inv_hom_id
  have hmain := fun {Z : Scheme.{u}}
      (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) ⥤
          Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) ↦
    retraction_of_eq_comp_map_comp_of_coinvariant
      R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧)
      G _ ((leftDerivedUpperStarId (Profinite.continuousMapRingObj T₀) X').app _) _
      (N.galoisLayerExchangeIso h Ω (Profinite.continuousMapRingObj T₀) C) rfl _ _ hα hRC
      (fun k ↦ derivedUnitTransport (Profinite.continuousMapRingObj T₀)
        (pullbackAction h _ specGaloisAction_comp (act k))
        (pullbackAction_fst h _ specGaloisAction_comp (act k))
        (pullbackAction_fst h _ specGaloisAction_comp (act k))
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))
      (fun k ↦ N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))
      (fun k ↦ galoisLayerAut_autAction (Profinite.continuousMapRingObj T₀) N h Ω (act k) C)
  refine ⟨_, (hmain (DerivedCategory.homologyFunctor _ 0)).1, fun {Z} G _ hG W φ hφ ↦ ?_⟩
  have hdZ : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) := fun j M ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) M
  refine (hmain G).2 φ (fun φ' hφ' ↦ ?_) hφ
  exact (galoisTower Ω h).map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK _ e
    (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ G)
    (hG K a hcab).some
    (fun k ↦ pullbackAction h _ specGaloisAction_comp (act k))
    (fun k ↦ pullbackAction_fst h _ specGaloisAction_comp (act k)) hlift (fun j ↦ hdZ j W) φ'
    hφ'


set_option profiler true in
set_option maxHeartbeats 800000 in
-- the objects of the Galois layer are large terms
/-- **`Ψ_N` is the summand of all the invariants of `Ψ_{N_Ω}`, after a tensor product** (SGA 4½,
[Th. finitude], Lemme 3.4; blueprint `det-nearby-kunneth-invariants`; finite field coefficients).
Let `Ω/L` be Galois with degrees invertible in the finite field `T₀` and `C` bounded below of étale
origin on the generic fibre. The pullback exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has
a retraction `r` such that, on the cohomology sheaves of `Lf'^*(-) ⊗ V` for any `f' : Z ⟶ X'` and
any bounded below `V`, every map invariant under a family `act` of elements of `Gal(Ω/L)` meeting
every element of every finite quotient `Gal(L'/L)` is fixed by the projector `r ≫ α`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_tensor (T₀ : Type)
    [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    {Z : Scheme.{u}} (f' : Z ⟶ X') {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', act k x = a x) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      ∀ (q : ℤ) (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))) (b : ℤ), V.IsGE b →
        ∀ {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : (DerivedCategory.homologyFunctor _ q).obj
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ⊗ V) ⟶ W),
        (∀ k, (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ▷ V) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C) ▷ V) ≫ φ = φ := by
  obtain ⟨r, hr, hcoinv⟩ :=
    exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_isColimit T₀ N h Ω hp C hC act
      hact
  refine ⟨r, hr, fun q V b hV W φ hφ ↦ ?_⟩
  refine hcoinv (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ tensorRight V ⋙
    DerivedCategory.homologyFunctor _ q) (fun K a _ hcab ↦ ?_) φ hφ
  -- the cohomology of the tensor product is continuous along the finite layers
  let F := DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
    L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ L((f')^*⟦Profinite.continuousMapRingObj T₀⟧)
  have hGE : ∀ (Y : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ), Y.IsStrictlyGE a →
        (F.obj Y).IsGE a := fun Y hY ↦ by
    have := Functor.isGE_rightDerivedFunctor_obj ((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧)
      (DerivedCategory.Q.obj Y) a
    have := isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj T₀) N.i
      (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧).obj (DerivedCategory.Q.obj Y)) a
    exact isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj T₀) f' _ a
  have hpt : ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K).pt.IsStrictlyGE
      a := (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi ↦
    (ProEtale.GaloisTower.infFunctor (Profinite.continuousMapRingObj T₀) _).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K a i hi)
  exact isColimit_homology_tensorRight_mapCocone' T₀
    ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K) F a
    (fun j ↦ hGE _ inferInstance) (hGE _ hpt)
    (fun p ↦ (nonempty_isColimit_homology_pullback_nearbyCycles_complexCocone T₀ N
      (galoisTower Ω h) K hcab a f' p).some) V b hV q

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
