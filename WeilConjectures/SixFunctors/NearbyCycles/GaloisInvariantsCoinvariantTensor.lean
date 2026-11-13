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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShortcutInstances

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

/-- Transport a retraction and its coinvariant property simultaneously for all functors.
The witness is constructed before the target category and functor are chosen. -/
private lemma CategoryTheory.exists_retraction_of_eq_comp_map_comp_of_coinvariant
    {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {A₀ T : C} {P Q : E} (α : P ⟶ Q) (i : P ≅ F.obj A₀) (κ : F.obj T ≅ Q)
    (η : A₀ ⟶ T) (R : T ⟶ A₀) (hα : α = i.hom ≫ F.map η ≫ κ.hom)
    (hR : η ≫ R = 𝟙 A₀) {ι : Type*} (act : ι → (T ⟶ T)) (ρ : ι → (Q ⟶ Q))
    (hρ : ∀ σ, ρ σ = κ.inv ≫ F.map (act σ) ≫ κ.hom) :
    ∃ r, α ≫ r = 𝟙 P ∧
      ∀ {A : Type*} [Category A] (G : E ⥤ A) {B : A} (φ : G.obj Q ⟶ B),
        (∀ φ' : G.obj (F.obj T) ⟶ B,
          (∀ σ, G.map (F.map (act σ)) ≫ φ' = φ') →
            G.map (F.map (R ≫ η)) ≫ φ' = φ') →
        (∀ σ, G.map (ρ σ) ≫ φ = φ) → G.map (r ≫ α) ≫ φ = φ := by
  refine ⟨_, (retraction_of_eq_comp_map_comp_of_coinvariant F (𝟭 E) (𝟭 E)
    α i κ.hom κ rfl η R hα hR act ρ hρ).1, ?_⟩
  intro A _ G B φ hcoinv hφ
  exact (retraction_of_eq_comp_map_comp_of_coinvariant F (𝟭 E) G
    α i κ.hom κ rfl η R hα hR act ρ hρ).2 φ hcoinv hφ

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

-- Resolve tensor colimit obligations directly, before instance search expands the graded
-- tensor diagrams used in the construction of each derived pullback.
/-- Small colimits of module objects, shared by the derived functor constructions below. -/
private theorem galoisTensorModuleColimit (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {J : Type} [SmallCategory J] (F : J ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) :
    HasColimit F := inferInstance

/-- Tensoring on the left preserves a small colimit of module objects. -/
private theorem galoisTensorLeftColimit (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    {J : Type} [SmallCategory J] (F : J ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) :
    PreservesColimit F ((curriedTensor _).obj M) := inferInstance

/-- Tensoring on the right preserves a small colimit of module objects. -/
private theorem galoisTensorRightColimit (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    {J : Type} [SmallCategory J] (F : J ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) :
    PreservesColimit F ((curriedTensor _).flip.obj M) := inferInstance

/-- The exchange of a Galois layer is the image of the derived unit, with the comparison
isomorphisms on either side. -/
private lemma pullbackExchange_galoisLayerHom_app_eq_comp_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
    (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C =
      ((leftDerivedUpperStarId Λ X').app ((N.nearbyCycles Λ).obj C)).hom ≫
        (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)).map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
              (L((N.ε)^*⟦Λ⟧).obj C)) ≫ (N.galoisLayerExchangeIso h Ω Λ C).hom := by
  have hα := Hom.pullbackExchange_app_of_total_eq_id Λ N
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) _ rfl
    (N.galoisLayerHom h Ω) rfl rfl C
  simp only [eqToHom_refl, Category.id_comp] at hα
  -- Normalize the model before matching the exchange formula.
  dsimp only [galoisLayer, galoisLayerExchangeIso, Functor.comp_map, Functor.mapIso_hom,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  simpa only [Functor.map_comp] using hα

/-- Transport the normalized trace retraction of a tower from a bounded below complex
across an isomorphism in the derived category. -/
private theorem galoisTower_derivedUnit_retraction_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {S Sinf : Scheme.{u}} (g : Sinf ⟶ S) [WeaklyEtale g] (T : GaloisTower g)
    (hd : ∀ (j : T.J) (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)), IsIso (Fintype.card (T.Γ j) • 𝟙 M))
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)) ℤ) (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n)))
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((g)_*⟦Λ⟧).rightAcyclic (((g)^*⟦Λ⟧).obj (K.X n)))
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))} (e : DerivedCategory.Q.obj K ≅ A) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).unit.app A ≫
      (R((g)_*⟦Λ⟧).map (L((g)^*⟦Λ⟧).map e.inv) ≫
        Adjunction.derivedUnitRetraction (f := (g)^*⟦Λ⟧) (g := (g)_*⟦Λ⟧) K a hK
          (T.complexTrace Λ hd K hc) ≫ e.hom) = 𝟙 _ := by
  have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).unit.naturality e.inv
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
  have hadj := Adjunction.derivedAdjunction_unit_app_comp_derivedUnitRetraction
    (f := (g)^*⟦Λ⟧) (g := (g)_*⟦Λ⟧) K a hK (T.complexTrace Λ hd K hc)
    (CondensedRing.upperStarLowerStarAdjunction Λ g) (T.unit_comp_complexTrace Λ hd K hc)
  rw [← reassoc_of% hn]
  erw [reassoc_of% hadj]
  exact e.inv_hom_id

/-- Invertible finite Galois degrees act invertibly on every coefficient module. -/
private theorem isIso_galois_card_smul_id (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀]
    [IsTopologicalRing T₀] [DiscreteTopology T₀] {L Ω : Type u} [Field L] [Field Ω]
    [Algebra L Ω] (j : FiniteGaloisIntermediateField L Ω)
    (hj : IsUnit ((Module.finrank L j : ℕ) : T₀)) {Z : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) :
    IsIso (Fintype.card (j ≃ₐ[L] j) • 𝟙 M) := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀) hj M

/-- The normalized trace of a Galois tower fixes invariant maps after every additive functor
that carries its bounded below complex cocones to colimits. -/
private theorem exists_retraction_derivedUnit_galois_coinvariant_of_isColimit
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
    [DiscreteTopology T₀] [Finite T₀] {S : Scheme.{u}} {L : Type u} [Field L]
    (h : S ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
    (hp : ∀ j : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L j : ℕ) : T₀))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) S)))
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) S
      ((finiteCoefficientDerivedEquivalence S T₀).functor.obj A))
    {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (j : FiniteGaloisIntermediateField L Ω) (a : j ≃ₐ[L] j),
      ∃ k, ∀ x : j, act k x = a x) :
    ∃ R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj T₀⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.continuousMapRingObj T₀⟧).obj A) ⟶ A,
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app A ≫ R = 𝟙 A ∧
      ∀ {Z : Scheme.{u}} (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) S)) ⥤
            Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) [G.Additive],
        (∀ (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousMapRingObj T₀) S)) ℤ) (a : ℤ) [K.IsStrictlyGE a],
          (∀ n, IsColimit ((galoisTower Ω h).abCocone (K.X n).X)) →
            Nonempty (IsColimit ((DerivedCategory.Q ⋙ G).mapCocone
              ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K)))) →
        ∀ {W} (φ : G.obj
          (R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
            Profinite.continuousMapRingObj T₀⟧).obj
              (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
                Profinite.continuousMapRingObj T₀⟧).obj A)) ⟶ W),
          (∀ k, G.map (derivedUnitTransport (Profinite.continuousMapRingObj T₀)
            (pullbackAction h _ specGaloisAction_comp (act k))
            (pullbackAction_fst h _ specGaloisAction_comp (act k))
            (pullbackAction_fst h _ specGaloisAction_comp (act k)) A) ≫ φ = φ) →
          G.map (R ≫ (CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.continuousMapRingObj T₀)
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app A) ≫ φ =
              φ := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ A hA
  choose F₀ hF₀ using hterms
  have hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) S)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) :=
    fun j M ↦ isIso_galois_card_smul_id T₀ j (hp j) M
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hcab := fun n ↦ (nonempty_isColimit_galoisUpperLowerCocone (Ω := Ω) h (K.X n).X
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)).some
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
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
  let R := R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
      Profinite.continuousMapRingObj T₀⟧).map
        (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
          Profinite.continuousMapRingObj T₀⟧).map e.inv) ≫
    Adjunction.derivedUnitRetraction
      (f := (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
        Profinite.continuousMapRingObj T₀⟧)
      (g := (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj T₀⟧) K a hK
      ((galoisTower Ω h).complexTrace (Profinite.continuousMapRingObj T₀) hd K hc) ≫ e.hom
  refine ⟨R, galoisTower_derivedUnit_retraction_of_iso (Profinite.continuousMapRingObj T₀)
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
    (galoisTower Ω h) hd K hc a hK e, ?_⟩
  intro Z G _ hG W φ hφ
  exact (galoisTower Ω h).map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK A e G (hG K a hcab).some
    (fun k ↦ pullbackAction h _ specGaloisAction_comp (act k))
    (fun k ↦ pullbackAction_fst h _ specGaloisAction_comp (act k)) hlift
    (fun j ↦ isIso_galois_card_smul_id T₀ j (hp j) W) φ hφ

private lemma exists_retraction_transfer
    {E : Type*} [Category E] {P Q : E} (α : P ⟶ Q)
    {R S : (Q ⟶ P) → Prop}
    (h : ∃ r, α ≫ r = 𝟙 _ ∧ R r) (hRS : ∀ r, R r → S r) :
    ∃ r, α ≫ r = 𝟙 _ ∧ S r := by
  obtain ⟨r, hr, hR⟩ := h
  exact ⟨r, hr, hRS r hR⟩

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]

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
  have := hasTensor₄ObjExt_mod.{u}
  have := hasGoodTensor₁₂Tensor_mod.{u}
  have := hasGoodTensorTensor₂₃_mod.{u}
  have := hasColimitsOfShape_int_mod.{u}
  have := preservesColimitsOfShape_int_curriedTensor_obj_mod.{u}
  have := preservesColimitsOfShape_int_curriedTensor_flip_obj_mod.{u}
  letI := galoisTensorModuleColimit
  letI := galoisTensorLeftColimit
  letI := galoisTensorRightColimit
  obtain ⟨R, hRC, hcoinv⟩ := exists_retraction_derivedUnit_galois_coinvariant_of_isColimit
    T₀ h Ω hp (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) hC act hact
  have hα := pullbackExchange_galoisLayerHom_app_eq_comp_unit
    (Profinite.continuousMapRingObj T₀) N h Ω C
  refine Exists.imp ?_ (exists_retraction_of_eq_comp_map_comp_of_coinvariant
    (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧))
    (A₀ := L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)
    (T := R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
      Profinite.continuousMapRingObj T₀⟧).obj
      (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
        Profinite.continuousMapRingObj T₀⟧).obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C)
    ((leftDerivedUpperStarId (Profinite.continuousMapRingObj T₀) X').app
      ((N.nearbyCycles (Profinite.continuousMapRingObj T₀)).obj C))
    (N.galoisLayerExchangeIso h Ω (Profinite.continuousMapRingObj T₀) C)
    ((CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))
    R hα hRC
      (fun k ↦ derivedUnitTransport (Profinite.continuousMapRingObj T₀)
        (pullbackAction h _ specGaloisAction_comp (act k))
        (pullbackAction_fst h _ specGaloisAction_comp (act k))
        (pullbackAction_fst h _ specGaloisAction_comp (act k))
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))
      (fun k ↦ N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))
      (fun k ↦ galoisLayerAut_autAction (Profinite.continuousMapRingObj T₀) N h Ω (act k) C))
  intro r hr
  refine ⟨hr.1, ?_⟩
  intro Z G _ hG W φ hφ
  refine hr.2 G (B := W) φ ?_ hφ
  intro φ' hφ'
  exact hcoinv (Z := Z) (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
    L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ G) hG φ' hφ'

private theorem tensor_property_of_coinvariant
    (T₀ : Type) [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
    (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
    {Z : Scheme.{u}}
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X))) (f' : Z ⟶ X')
    (r : ((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
      (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) ⟶
        (N.nearbyCycles (Profinite.continuousMapRingObj T₀)).obj C)
    {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hcoinv : ∀ {Z : Scheme.{u}}
      (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
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
            (Profinite.continuousMapRingObj T₀)).app C) ≫ φ = φ) :
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
  have := hasTensor₄ObjExt_mod.{u}
  have := hasGoodTensor₁₂Tensor_mod.{u}
  have := hasGoodTensorTensor₂₃_mod.{u}
  have := hasColimitsOfShape_int_mod.{u}
  have := preservesColimitsOfShape_int_curriedTensor_obj_mod.{u}
  have := preservesColimitsOfShape_int_curriedTensor_flip_obj_mod.{u}
  letI := galoisTensorModuleColimit
  letI := galoisTensorLeftColimit
  letI := galoisTensorRightColimit
  intro q V b hV W φ hφ
  refine hcoinv (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ tensorRight V ⋙
    DerivedCategory.homologyFunctor _ q) ?_ φ hφ
  intro K a _ hcab
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

set_option profiler true in
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
  have := hasTensor₄ObjExt_mod.{u}
  have := hasGoodTensor₁₂Tensor_mod.{u}
  have := hasGoodTensorTensor₂₃_mod.{u}
  have := hasColimitsOfShape_int_mod.{u}
  have := preservesColimitsOfShape_int_curriedTensor_obj_mod.{u}
  have := preservesColimitsOfShape_int_curriedTensor_flip_obj_mod.{u}
  letI := galoisTensorModuleColimit
  letI := galoisTensorLeftColimit
  letI := galoisTensorRightColimit
  exact exists_retraction_transfer
    (exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_isColimit T₀ N h Ω hp C hC act
      hact)
    (fun r hcoinv ↦ tensor_property_of_coinvariant T₀ N h Ω C f' r hcoinv act)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
