/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-!

# The action of self-maps of models and the exchange morphisms

Let `τ : M ⟶ N` be a morphism of models over `f, f'`, and `s : M ⟶ M`, `s' : N ⟶ N` morphisms of
models over the identities with `s ≫ τ = τ ≫ s'` on total spaces and geometric generic fibres.
Then the exchanges of `τ` intertwine the actions of `s` and `s'` on nearby cycles
(`NearbyCyclesModel.Hom.autAction`):

* `α_τ(C) ≫ ρ(s)(Lf^* C) = Lf'^*(ρ(s')(C)) ≫ α_τ(C)` for the pullback exchange
  (`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`);
* `χ_τ(E) ≫ Rf'_*(ρ(s)(E)) = ρ(s')(Rf_* E) ≫ χ_τ(E)` for the pushforward exchange
  (`NearbyCyclesModel.Hom.pushforwardExchange_app_comp_map_autAction`).

Moreover the action of a self-map fixes the specialization unit
(`NearbyCyclesModel.Hom.unit_comp_autAction`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- A transformation `χ : R₁ ⋙ G ⟶ H ⋙ R₂` with the counit property of the mate of
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` intertwines endomorphisms `β` of `H` (natural) and `β'` of `G` which
`α` intertwines:
if `α(B) ≫ β(L₁ B) = L₂(β'(B)) ≫ α(B)` for all `B`, then
`χ(E) ≫ R₂(β(E)) = β'(R₁ E) ≫ χ(E)`. -/
lemma comp_map_of_comp_of_map_comp_counit {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂] {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (χ : ∀ E, G.obj (R₁.obj E) ⟶ R₂.obj (H.obj E))
    (hχ : ∀ E, L₂.map (χ E) ≫ adj₂.counit.app (H.obj E) =
      α.app (R₁.obj E) ≫ H.map (adj₁.counit.app E))
    (β : ∀ E, H.obj E ⟶ H.obj E) (hβ : ∀ {E E' : D₁} (g : E ⟶ E'), β E ≫ H.map g = H.map g ≫ β E')
    (β' : ∀ B, G.obj B ⟶ G.obj B) (h : ∀ B, α.app B ≫ β (L₁.obj B) = L₂.map (β' B) ≫ α.app B)
    (E : D₁) :
    χ E ≫ R₂.map (β E) = β' (R₁.obj E) ≫ χ E := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, L₂.map_comp, L₂.map_comp,
    Category.assoc, Category.assoc, adj₂.counit_naturality, ← Category.assoc,
    hχ, Category.assoc]
  erw [← hβ]
  rw [← Category.assoc, h, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- **Right unit law** for the composition isomorphisms transported along `p ≫ 𝟙 Y = pq`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {p pq : X ⟶ Y} (h : p ≫ 𝟙 Y = pq)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompOfEq Λ h).hom.app K ≫
        L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) =
      eqToHom (by rw [← h, Category.comp_id]; rfl) := by
  subst h
  exact leftDerivedUpperStarComp_id_right_app Λ p K

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

/-- The diagram chase behind `NearbyCyclesModel.Hom.pullbackExchange_app_of_comp_left`. -/
private lemma comp_autAction_aux {D : Type*} [Category D] {P Q Q₁ R R₁ R₂ : D}
    {χ : P ⟶ Q} {c : Q ⟶ Q₁} {i : Q₁ ⟶ Q} {c' j' : P ⟶ R} {i' : R ⟶ P} {τ : P ⟶ R₂}
    {Lτ : R ⟶ R₁} {j'' : R₂ ⟶ R₁} {a : R₁ ⟶ Q₁} (hc : c ≫ i = 𝟙 Q)
    (he : χ ≫ c = c' ≫ Lτ ≫ a) (hc' : c' ≫ i' = 𝟙 P) (hij : i' ≫ j' = 𝟙 R)
    (hnat : τ ≫ j'' = j' ≫ Lτ) :
    χ = τ ≫ j'' ≫ a ≫ i := by
  obtain rfl : c' = j' := by
    rw [← Category.comp_id c', ← hij, ← Category.assoc, hc', Category.id_comp]
  rw [reassoc_of% hnat, ← reassoc_of% he, hc, Category.comp_id]

/-- The diagram chase behind `NearbyCyclesModel.Hom.pullbackExchange_app_of_comp_right`, for
functors `ΨN : DY ⥤ DY'`, `ΨM : DX ⥤ DX'`, `Lf`, `Lf'` and `I ≅ 𝟭`, `I' ≅ 𝟭`. -/
private lemma comp_autAction_aux' {DY DY' DX DX' : Type*} [Category DY] [Category DY']
    [Category DX] [Category DX'] {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'} {Lf : DY ⥤ DX}
    {Lf' : DY' ⥤ DX'} {I : DY ⥤ DY} {I' : DY' ⥤ DY'} (eY : I ≅ 𝟭 DY) (eY' : I' ≅ 𝟭 DY')
    (ατ αχ : ΨN ⋙ Lf' ⟶ Lf ⋙ ΨM) (αs : ΨN ⋙ I' ⟶ I ⋙ ΨN) (c : Lf ≅ I ⋙ Lf)
    (c' : Lf' ≅ I' ⋙ Lf') (C : DY)
    (he : αχ.app C ≫ ΨM.map (c.hom.app C) =
      c'.hom.app (ΨN.obj C) ≫ Lf'.map (αs.app C) ≫ ατ.app (I.obj C))
    (hc : c.hom.app C ≫ Lf.map (eY.hom.app C) = 𝟙 _)
    (hc' : c'.hom.app (ΨN.obj C) ≫ Lf'.map (eY'.hom.app (ΨN.obj C)) = 𝟙 _) :
    αχ.app C = Lf'.map (eY'.inv.app (ΨN.obj C) ≫ αs.app C ≫ ΨN.map (eY.hom.app C)) ≫
      ατ.app C := by
  have hc'' : c'.hom.app (ΨN.obj C) = Lf'.map (eY'.inv.app (ΨN.obj C)) := by
    calc c'.hom.app (ΨN.obj C)
        = c'.hom.app (ΨN.obj C) ≫ Lf'.map (eY'.hom.app _ ≫ eY'.inv.app _) := by simp
      _ = (c'.hom.app (ΨN.obj C) ≫ Lf'.map (eY'.hom.app _)) ≫ Lf'.map (eY'.inv.app _) := by
        rw [Lf'.map_comp, Category.assoc]
      _ = _ := by rw [hc', Category.id_comp]
  have hnat := ατ.naturality (eY.hom.app C)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hnat
  calc αχ.app C = αχ.app C ≫ ΨM.map (c.hom.app C ≫ Lf.map (eY.hom.app C)) := by
        rw [hc]
        simp
    _ = (αχ.app C ≫ ΨM.map (c.hom.app C)) ≫ ΨM.map (Lf.map (eY.hom.app C)) := by
        rw [ΨM.map_comp, Category.assoc]
    _ = _ := by
        rw [he, hc'', Category.assoc, Category.assoc, ← hnat]
        simp

/-- The pullback exchange of a morphism of models `χ` which is `s ≫ τ` on total spaces and
geometric generic fibres, for a self-map `s` over the identities, is `α_τ` followed by the action
of `s`: `α_χ(C) = α_τ(C) ≫ ρ(s)(Lf^* C)`. -/
lemma pullbackExchange_app_of_comp_left (s : M.Hom M (𝟙 X) (𝟙 X')) (τ χ : M.Hom N f f')
    (htot : s.total ≫ τ.total = χ.total) (hgen : s.generic ≫ τ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (χ.pullbackExchange Λ).app C =
      (τ.pullbackExchange Λ).app C ≫ s.autAction Λ (L((f)^*⟦Λ⟧).obj C) := by
  have e := s.pullbackExchange_comp_app_of_eq Λ τ χ (Category.id_comp f) (Category.id_comp f')
    htot hgen C
  have hc := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp f) C
  have hc' := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp f') ((N.nearbyCycles Λ).obj C)
  rw [eqToHom_refl] at hc hc'
  have hΨ := congrArg (M.nearbyCycles Λ).map hc
  rw [(M.nearbyCycles Λ).map_comp, (M.nearbyCycles Λ).map_id] at hΨ
  exact comp_autAction_aux hΨ e hc' ((leftDerivedUpperStarId Λ X').hom_inv_id_app _)
    ((leftDerivedUpperStarId Λ X').inv.naturality _)

/-- The pullback exchange of a morphism of models `χ` which is `τ ≫ s'` on total spaces and
geometric generic fibres, for a self-map `s'` over the identities, is the action of `s'` followed
by `α_τ`: `α_χ(C) = Lf'^*(ρ(s')(C)) ≫ α_τ(C)`. -/
lemma pullbackExchange_app_of_comp_right (s' : N.Hom N (𝟙 Y) (𝟙 Y')) (τ χ : M.Hom N f f')
    (htot : τ.total ≫ s'.total = χ.total) (hgen : τ.generic ≫ s'.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (χ.pullbackExchange Λ).app C =
      L((f')^*⟦Λ⟧).map (s'.autAction Λ C) ≫ (τ.pullbackExchange Λ).app C := by
  exact comp_autAction_aux' (leftDerivedUpperStarId Λ Y) (leftDerivedUpperStarId Λ Y')
    (τ.pullbackExchange Λ) (χ.pullbackExchange Λ) (s'.pullbackExchange Λ)
    (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f))
    (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f')) C
    (τ.pullbackExchange_comp_app_of_eq Λ s' χ (Category.comp_id f) (Category.comp_id f') htot
      hgen C)
    ((leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId Λ
      (Category.comp_id f) C).trans (eqToHom_refl _ _))
    ((leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId Λ
      (Category.comp_id f') _).trans (eqToHom_refl _ _))

/-- **The pullback exchange intertwines the actions of self-maps**: if `s ≫ τ = τ ≫ s'` on total
spaces and geometric generic fibres, then `α_τ(C) ≫ ρ(s)(Lf^* C) = Lf'^*(ρ(s')(C)) ≫ α_τ(C)`. -/
lemma pullbackExchange_app_comp_autAction_of_comm (τ : M.Hom N f f')
    (s : M.Hom M (𝟙 X) (𝟙 X')) (s' : N.Hom N (𝟙 Y) (𝟙 Y')) (htot : s.total ≫ τ.total = τ.total ≫ s'.total)
    (hgen : s.generic ≫ τ.generic = τ.generic ≫ s'.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (τ.pullbackExchange Λ).app C ≫ s.autAction Λ (L((f)^*⟦Λ⟧).obj C) =
      L((f')^*⟦Λ⟧).map (s'.autAction Λ C) ≫ (τ.pullbackExchange Λ).app C := by
  let χ : M.Hom N f f' :=
    { total := τ.total ≫ s'.total
      generic := τ.generic ≫ s'.generic
      comm_j := (τ.comp s').comm_j
      comm_i := by simpa using (τ.comp s').comm_i
      comm_ε := by simpa using (τ.comp s').comm_ε }
  rw [← pullbackExchange_app_of_comp_left Λ s τ χ htot hgen,
    ← pullbackExchange_app_of_comp_right Λ s' τ χ rfl rfl]

/-- **The pushforward exchange intertwines the actions of self-maps**: if `s ≫ τ = τ ≫ s'` on
total spaces and geometric generic fibres, then `χ_τ(E) ≫ Rf'_*(ρ(s)(E)) = ρ(s')(Rf_* E) ≫ χ_τ(E)`.
-/
lemma pushforwardExchange_app_comp_map_autAction (τ : M.Hom N f f') (s : M.Hom M (𝟙 X) (𝟙 X'))
    (s' : N.Hom N (𝟙 Y) (𝟙 Y')) (htot : s.total ≫ τ.total = τ.total ≫ s'.total)
    (hgen : s.generic ≫ τ.generic = τ.generic ≫ s'.generic)
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (τ.pushforwardExchange Λ).app E ≫ R((f')_*⟦Λ⟧).map (s.autAction Λ E) =
      s'.autAction Λ (R((f)_*⟦Λ⟧).obj E) ≫ (τ.pushforwardExchange Λ).app E := by
  exact comp_map_of_comp_of_map_comp_counit (G := N.nearbyCycles Λ) (H := M.nearbyCycles Λ)
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (τ.pullbackExchange Λ)
    (fun E ↦ (τ.pushforwardExchange Λ).app E) (τ.map_pushforwardExchange_app_comp_counit_app Λ)
    (s.autAction Λ)
    (s.autAction_naturality Λ) (s'.autAction Λ)
    (τ.pullbackExchange_app_comp_autAction_of_comm Λ s s' htot hgen) E

/-- The diagram chase behind `NearbyCyclesModel.Hom.unit_comp_autAction`. -/
private lemma unit_comp_autAction_aux {D D' : Type*} [Category D] [Category D'] (Ψ : D ⥤ D')
    {I : D ⥤ D} {I' : D' ⥤ D'} (e : I ≅ 𝟭 D) (e' : I' ≅ 𝟭 D') {A : D} {B : D'}
    (u : B ⟶ Ψ.obj A) (α : Ψ ⋙ I' ⟶ I ⋙ Ψ)
    (h : I'.map u ≫ α.app A = (e'.app B).hom ≫ u ≫ Ψ.map (e.app A).inv) :
    u ≫ e'.inv.app (Ψ.obj A) ≫ α.app A ≫ Ψ.map (e.hom.app A) = u := by
  have hn := e'.inv.naturality u
  simp only [Functor.id_map, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc, reassoc_of% h]
  simp

/-- **The action of a self-map fixes the specialization unit**: `σ_M ≫ ρ(s)(Λ) = σ_M`. -/
lemma unit_comp_autAction (s : M.Hom M (𝟙 X) (𝟙 X')) :
    M.unit Λ ≫ s.autAction Λ (𝟙_ _) = M.unit Λ := by
  have h := s.map_unit_comp_pullbackExchange_app Λ
  have hU : leftDerivedUpperStarUnitIso Λ (𝟙 X) = (leftDerivedUpperStarId Λ X).app (𝟙_ _) :=
    Iso.ext (leftDerivedUpperStarId_hom_app_unit Λ X).symm
  have hU' : leftDerivedUpperStarUnitIso Λ (𝟙 X') = (leftDerivedUpperStarId Λ X').app (𝟙_ _) :=
    Iso.ext (leftDerivedUpperStarId_hom_app_unit Λ X').symm
  rw [hU, hU'] at h
  exact unit_comp_autAction_aux (M.nearbyCycles Λ) (leftDerivedUpperStarId Λ X)
    (leftDerivedUpperStarId Λ X') (M.unit Λ) (s.pullbackExchange Λ) h

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
