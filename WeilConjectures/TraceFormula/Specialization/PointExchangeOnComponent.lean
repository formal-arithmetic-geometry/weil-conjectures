/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationProperPoint
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnProperShape

/-!

# The exchange `ν_X` on objects pushed forward from a proper scheme

For `ν_X = pointCompactSupportExchangeOfOpenImmersion x u k'` (`u : X ⊂ Y` open, `Y` proper) and a
morphism of models `φ_g : M_B ⟶ 𝒳` over `g : B ⟶ X`, the identity of
`openPointExchangeAux_app_comp_aux_of_eq` on `g_* N`
(`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar`): `ν_X` read through the composition
isomorphisms, followed by the proper exchange of `B ⟶ 𝒳 ⟶ 𝒴 ⟶ 𝒫 ⟶ S` (`pointCompModelHom`),
is `Rp'_* h'_!(e'_u ∘ u'_!(χ_g))`, given the ambient identity `hC`.

The ingredients of `hC` are proved here: `ν_u` on pushforwards
(`NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app`), the identification of the `ν_h` of
`pointExchangeAux` with `lowerShriekExchangeOfInv` (`pointOpenExchange_app_eq`), and their
composition with `NearbyCyclesModel.Hom.compactSupportExchange_comp_app`
(`map_comp_exchange_aux`). The description of the mate `ν_u` on bounded constructible complexes
is `map_mateEquiv_inv_liftExchange`.

## Implementation notes

The statement is `∀ hC, type_of% (…)`. Discharging `hC` by
`map_comp_exchange_aux _ _ (lowerShriekExchangeOfInv_comp_app …) (pointOpenExchange_app_eq …)
(compactSupportExchange_comp_app … χ₀ hχ₀)` elaborates every piece except `hχ₀`: the right inverse
property of `χ₀` produced by unfolding `pointCompactSupportExchange` and the one expected by
`compactSupportExchange_comp_app` differ in instance terms of the ambient derived categories, and
their definitional equality times out (also at `maxHeartbeats 1000000`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- `ν_h` of `pointExchangeAux` is `lowerShriekExchangeOfInv` for the adjunction `𝟭 ⊣ L1`. -/
lemma pointOpenExchange_app_eq {DX DX' DP : Type*} [Category DX] [Category DX'] [Category DP]
    {ΨX : DX ⥤ DX'} {ΨP : DX ⥤ DP} {Dh : DX' ⥤ DP} {Lh : DP ⥤ DX'} {L1 : DX ⥤ DX}
    (adj : Dh ⊣ Lh) (e : 𝟭 DX ≅ L1) (α : ΨP ⋙ Lh ⟶ L1 ⋙ ΨX) [IsIso α] (Z : DX) :
    (pointOpenExchange adj e α).app Z =
      (lowerShriekExchangeOfInv (Adjunction.id.ofNatIsoRight e) adj α).app Z := by
  simp [pointOpenExchange, lowerShriekExchangeOfInv]

/-- Composing the identity `a ≫ b ≫ c = d ≫ e'` (`ν_u` on pushforwards) with the identity `k₂`
(`ν_Y` on pushforwards). -/
lemma map_comp_exchange_aux {C D E : Type*} [Category C] [Category D] [Category E] (Dh : C ⥤ D)
    (Rp : D ⥤ E) {x₀ x₁ x₂ x₃ y : C} {z w : D} {s t : E} {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂}
    {c : x₂ ⟶ x₃} {d : x₀ ⟶ y} {e' : y ⟶ x₃} (k₁ : a ≫ b ≫ c = d ≫ e') {ν₁ ν₂ : Dh.obj x₂ ⟶ z}
    (hν : ν₁ = ν₂) {eH : Dh.obj x₃ ⟶ w} {χ₀ : Rp.obj z ⟶ s} {r : s ⟶ t} {cj : Rp.obj w ⟶ t}
    (k₂ : Rp.map ν₂ ≫ χ₀ ≫ r = Rp.map (Dh.map c ≫ eH) ≫ cj) :
    Rp.map (Dh.map (a ≫ b)) ≫ Rp.map ν₁ ≫ χ₀ ≫ r = Rp.map (Dh.map (d ≫ e') ≫ eH) ≫ cj := by
  subst hν
  rw [k₂, ← Rp.map_comp_assoc, ← Dh.map_comp_assoc, Category.assoc, k₁]

end Abstract

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

section ModelExchange

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {B B' C C' P P' : Scheme.{u}} {MB : NearbyCyclesModel B B'} {MC : NearbyCyclesModel C C'}
  {MP : NearbyCyclesModel P P'} {g : B ⟶ C} {g' : B' ⟶ C'} {h : C ⟶ P} {h' : C' ⟶ P'}
  {hg : B ⟶ P} {hg' : B' ⟶ P'}

/-- **The exchange `ν_h` of an open immersion on pushforwards**, on the ambient derived
categories: `χ_{hg} ∘ Ψ_P(e) ∘ ν_h(g_* N) = e' ∘ h'_!(χ_g)` for `e = closedExtension`. -/
theorem NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app (φg : MB.Hom MC g g')
    (φh : MC.Hom MP h h') (φhg : MB.Hom MP hg hg') (w : g ≫ h = hg) (w' : g' ≫ h' = hg')
    (htot : φg.total ≫ φh.total = φhg.total) (hgen : φg.generic ≫ φh.generic = φhg.generic)
    {Dh : 𝔻(C) ⥤ 𝔻(P)} {Dh' : 𝔻(C') ⥤ 𝔻(P')} (adj : Dh ⊣ L((h)^*⟦Λ⟧))
    (adj' : Dh' ⊣ L((h')^*⟦Λ⟧)) [IsIso (φh.pullbackExchange Λ)]
    [Mono h] [WeaklyEtale h] [Mono h'] [WeaklyEtale h'] (N : 𝔻(B)) :
    (lowerShriekExchangeOfInv adj adj' (φh.pullbackExchange Λ)).app (R((g)_*⟦Λ⟧).obj N) ≫
        (MP.nearbyCycles Λ).map ((closedExtension adj w).app N) ≫
        (φhg.pushforwardExchange Λ).app N =
      Dh'.map ((φg.pushforwardExchange Λ).app N) ≫
        (closedExtension adj' w').app ((MB.nearbyCycles Λ).obj N) :=
  lowerShriekExchangeOfInv_app_comp_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ hg) (derivedUpperStarLowerStarAdjunction Λ g')
    (derivedUpperStarLowerStarAdjunction Λ hg') (leftDerivedUpperStarCompOfEq Λ w)
    (leftDerivedUpperStarCompOfEq Λ w') (φg.pullbackExchange Λ) (φh.pullbackExchange Λ)
    (φhg.pullbackExchange Λ) (φg.pullbackExchange_comp_app_of_eq Λ φh φhg w w' htot hgen)
    (φg.pushforwardExchange Λ) rfl (φhg.pushforwardExchange Λ) rfl (closedBaseChange Λ w)
    (map_closedBaseChange_app_comp_counit Λ w) (closedBaseChange Λ w')
    (map_closedBaseChange_app_comp_counit Λ w') adj adj' (closedExtension adj w)
    (unit_comp_closedExtension_app adj w) (closedExtension adj' w')
    (unit_comp_closedExtension_app adj' w') N

end ModelExchange

section Lift

variable {DA DA' DB DB' : Type*} [Category DA] [Category DA'] [Category DB] [Category DB']
  {PA : ObjectProperty DA} {PA' : ObjectProperty DA'} {PB : ObjectProperty DB}
  {PB' : ObjectProperty DB'} {DuS : DA ⥤ DB} {RuA : DB ⥤ DA} {DuS' : DA' ⥤ DB'}
  {RuA' : DB' ⥤ DA'} {ΨA : DA ⥤ DA'} {ΨB : DB ⥤ DB'}

/-- The mate of the inverse of a lifted pullback exchange (`NearbyCyclesModel.liftExchange`) for
the restrictions of adjunctions `u_! ⊣ u^*` to full subcategories is, through the inclusions, the
ambient `lowerShriekExchangeOfInv`. -/
lemma map_mateEquiv_inv_liftExchange (adj : DuS ⊣ RuA) (adj' : DuS' ⊣ RuA')
    (hL : ∀ Z : PA.FullSubcategory, PB ((PA.ι ⋙ DuS).obj Z))
    (hR : ∀ Z : PB.FullSubcategory, PA ((PB.ι ⋙ RuA).obj Z))
    (hL' : ∀ Z : PA'.FullSubcategory, PB' ((PA'.ι ⋙ DuS').obj Z))
    (hR' : ∀ Z : PB'.FullSubcategory, PA' ((PB'.ι ⋙ RuA').obj Z))
    (hA : ∀ Z : PA.FullSubcategory, PA' ((PA.ι ⋙ ΨA).obj Z))
    (hB : ∀ Z : PB.FullSubcategory, PB' ((PB.ι ⋙ ΨB).obj Z))
    (α : ΨB ⋙ RuA' ⟶ RuA ⋙ ΨA) [IsIso α]
    (hα : IsIso (NearbyCyclesModel.liftExchange α hB hA hR' hR)) (K : PA.FullSubcategory) :
    PB'.ι.map (((mateEquiv
        (adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
          (PB.liftCompιIso _ hL).symm (PA.liftCompιIso _ hR).symm)
        (adj'.restrictFullyFaithful PA'.fullyFaithfulι PB'.fullyFaithfulι
          (PB'.liftCompιIso _ hL').symm (PA'.liftCompιIso _ hR').symm)).symm
          (TwoSquare.mk _ _ _ _ (inv (NearbyCyclesModel.liftExchange α hB hA hR' hR)))).natTrans.app
          K) =
      (PB'.liftCompιIso _ hL').hom.app ((PA'.lift _ hA).obj K) ≫
        DuS'.map ((PA'.liftCompιIso _ hA).hom.app K) ≫
        (lowerShriekExchangeOfInv adj adj' α).app K.obj ≫
        ΨB.map ((PB.liftCompιIso _ hL).inv.app K) ≫
        (PB'.liftCompιIso _ hB).inv.app ((PB.lift _ hL).obj K) := by
  have f1 := Adjunction.map_restrictFullyFaithful_unit_app adj PA.fullyFaithfulι
    PB.fullyFaithfulι (PB.liftCompιIso _ hL).symm (PA.liftCompιIso _ hR).symm K
  have f2 := Adjunction.map_restrictFullyFaithful_counit_app adj' PA'.fullyFaithfulι
    PB'.fullyFaithfulι (PB'.liftCompιIso _ hL').symm (PA'.liftCompιIso _ hR').symm
    ((PB'.lift (PB.ι ⋙ ΨB) hB).obj ((PB.lift (PA.ι ⋙ DuS) hL).obj K))
  simp only [ObjectProperty.liftCompιIso, Iso.refl_symm, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp,
    ObjectProperty.ι_map] at f1 f2
  simp [mateEquiv, lowerShriekExchangeOfInv, ObjectProperty.hom_inv, ObjectProperty.liftCompιIso,
    f1, f2]

end Lift

section Point

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (x : RationalPoint X) (u : X ⟶ Y)
  [IsOpenImmersion u.left] (k' : Type u) [Field k'] [Algebra k k']

/-- The morphism of special fibres of the deformations along the open immersion `u`. -/
noncomputable abbrev pointSpecialMap :=
  deformationSpecialFibreMap u (ker_compatible_of_isOpenImmersion x u) k'

/-- The open immersion of deformation models along `u : X ⊂ Y` (ideals of `x` and `x ≫ u`). -/
noncomputable abbrev pointModelHom :=
  deformationModelHom u (ker_compatible_of_isOpenImmersion x u) k'

instance isIso_pointModelHom_pullbackExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsIso ((pointModelHom x u k').pullbackExchange Λ) :=
  isIso_deformationModelHom_pullbackExchange u _ k' Λ (ker_eq_comap_of_isOpenImmersion x u)

instance isOpenImmersion_pointSpecialMap : IsOpenImmersion (pointSpecialMap x u k').left :=
  have : IsOpenImmersion (pointModelHom x u k').total :=
    isOpenImmersion_deformationTotalMap u _ k' (ker_eq_comap_of_isOpenImmersion x u)
  MorphismProperty.of_isPullback (IsPullback.of_right (by
      rw [Over.w, deformationTotalMap_toTrait]
      exact (isPullback_deformationSpecialFibre X _ k').flip)
    (deformationSpecialFibreMap_toTotal u _ k')
    (isPullback_deformationSpecialFibre Y _ k').flip).flip this

variable [IsProper Y.hom] {B : Over (Spec (.of k))} {B' : Scheme.{u}}
  {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
  {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}

/-- The composite morphism of models `𝒟_B ⟶ 𝒳 ⟶ 𝒴 ⟶ 𝒫 ⟶ S` over the structure map of `B`. -/
noncomputable abbrev pointCompModelHom (φg : MB.Hom (deformationModel X x.left.ker k') g.left g') :=
  ((φg.comp (pointModelHom x u k')).comp (deformationToCompactifiedModelHom Y (x ≫ u) k')).comp
    (compactifiedToPointModelHom Y (x ≫ u) k')

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {ℓ : ℕ}
  [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]
  (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')

/-- **The exchange `ν_X` on pushforwards from `B`** (step (B) of Varshavsky's argument for `ν_X`):
the instance of `openPointExchangeAux_app_comp_aux_of_eq` for `ν_X`, `G = g_*`, `e_u, e'_u, e'_h`
(`closedExtension`) and the proper exchange of `pointCompModelHom`, given the ambient identity
`hC` (a consequence of `lowerShriekExchangeOfInv_comp_app` and
`compactSupportExchange_comp_app`, see the implementation notes). -/
theorem pointCompactSupportExchangeOfOpenImmersion_app_lowerStar
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∀ hC, type_of% (
      openPointExchangeAux_app_comp_aux_of_eq _ _ _ _ _ _ _
      (ObjectProperty.fullyFaithfulι _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (pointCompactSupportExchangeOfOpenImmersion (ℓ := ℓ) x u k') rfl
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ (pointSpecialMap x u k'))
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
        (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        ((pointModelHom x u k').pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
      (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
      (boundedConstructibleLowerStarCompatibility _ ℓ g)
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
      (closedExtension
        (Adjunction.id.ofNatIsoRight
          (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
      (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
      (φg.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
      (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        (rfl : g' ≫ (pointSpecialMap x u k').left = _))
      (closedExtension (openImmersionAdjunction ℓ (deformationSpecialFibreToCompactified Y (x ≫ u)
        k').left) rfl)
      (lowerStarCompOfEq rfl)
      ((pointCompModelHom x u k' φg).pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) N
      ⟨_, boundedConstructible_rightDerivedLowerStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ (g ≫ u)
        N.obj N.property⟩
      (Iso.refl _)
      hC
      ) :=
  fun hC ↦ openPointExchangeAux_app_comp_aux_of_eq _ _ _ _ _ _ _
      (ObjectProperty.fullyFaithfulι _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (pointCompactSupportExchangeOfOpenImmersion (ℓ := ℓ) x u k') rfl
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ (pointSpecialMap x u k'))
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
        (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        ((pointModelHom x u k').pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
      (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
      (boundedConstructibleLowerStarCompatibility _ ℓ g)
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
      (closedExtension
        (Adjunction.id.ofNatIsoRight
          (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
      (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
      (φg.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
      (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        (rfl : g' ≫ (pointSpecialMap x u k').left = _))
      (closedExtension (openImmersionAdjunction ℓ (deformationSpecialFibreToCompactified Y (x ≫ u)
        k').left) rfl)
      (lowerStarCompOfEq rfl)
      ((pointCompModelHom x u k' φg).pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) N
      ⟨_, boundedConstructible_rightDerivedLowerStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ (g ≫ u)
        N.obj N.property⟩
      (Iso.refl _)
      hC

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
