/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationTraceSpecialization
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityExchange
public import WeilConjectures.Tactic.MatchTactic
public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProper
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# Nearby cycles of the universal kernel, abstractly

Let `S_X`, `S_{X×X}` be nearby cycles on `X` and `X ×_S X`, `Δ` the diagonal, `K` a complex on the
generic fibre and `K' = S_X K`. With the external product comparison
`Π : K' ⊠ S_X D K ⟶ S_{X×X}(K ⊠ D K)` and the duality map `δ_K : S_X D K ⟶ D K'` invertible, put
`ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : S_{X×X}(K ⊠ D K) ⟶ K' ⊠ D K'`. The second identity of blueprint
`det-tf-sp-universal-kernel` is

`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`,

for the evaluation kernels `e_K : K ⊠ D K ⟶ RΔ_* ω_X`. This file proves it for abstract
adjunctions and monoidal closed categories:

* `CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange`: both sides are the adjoints of
  the same map, given the mate property of `χ_Δ` and the restriction of `ρ` to the diagonal;
* `CategoryTheory.map_comp_ev_eq_of_kunneth`: the restriction of `ρ` to the diagonal is the
  pairing `θ ∘ S(ev) ∘ μ` defining `δ_K`, given that `Δ_s^* Π` is the lax tensor map `μ_X` (the
  composition law and monoidality of the pullback exchanges, with `p_i ∘ Δ = 1`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {CP CX CP' CX' : Type*} [Category CP] [Category CX] [Category CP'] [Category CX']

/-- **The evaluation kernel identity**, abstractly: for adjunctions `U ⊣ R` (`Δ_η^* ⊣ RΔ_{η*}`)
and `U' ⊣ R'`, a transformation `α : S_P ⋙ U' ⟶ U ⋙ S_X` and its mate `χ : R ⋙ S_P ⟶ S_X ⋙ R'`,
if the restriction of `ρ : S_P P ⟶ P'` along `U'` composed with `ev'` is `α ≫ S_X(ev) ≫ θ`, then
`ρ` followed by the adjoint of `ev'` is `S_P` of the adjoint of `ev` followed by `χ` and
`R'(θ)`. -/
theorem comp_homEquiv_eq_map_homEquiv_comp_exchange {U : CP ⥤ CX} {R : CX ⥤ CP} (a : U ⊣ R)
    {U' : CP' ⥤ CX'} {R' : CX' ⥤ CP'} (a' : U' ⊣ R') {SP : CP ⥤ CP'} {SX : CX ⥤ CX'}
    (α : SP ⋙ U' ⟶ U ⋙ SX) (χ : R ⋙ SP ⟶ SX ⋙ R')
    (hχ : ∀ A, U'.map (χ.app A) ≫ a'.counit.app _ = α.app (R.obj A) ≫ SX.map (a.counit.app A))
    {P : CP} {P' : CP'} {ω : CX} {ω' : CX'} (ev : U.obj P ⟶ ω) (ev' : U'.obj P' ⟶ ω')
    (θ : SX.obj ω ⟶ ω') (ρ : SP.obj P ⟶ P')
    (hρ : U'.map ρ ≫ ev' = α.app P ≫ SX.map ev ≫ θ) :
    ρ ≫ a'.homEquiv _ _ ev' = SP.map (a.homEquiv _ _ ev) ≫ χ.app ω ≫ R'.map θ := by
  apply (a'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, hρ,
    Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Adjunction.counit_naturality, ← Category.assoc (U'.map (χ.app ω)),
    hχ]
  have hn := α.naturality (a.homEquiv _ _ ev)
  simp only [Functor.comp_map] at hn
  have he : U.map (a.homEquiv _ _ ev) ≫ a.counit.app ω = ev := by
    simp [Adjunction.homEquiv_unit]
  rw [Category.assoc, reassoc_of% hn, ← SX.map_comp_assoc, he]

/-- The cancellation of the identity isomorphisms `I : E ≅ 𝟭`, `I' : F ≅ 𝟭` around
`a = I'(Ψ C) ≫ Ψ(I⁻¹ C)` and `b = I'(Ψ E C) ≫ Ψ(I⁻¹(E C))` (the pullback exchanges of identity
morphisms of models). -/
lemma map_comp_comp_map_of_isoId {C D : Type*} [Category C] [Category D] (Ψ : C ⥤ D) {F : D ⥤ D}
    (I' : F ≅ 𝟭 D) {E : C ⥤ C} (I : E ≅ 𝟭 C) (C₀ : C) {a : F.obj (Ψ.obj C₀) ⟶ Ψ.obj (E.obj C₀)}
    {b : F.obj (Ψ.obj (E.obj C₀)) ⟶ Ψ.obj (E.obj (E.obj C₀))}
    (ha : a = I'.hom.app (Ψ.obj C₀) ≫ Ψ.map (I.inv.app C₀))
    (hb : b = I'.hom.app (Ψ.obj (E.obj C₀)) ≫ Ψ.map (I.inv.app (E.obj C₀))) :
    F.map a ≫ b ≫ Ψ.map (I.hom.app (E.obj C₀) ≫ I.hom.app C₀) =
      I'.hom.app (F.obj (Ψ.obj C₀)) ≫ I'.hom.app (Ψ.obj C₀) := by
  subst ha hb
  have hn := I'.hom.naturality (I'.hom.app (Ψ.obj C₀) ≫ Ψ.map (I.inv.app C₀))
  simp only [Functor.id_map, Functor.id_obj] at hn
  rw [Category.assoc, reassoc_of% hn]
  simp only [← Ψ.map_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Functor.id_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The algebra of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction`: from
the compatibility `h` of the Künneth map with pullbacks along the identity morphisms of models,
the naturality of the lax tensor maps and the cancellations `hcA`, `hcB` of the identity
isomorphisms. -/
lemma kunneth_retraction_aux {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (Ψ : C ⥤ D) {S X₁ eA eB fA fB gA gB hA hB : D}
    {c₀ cA cB A₂ B₂ A₁ B₁ A B : C} (P₁ : S ⟶ X₁) (P₂ : X₁ ⟶ Ψ.obj c₀) (δ : c₀ ⟶ cA ⊗ cB)
    (θA : cA ⟶ A₂) (θB : cB ⟶ B₂) (iA₁ : A₂ ⟶ A₁) (iA : A₁ ⟶ A) (iB₁ : B₂ ⟶ B₁) (iB : B₁ ⟶ B)
    (δ' : S ⟶ eA ⊗ eB) (θ'A : eA ⟶ fA) (θ'B : eB ⟶ fB) (La : fA ⟶ gA) (Lb : fB ⟶ gB)
    (a₁ : gA ⟶ Ψ.obj A₂) (b₁ : gB ⟶ Ψ.obj B₂) (μ₁ : Ψ.obj A₂ ⊗ Ψ.obj B₂ ⟶ Ψ.obj (A₂ ⊗ B₂))
    (μ : Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B))
    (hnat : (Ψ.map (iA₁ ≫ iA) ⊗ₘ Ψ.map (iB₁ ≫ iB)) ≫ μ = μ₁ ≫ Ψ.map ((iA₁ ≫ iA) ⊗ₘ (iB₁ ≫ iB)))
    (jA₁ : fA ⟶ hA) (jA : hA ⟶ Ψ.obj A) (jB₁ : fB ⟶ hB) (jB : hB ⟶ Ψ.obj B)
    (hcA : La ≫ a₁ ≫ Ψ.map (iA₁ ≫ iA) = jA₁ ≫ jA) (hcB : Lb ≫ b₁ ≫ Ψ.map (iB₁ ≫ iB) = jB₁ ≫ jB)
    (h : P₁ ≫ P₂ ≫ Ψ.map (δ ≫ (θA ⊗ₘ θB)) =
      δ' ≫ ((θ'A ≫ La) ⊗ₘ (θ'B ≫ Lb)) ≫ (a₁ ⊗ₘ b₁) ≫ μ₁)
    {mA : C} {mB : C} {mA' mB' : D} {gA₁ : cA ⟶ mA} {gA₂ : mA ⟶ A₁} {gB₁ : cB ⟶ mB}
    {gB₂ : mB ⟶ B₁} {g'A₁ : eA ⟶ mA'} {g'A₂ : mA' ⟶ hA} {g'B₁ : eB ⟶ mB'}
    {g'B₂ : mB' ⟶ hB}
    (ecA : θA ≫ iA₁ = gA₁ ≫ gA₂) (ecB : θB ≫ iB₁ = gB₁ ≫ gB₂)
    (ec'A : θ'A ≫ jA₁ = g'A₁ ≫ g'A₂) (ec'B : θ'B ≫ jB₁ = g'B₁ ≫ g'B₂) :
    P₁ ≫ P₂ ≫ Ψ.map (δ ≫ ((gA₁ ≫ gA₂ ≫ iA) ⊗ₘ (gB₁ ≫ gB₂ ≫ iB))) =
      δ' ≫ ((g'A₁ ≫ g'A₂ ≫ jA) ⊗ₘ (g'B₁ ≫ g'B₂ ≫ jB)) ≫ μ := by
  simp only [← Category.assoc gA₁, ← Category.assoc gB₁, ← Category.assoc g'A₁,
    ← Category.assoc g'B₁, ← ecA, ← ecB, ← ec'A, ← ec'B]
  have e : δ ≫ (((θA ≫ iA₁) ≫ iA) ⊗ₘ ((θB ≫ iB₁) ≫ iB)) =
      (δ ≫ (θA ⊗ₘ θB)) ≫ ((iA₁ ≫ iA) ⊗ₘ (iB₁ ≫ iB)) := by
    simp only [Category.assoc, tensorHom_comp_tensorHom]
  rw [e, Ψ.map_comp, reassoc_of% h, ← hnat]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, hcA, hcB]

variable [MonoidalCategory CX] [MonoidalCategory CX'] [MonoidalClosed CX']

/-- **The restriction of `ρ` to the diagonal**, abstractly: let `Km = Π : Q' ⟶ S_P P` be invertible,
`b : Q' ⟶ P'` (the map `1 ⊠ δ`), and `εP : U P ≅ K ⊗ N`, `εQ : U' Q' ≅ S_X K ⊗ N'`,
`εP' : U' P' ≅ S_X K ⊗ D'` the restrictions of the external products to the diagonal. If
`U'(Π)` is the lax tensor map `μ` along these identifications, `U'(b)` is `S_X K ◁ δ`, and `δ` is
the adjoint of the pairing `θ ∘ S_X(ev) ∘ μ`, then `U'(Π⁻¹ ≫ b)` followed by the evaluation is
`α ≫ S_X(εP ≫ ev) ≫ θ`. -/
theorem map_comp_ev_eq_of_kunneth {U : CP ⥤ CX} {U' : CP' ⥤ CX'} {SP : CP ⥤ CP'}
    {SX : CX ⥤ CX'} (α : SP ⋙ U' ⟶ U ⋙ SX) {P : CP} {Q' P' : CP'} {K N ω : CX} {N' : CX'}
    {ω' : CX'} (εP : U.obj P ≅ K ⊗ N) (εQ : U'.obj Q' ≅ SX.obj K ⊗ N')
    (εP' : U'.obj P' ≅ SX.obj K ⊗ (ihom (SX.obj K)).obj ω')
    (μ : SX.obj K ⊗ N' ⟶ SX.obj (K ⊗ N)) (ev : K ⊗ N ⟶ ω) (θ : SX.obj ω ⟶ ω')
    (δ : N' ⟶ (ihom (SX.obj K)).obj ω')
    (hδ : SX.obj K ◁ δ ≫ (ihom.ev (SX.obj K)).app ω' = μ ≫ SX.map ev ≫ θ)
    (Km : Q' ⟶ SP.obj P) [IsIso Km]
    (hKm : U'.map Km ≫ α.app P ≫ SX.map εP.hom = εQ.hom ≫ μ)
    (b : Q' ⟶ P') (hb : U'.map b ≫ εP'.hom = εQ.hom ≫ SX.obj K ◁ δ) :
    U'.map (inv Km ≫ b) ≫ εP'.hom ≫ (ihom.ev (SX.obj K)).app ω' =
      α.app P ≫ SX.map (εP.hom ≫ ev) ≫ θ := by
  rw [Functor.map_comp, Category.assoc, reassoc_of% hb, hδ]
  have h : U'.map (inv Km) ≫ εQ.hom ≫ μ = α.app P ≫ SX.map εP.hom := by
    rw [← hKm, ← U'.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% h, SX.map_comp, Category.assoc]

end CategoryTheory

open Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section KunnethRetraction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {P : NearbyCyclesModel Z Z'}
  {f₁ f₂ : Z ⟶ X} {f₁' f₂' : Z' ⟶ X'} {d : X ⟶ Z} {d' : X' ⟶ Z'}

/-- `leftDerivedUpperStarCompOfEq` is `leftDerivedUpperStarComp` up to `eqToHom`, inverse form. -/
lemma leftDerivedUpperStarCompOfEq_inv_app_eq {B₀ B₁ B₂ : Scheme.{u}} (p : B₀ ⟶ B₁) (q : B₁ ⟶ B₂)
    {pq : B₀ ⟶ B₂} (w : p ≫ q = pq)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology B₂) Ab.{u + 1}) (condensedRingObj Λ B₂))) :
    (leftDerivedUpperStarCompOfEq Λ w).inv.app K =
      (leftDerivedUpperStarComp Λ p q).inv.app K ≫ eqToHom (by rw [w]) := by
  subst w
  simp only [eqToHom_refl, Category.comp_id]
  rfl

set_option maxHeartbeats 1000000 in
-- the instance of the abstract computation is matched against the unfolded Künneth maps
/-- **The Künneth map along a common section of the two projections**: for morphisms of models
`φ₁ φ₂ : P ⟶ M` and `ρ : M ⟶ P` with `ρ ≫ φ₁ = ρ ≫ φ₂ = 𝟙`, the pullback of the Künneth map
`Π_{A,B}` along `ρ`, followed by the pullback exchange `α_ρ`, is the lax tensor map `μ_M`, through
the identifications `L(d)^* L(f_i)^* ≅ L(𝟙)^* ≅ 𝟭`. -/
lemma NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction
    (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom M f₂ f₂') (ρ : M.Hom P d d')
    (htot₁ : ρ.total ≫ φ₁.total = 𝟙 _) (hgen₁ : ρ.generic ≫ φ₁.generic = 𝟙 _)
    (htot₂ : ρ.total ≫ φ₂.total = 𝟙 _) (hgen₂ : ρ.generic ≫ φ₂.generic = 𝟙 _)
    (hb₁ : d ≫ f₁ = 𝟙 X) (hs₁ : d' ≫ f₁' = 𝟙 X') (hb₂ : d ≫ f₂ = 𝟙 X) (hs₂ : d' ≫ f₂' = 𝟙 X')
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    L((d')^*⟦Λ⟧).map (NearbyCyclesModel.kunnethMap Λ φ₁ φ₂ A B) ≫
        (ρ.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫
        (M.nearbyCycles Λ).map (Functor.OplaxMonoidal.δ L((d)^*⟦Λ⟧) _ _ ≫
          (((leftDerivedUpperStarComp Λ d f₁).inv.app A ≫ eqToHom (by rw [hb₁]) ≫
              (leftDerivedUpperStarId Λ X).hom.app A) ⊗ₘ
            ((leftDerivedUpperStarComp Λ d f₂).inv.app B ≫ eqToHom (by rw [hb₂]) ≫
              (leftDerivedUpperStarId Λ X).hom.app B))) =
      Functor.OplaxMonoidal.δ L((d')^*⟦Λ⟧) _ _ ≫
        (((leftDerivedUpperStarComp Λ d' f₁').inv.app _ ≫ eqToHom (by rw [hs₁]) ≫
            (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A)) ⊗ₘ
          ((leftDerivedUpperStarComp Λ d' f₂').inv.app _ ≫ eqToHom (by rw [hs₂]) ≫
            (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj B))) ≫
        M.tensorMap Λ A B := by
  have h := NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂
    (NearbyCyclesModel.Hom.id M) (NearbyCyclesModel.Hom.id M) (NearbyCyclesModel.Hom.id M)
    (NearbyCyclesModel.Hom.id M) ρ
    (by rw [NearbyCyclesModel.Hom.id_total, Category.comp_id, htot₁])
    (by rw [NearbyCyclesModel.Hom.id_generic, Category.comp_id, hgen₁])
    (by rw [NearbyCyclesModel.Hom.id_total, Category.comp_id, htot₂])
    (by rw [NearbyCyclesModel.Hom.id_generic, Category.comp_id, hgen₂])
    (by rw [Category.comp_id, hb₁]) (by rw [Category.comp_id, hs₁])
    (by rw [Category.comp_id, hb₂]) (by rw [Category.comp_id, hs₂]) A B
  -- the identity components
  have hc := fun C ↦ CategoryTheory.map_comp_comp_map_of_isoId (M.nearbyCycles Λ)
    (leftDerivedUpperStarId Λ X') (leftDerivedUpperStarId Λ X) C
    (NearbyCyclesModel.Hom.id_pullbackExchange_app Λ M C)
    (NearbyCyclesModel.Hom.id_pullbackExchange_app Λ M _)
  simp only [NearbyCyclesModel.kunnethMap] at h ⊢
  have hnat := NearbyCyclesModel.tensorMap_natural Λ M
    ((leftDerivedUpperStarId Λ X).hom.app (L((𝟙 X)^*⟦Λ⟧).obj A) ≫
      (leftDerivedUpperStarId Λ X).hom.app A)
    ((leftDerivedUpperStarId Λ X).hom.app (L((𝟙 X)^*⟦Λ⟧).obj B) ≫
      (leftDerivedUpperStarId Λ X).hom.app B)
  have hcA := hc A
  have hcB := hc B
  have ecA := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hb₁ A).trans
    (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d f₁ hb₁ A)
  have ecB := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hb₂ B).trans
    (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d f₂ hb₂ B)
  have ec'A := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hs₁
    ((M.nearbyCycles Λ).obj A)).trans (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d' f₁' hs₁ _)
  have ec'B := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hs₂
    ((M.nearbyCycles Λ).obj B)).trans (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d' f₂' hs₂ _)
  apply_by_match CategoryTheory.kunneth_retraction_aux [h := h, hnat := hnat, hcA := hcA,
    hcB := hcB, ecA := ecA, ecB := ecB, ec'A := ec'A, ec'B := ec'B]

end KunnethRetraction

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k).Prime] in
/-- The deformation to the normal cone of `x` is a trait model over the base. -/
lemma isTraitModelOfBase_deformationModel :
    (deformationModel X x.left.ker k').IsTraitModelOfBase k
      (deformationTotalToTrait X x.left.ker k') (deformationGenericToPoint X x.left.ker k') :=
  .of_isPullback ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      isPullback_deformationSpecialFibre X _ k'⟩ ⟨deformationTotalToBase X _ k', rfl,
        deformationTotalToBase_hom X _ k'⟩
    (isPullback_deformationModel_ε k' x.left.ker)

variable (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)

/-- The duality map `δ_K : Sp_{X,x}(D K) ⟶ D Sp_{X,x}(K)` of the specialization (blueprint
`sk-prop-tf-nearby-duality-foundation`), for a family of dualizing maps `D`. -/
noncomputable def specializationDualityMap (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specialization k' x).obj (verdierDual ℓ K) ⟶ verdierDual ℓ ((specialization k' x).obj K) :=
  NearbyCyclesModel.nearbyDualityMap ℓ D (isTraitModelOfBase_deformationModel k' x) K

/-- The comparison `ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : Ψ_{X×X}(K ⊠ D K) ⟶ Ψ_X K ⊠ D Ψ_X K` of the universal
kernels (blueprint `det-tf-sp-universal-kernel`). -/
noncomputable def universalKernelSpecialization
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specializationProd k' x).obj (externalProduct ℓ K (verdierDual ℓ K)) ⟶
      externalProduct ℓ ((specialization k' x).obj K)
        (verdierDual ℓ ((specialization k' x).obj K)) :=
  inv (specializationKunnethMap k' x K (verdierDual ℓ K)) ≫
    _ ◁ (boundedConstructibleUpperStar _ ℓ _).map (specializationDualityMap k' x D K)

/-- The restriction of the Künneth map `Π_{K,L}` to the diagonal is the lax tensor map `μ_X` of
the specialization, through the pullback exchange `α_Δ` and the identifications
`LΔ^*(M ⊠ N) ≅ M ⊗ N` (the composition law and monoidality of the pullback exchanges, with
`p_i ∘ Δ = 1`). -/
lemma map_specializationKunnethMap_comp_pullbackExchange
    (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
        (specializationKunnethMap k' x K L) ≫
      ((deformationDiagModelHom X x.left.ker k').boundedConstructiblePullbackExchange ℓ
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k'))
        (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
          (deformationProdModel X x.left.ker X x.left.ker k')
          (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
          (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))).app
        (externalProduct ℓ K L) ≫
      (specialization k' x).map (diagUpperStarExternalProductIso ℓ K L).hom =
    (diagUpperStarExternalProductIso ℓ _ _).hom ≫
      NearbyCyclesModel.boundedConstructibleTensorMap
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k')) K L := by
  -- The ambient content of this identity is
  -- `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction`, at the projections
  -- and the diagonal of the deformation models. What is missing is its transport to bounded
  -- constructible complexes: after `ObjectProperty.hom_ext` and the ambient forms of the
  -- comparison isomorphisms, the two sides differ only in the spelling of objects (e.g.
  -- `(externalProduct ℓ K L).obj` and `Lp₁^* K.obj ⊗ Lp₂^* L.obj`), but neither the unifier nor
  -- the kernel identifies them within the heartbeat budget.
  sorry

set_option maxHeartbeats 1000000 in
-- matching the abstract statements against the concrete functors
/-- **Nearby cycles of the universal kernel**, second identity (blueprint
`det-tf-sp-universal-kernel`): for `ρ = (1 ⊠ δ_K) ∘ Π⁻¹`, the evaluation kernels satisfy
`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`, with `K' = Sp_{X,x}(K)`. -/
theorem universalKernelSpecialization_comp_evaluationKernel
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    universalKernelSpecialization k' x D K ≫ evaluationKernel ℓ ((specialization k' x).obj K) =
      (specializationProd k' x).map (evaluationKernel ℓ K) ≫
        (Correspondence.IsContractingAt.diagPushforwardExchange ℓ X k' x).app
          (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
          (D.θ (isTraitModelOfBase_deformationModel k' x)) := by
  have hρ := CategoryTheory.map_comp_ev_eq_of_kunneth
    ((deformationDiagModelHom X x.left.ker k').boundedConstructiblePullbackExchange ℓ
      ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel X x.left.ker k')
        (deformationModel_exists_comp_ε X x.left.ker k'))
      (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
        (deformationProdModel X x.left.ker X x.left.ker k')
        (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
        (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k')))
    (diagUpperStarExternalProductIso ℓ K (verdierDual ℓ K))
    (diagUpperStarExternalProductIso ℓ ((specialization k' x).obj K)
      ((specialization k' x).obj (verdierDual ℓ K)))
    (diagUpperStarExternalProductIso ℓ ((specialization k' x).obj K)
      (verdierDual ℓ ((specialization k' x).obj K)))
    (NearbyCyclesModel.boundedConstructibleTensorMap
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k')) K (verdierDual ℓ K))
    ((ihom.ev K).app (dualizingComplex' ℓ X)) (D.θ (isTraitModelOfBase_deformationModel k' x))
    (specializationDualityMap k' x D K)
    (Verdier.whiskerLeft_nearbyDualityMap_comp_ev _ _ K)
    (specializationKunnethMap k' x K (verdierDual ℓ K))
    (map_specializationKunnethMap_comp_pullbackExchange k' x K (verdierDual ℓ K))
    (_ ◁ (boundedConstructibleUpperStar _ ℓ _).map (specializationDualityMap k' x D K))
    (diagUpperStarExternalProductIso_hom_naturality_right ℓ _ (specializationDualityMap k' x D K))
  have hχ :=
    NearbyCyclesModel.Hom.map_boundedConstructiblePushforwardExchange_app_comp_counit_app (ℓ := ℓ)
    (deformationDiagModelHom X x.left.ker k')
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
  unfold universalKernelSpecialization evaluationKernel
  apply_by_match CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange [hχ := hχ, hρ := hρ]

end AlgebraicGeometry.ProEtale.CondensedRing
