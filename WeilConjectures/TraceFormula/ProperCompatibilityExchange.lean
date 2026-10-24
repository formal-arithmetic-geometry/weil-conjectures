/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperPushforwardKernel

/-!

# Exchange lemmas for the proper pushforward of the trace class

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` (blueprint
`def-trf-coefficient-pushforward`), with `q = f × f`:

* the kernel class of `[f, g]_! u` is the transported kernel class of `u`
  (`Correspondence.ProperPushforwardDiagram.kernelClass_pushforward`, blueprint
  `lem-trf-trace-source-exchange`);
* the evaluation kernels are exchanged by the kernel pushforward
  (`Correspondence.ProperPushforwardDiagram.kernelPushforward_comp_evaluationKernel`, blueprint
  `lem-trf-trace-map-exchange`, (1));
* the support isomorphisms are exchanged by the exchange map of the support square
  (`Correspondence.ProperPushforwardDiagram.lowerStar_map_supportIso_comp_exchange`, blueprint
  `lem-trf-trace-map-exchange`, (2)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- The exceptional adjoint of a map through a mate: for an exchange `E = mate(Ξ)` of
`Ξ : G ⋙ L₂ ⟶ L₁ ⋙ H` along `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, the `L₂ ⊣ R₂`-adjoint of
`L₂ η ≫ Ξ ≫ H φ♭ ≫ ψ` is `η ≫ G φ ≫ E ≫ R₂ ψ`. -/
lemma Adjunction.homEquiv_comp_mateEquiv {CC CD CP CQ : Type*} [Category CC] [Category CD]
    [Category CP] [Category CQ] {L₁ : CC ⥤ CP} {R₁ : CP ⥤ CC} {L₂ : CD ⥤ CQ} {R₂ : CQ ⥤ CD}
    {G : CC ⥤ CD} {H : CP ⥤ CQ} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (Ξ : G ⋙ L₂ ⟶ L₁ ⋙ H)
    {A : CD} {A' : CC} {M : CP} {N : CQ} (η : A ⟶ G.obj A') (φ : A' ⟶ R₁.obj M)
    (ψ : H.obj M ⟶ N) :
    adj₂.homEquiv _ _ (L₂.map η ≫ Ξ.app A' ≫ H.map ((adj₁.homEquiv _ _).symm φ) ≫ ψ) =
      η ≫ G.map φ ≫ (mateEquiv adj₁ adj₂ Ξ).app M ≫ R₂.map ψ := by
  rw [← Equiv.eq_symm_apply, Adjunction.homEquiv_counit]
  have hc := mateEquiv_counit adj₁ adj₂ Ξ M
  have hn := Ξ.naturality φ
  have hε := adj₂.counit.naturality ψ
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc hn hε
  simp only [Functor.map_comp, Category.assoc, Adjunction.homEquiv_counit]
  rw [hε, reassoc_of% hc, reassoc_of% hn]

/-- Assembly of the transport along `g` (blueprint `thm-trf-trace-proper-compatibility`,
Step 3) from the adjunction description of `T ≫ ζ` and the exchange of the supports. -/
lemma Adjunction.homEquiv_comp_mateEquiv_of_eq {CC CD CP CQ : Type*} [Category CC]
    [Category CD] [Category CP] [Category CQ] {L₁ : CC ⥤ CP} {R₁ : CP ⥤ CC} {L₂ : CD ⥤ CQ}
    {R₂ : CQ ⥤ CD} {G : CC ⥤ CD} {H : CP ⥤ CQ} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (Ξ : G ⋙ L₂ ⟶ L₁ ⋙ H) {A : CD} {A' Z : CC} {M' M : CP} {N : CQ}
    (η : A ⟶ G.obj A') (κ : L₁.obj A' ⟶ M') (δ : M' ⟶ M) (ψ : H.obj M ⟶ N) (T : A' ⟶ Z)
    (ζ : Z ⟶ R₁.obj M) (hc : adj₁.homEquiv _ _ (κ ≫ δ) = T ≫ ζ) (rhs : G.obj Z ⟶ R₂.obj N)
    (E : R₁ ⋙ G ⟶ H ⋙ R₂) (hE : E = mateEquiv adj₁ adj₂ Ξ)
    (h : G.map ζ ≫ E.app M ≫ R₂.map ψ = rhs) :
    adj₂.homEquiv _ _ (L₂.map η ≫ Ξ.app A' ≫ H.map κ ≫ H.map δ ≫ ψ) =
      η ≫ G.map T ≫ rhs := by
  have hκ : κ ≫ δ = (adj₁.homEquiv _ _).symm (T ≫ ζ) := by rw [← hc, Equiv.symm_apply_apply]
  subst hE
  rw [← H.map_comp_assoc, hκ, Adjunction.homEquiv_comp_mateEquiv, G.map_comp, Category.assoc]
  exact congrArg (fun t ↦ η ≫ G.map T ≫ t) h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

/-- The trace morphism followed by the support isomorphism is the exceptional adjoint of the
kernel class followed by the evaluation kernel (blueprint `thm-trf-trace-proper-compatibility`,
Step 1). -/
lemma mate_comp_traceMap_comp_supportIso (c : Correspondence ℓ K) (F : c.FixedLocus) :
    c.mate ≫ c.traceMap F ≫ F.supportIso.hom =
      (boundedConstructibleUpperShriekAdjunction _ ℓ c.support).homEquiv _ _
        (c.kernelClass ≫ evaluationKernel ℓ K) := by
  rw [traceMap_eq, Adjunction.homEquiv_naturality_right, kernelClass,
    Equiv.apply_symm_apply]
  simp

end Correspondence

namespace Correspondence.ProperPushforwardDiagram


variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

/-- The support square `g ≫ b = c ≫ (f × f)` of a proper pushforward diagram. -/
lemma g_comp_support : P.g ≫ P.pushforward.support = c.support ≫ prod.map P.f P.f := by
  apply prod.hom_ext <;> simp [Correspondence.support, P.w₁, P.w₂]

omit [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The diagonal square `Δ_X ≫ (f × f) = f ≫ Δ_Y`. -/
lemma diag_comp_prodMap : diag X ≫ prod.map P.f P.f = P.f ≫ diag Y := by
  apply prod.hom_ext <;> simp

/-- **Exchange of the trace-class sources** (blueprint `lem-trf-trace-source-exchange`): the
kernel class of the coefficient pushforward `[f, g]_! u` is the transported kernel class of `u`,
`[[f, g]_! u]_P = ρ_f ∘ Rq_* [u]_P ∘ Ξ ∘ Rb_! η_g`. -/
theorem kernelClass_pushforward :
    P.pushforward.kernelClass =
      (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
          ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
            (boundedConstructibleLowerStar _ ℓ P.g).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar _ ℓ (prod.map P.f P.f)).map c.kernelClass ≫
        kernelPushforward ℓ P.f K :=
  sorry

/-- **Exchange of the evaluation kernels** (blueprint `lem-trf-trace-map-exchange`, (1)):
`δ_{K'} ∘ ρ_f = RΔ_{Y*} τ_f ∘ Rq_* δ_K`, read through `Rq_* RΔ_{X*} ≅ RΔ_{Y*} Rf_*`. -/
theorem kernelPushforward_comp_evaluationKernel :
    kernelPushforward ℓ P.f K ≫ evaluationKernel ℓ P.coeff =
      (boundedConstructibleLowerStar _ ℓ (prod.map P.f P.f)).map (evaluationKernel ℓ K) ≫
        (boundedConstructibleLowerStarComp _ ℓ (diag X) (prod.map P.f P.f)).hom.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (by rw [P.diag_comp_prodMap]) ≫
        (boundedConstructibleLowerStarComp _ ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar _ ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f) :=
  sorry

variable (Fc : c.FixedLocus) (Fb : P.pushforward.FixedLocus)

/-- **Exchange of the support isomorphisms** (blueprint `lem-trf-trace-map-exchange`, (2)):
`Rb^!(RΔ_{Y*} τ_f) ∘ E ∘ Rg_* ζ_c = ζ_b ∘ Ri_{b*} τ_h`, read through `g ∘ i_c = i_b ∘ h`. -/
theorem lowerStar_map_supportIso_comp_exchange :
    (boundedConstructibleLowerStar _ ℓ P.g).map Fc.supportIso.hom ≫
        (lowerStarUpperShriekExchange ℓ P.g_comp_support).app
          ((boundedConstructibleLowerStar _ ℓ (diag X)).obj (dualizingComplex' ℓ X)) ≫
        (boundedConstructibleUpperShriek _ ℓ P.pushforward.support).map
          ((boundedConstructibleLowerStarComp _ ℓ (diag X) (prod.map P.f P.f)).hom.app
              (dualizingComplex' ℓ X) ≫
            eqToHom (by rw [P.diag_comp_prodMap]) ≫
            (boundedConstructibleLowerStarComp _ ℓ P.f (diag Y)).inv.app
              (dualizingComplex' ℓ X) ≫
            (boundedConstructibleLowerStar _ ℓ (diag Y)).map
              (lowerStarDualizingComplexTrace ℓ P.f)) =
      (boundedConstructibleLowerStarComp _ ℓ Fc.ι P.g).hom.app (dualizingComplex' ℓ Fc.F) ≫
        eqToHom (by rw [← P.fixMap_ι]) ≫
        (boundedConstructibleLowerStarComp _ ℓ (P.fixMap Fc Fb) Fb.ι).inv.app
          (dualizingComplex' ℓ Fc.F) ≫
        (boundedConstructibleLowerStar _ ℓ Fb.ι).map
          (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb)) ≫
        Fb.supportIso.hom :=
  sorry

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
