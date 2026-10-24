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
* the evaluation kernels are exchanged by the kernel pushforward (blueprint
  `lem-trf-trace-map-exchange`, (1); proved in
  `WeilConjectures.TraceFormula.ProperCompatibilityEvaluation`);
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

/-- The points `𝟙 ⟶ Rp_* 𝟙` (units followed by the unit comparisons of the pullbacks) compose:
for adjunctions `Lp ⊣ Rp`, `Lq ⊣ Rq`, `Lpq ⊣ Rpq` with `Lpq ≅ Lq ⋙ Lp` and the conjugate
`Rp ⋙ Rq ≅ Rpq`, compatible unit comparisons give `s_q ≫ Rq s_p = s_{pq} ≫ (Rp ⋙ Rq ≅ Rpq)⁻¹`. -/
lemma Adjunction.unit_map_comp_unit_map {CA CB CC : Type*} [Category CA] [Category CB]
    [Category CC] {Lp : CB ⥤ CA} {Rp : CA ⥤ CB} {Lq : CC ⥤ CB} {Rq : CB ⥤ CC} {Lpq : CC ⥤ CA}
    {Rpq : CA ⥤ CC} (ap : Lp ⊣ Rp) (aq : Lq ⊣ Rq) (apq : Lpq ⊣ Rpq) (cU : Lpq ≅ Lq ⋙ Lp)
    (cR : Rp ⋙ Rq ≅ Rpq) (hcR : cR.inv = conjugateEquiv apq (aq.comp ap) cU.inv) {oC : CC}
    {oB : CB} {oA : CA} (eq : Lq.obj oC ⟶ oB) (ep : Lp.obj oB ⟶ oA) (epq : Lpq.obj oC ⟶ oA)
    (hε : cU.hom.app oC ≫ Lp.map eq ≫ ep = epq) :
    (aq.unit.app oC ≫ Rq.map eq) ≫ Rq.map (ap.unit.app oB ≫ Rp.map ep) =
      (apq.unit.app oC ≫ Rpq.map epq) ≫ cR.inv.app oA := by
  have hU := unit_conjugateEquiv apq (aq.comp ap) cU.inv oC
  rw [← hcR] at hU
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_unit_app] at hU
  have hη := ap.unit.naturality eq
  have hn := cR.inv.naturality epq
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hη hn
  rw [Category.assoc, Category.assoc, hn, reassoc_of% hU, ← hε]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  congr 2
  rw [Functor.map_comp, ← reassoc_of% hη]

/-- Bookkeeping for the proper pushforward of the trace class (blueprint
`thm-trf-trace-proper-compatibility`, Step 4): two chains of points through a square agree. -/
lemma comp_eq_comp_of_points {C : Type*} [Category C]
    {P₀ P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ Q₄ Q₅ R₁ R₂ S₁ S₂ N : C}
    (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃) (a₄ : P₃ ⟶ P₄) (t : P₄ ⟶ P₅)
    (b₁ : P₀ ⟶ Q₁) (b₂ : Q₁ ⟶ Q₂) (b₃ : Q₂ ⟶ Q₃) (b₄ : Q₃ ⟶ Q₄) (t' : Q₄ ⟶ Q₅)
    (e₁ : Q₅ ⟶ R₁) (e₂ : R₁ ⟶ R₂) (e₃ : R₂ ⟶ P₅) (f₁ : Q₄ ⟶ S₁) (f₂ : S₁ ⟶ S₂) (f₃ : S₂ ⟶ P₄)
    (z : P₀ ⟶ S₁) (w : P₀ ⟶ S₂) (r : P₅ ⟶ N)
    (hnat : t' ≫ e₁ ≫ e₂ ≫ e₃ = f₁ ≫ f₂ ≫ f₃ ≫ t) (hpg : b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ f₁ = z)
    (htr : z ≫ f₂ = w) (hhb : a₁ ≫ a₂ ≫ a₃ ≫ a₄ = w ≫ f₃) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ t ≫ r = b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ t' ≫ e₁ ≫ e₂ ≫ e₃ ≫ r := by
  rw [reassoc_of% hnat]
  simp only [← Category.assoc] at hpg hhb ⊢
  rw [hpg, hhb, ← htr]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

section Transport

variable {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
  [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- `Rp_*` and `Rq_*` agree on morphisms for `p = q`, through the casts. -/
lemma lowerStar_map_comp_eqToHom_of_eq {p q : A ⟶ B} (h : p = q)
    {a b : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (x : a ⟶ b) :
    (boundedConstructibleLowerStar _ ℓ p).map x ≫ eqToHom (congrArg (fun r : A ⟶ B ↦
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj b) h) =
      eqToHom (congrArg (fun r : A ⟶ B ↦
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj a) h) ≫
        (boundedConstructibleLowerStar _ ℓ q).map x := by
  subst h
  simp

/-- The points `𝟙 ⟶ Rp_* 𝟙` of `p = q` agree through the cast. -/
lemma unit_comp_map_εIso_inv_comp_eqToHom_of_eq {p q : A ⟶ B} (h : p = q) :
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar _ ℓ p).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ p)).inv) ≫
      eqToHom (congrArg (fun r : A ⟶ B ↦
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj (𝟙_ _)) h) =
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ q).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar _ ℓ q).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ q)).inv := by
  subst h
  simp

end Transport

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


end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
