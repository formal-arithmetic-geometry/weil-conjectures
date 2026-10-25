/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunneth
public import WeilConjectures.TraceFormula.SourceExchangeKunnethBaseChange
public import WeilConjectures.TraceFormula.SourceExchangeKunnethUnit

/-!

# The exceptional Künneth adjoint along a proper pushforward

The exceptional Künneth part of identity (a) of the trace-class source exchange (blueprint
`lem-trf-trace-source-exchange`, Step 3):
`ProEtale.CondensedRing.lowerShriek_map_trace_comp_exceptionalKunnethAdjoint`. Through `Π_f`,
`Rq_* ≅ Rq_!`, the composition law of the square `q ≫ p₁' = p₁ ≫ f` and `Rf_! ≅ Rf_*`, the
adjoint of the exceptional Künneth map of `Rf_* K`, precomposed with the trace `τ_f`, is `Rf_*`
of that of `K`.

The proof writes `Π_f` through the unit of `Lq^* ⊣ Rq_!`
(`ProEtale.CondensedRing.prodLowerStarExternalProduct_comp_inv_app`), moves the projection
formula for `p₁'` across that unit to those for `f` and `p₁`
(`ProEtale.CondensedRing.exceptionalProjection_comp_unit_square`), evaluates the projection
formula for `p₁` against the exceptional Künneth adjoint of `K`
(`ProEtale.CondensedRing.exceptionalProjection_comp_exceptionalKunnethAdjoint`), and concludes
with the base change along the Künneth square
(`ProEtale.CondensedRing.unit_comp_lowerShriek_map_prodBaseChangeIso`) and the unit
compatibility of the projection formula for `f`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Braiding

variable {X Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The tensor symmetry of an external product, `M ⊠ N ≅ Lp_Z^* N ⊗ Lp_X^* M`, with the external
product in its source (so that it composes with maps out of `M ⊠ N` without unfolding
`ProEtale.CondensedRing.externalProduct`). -/
noncomputable def externalProductBraiding (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M N ≅ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Z ⟶ Z)).obj N ⊗
      (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)).obj M :=
  β_ _ _

end Braiding

section Evaluation

variable {X Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The projection formula for `p_X` followed by the exceptional Künneth adjoint: for maps
`c : S ⟶ Lp_Z^* ω_Z` and `e : M' ⟶ K`, it applies `c`, base change in the product square, the
counit of `Ra_Z! ⊣ Ra_Z^!` and then `e`. -/
theorem exceptionalProjection_comp_exceptionalKunnethAdjoint
    (S : Dᵇc((X ⨯ Z).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {M' K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (e : M' ⟶ K)
    (c : S ⟶ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Z ⟶ Z)).obj
      (dualizingComplex' ℓ Z)) :
    boundedConstructibleExceptionalProjectionMorphism _ ℓ (prod.fst : X ⨯ Z ⟶ X) S M' ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ Z ⟶ X)).map
        ((S ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)).map e) ≫
          (c ▷ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)).obj K) ≫
          (externalProductBraiding ℓ K (dualizingComplex' ℓ Z)).inv) ≫
      exceptionalKunnethAdjoint ℓ K =
    (((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ Z ⟶ X)).map c ≫
        (prodBaseChangeIso ℓ X Z).hom.app (dualizingComplex' ℓ Z) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint Z)).counit.app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) ▷ M') ≫
      (𝟙_ _ ◁ e) ≫ (λ_ K).hom := by
  sorry

end Evaluation

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The Künneth map `Π_f` of `q = f × f`, read through `Rq_* ≅ Rq_!`, is the unit of
`Lq^* ⊣ Rq_!` followed by `Rq_!` of the tensor structure of `Lq^*` and the transported counits,
written with the factors exchanged. -/
theorem prodLowerStarExternalProduct_comp_inv_app (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    prodLowerStarExternalProduct ℓ f f K N ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
        (externalProduct ℓ K N) =
    (externalProductBraiding ℓ _ _).hom ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f f)).unit.app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj N) ⊗
          (boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj K)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.map f f)).map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (prod.map f f))
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj N))
            ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K)) ≫
          (_ ◁ ((boundedConstructibleUpperStarComp _ ℓ (prod.map f f) prod.fst).inv.app
              ((boundedConstructibleLowerStar _ ℓ f).obj K) ≫
            eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K)) (prod.map_fst f f)) ≫
            ((boundedConstructibleUpperStarComp _ ℓ (prod.fst : X ⨯ X ⟶ X) f).hom.app
              ((boundedConstructibleLowerStar _ ℓ f).obj K) :
                _ ⟶ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj
                  ((boundedConstructibleUpperStar _ ℓ f).obj
                    ((boundedConstructibleLowerStar _ ℓ f).obj K)))))) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.map f f)).map
        ((_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
            ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K :
              (boundedConstructibleUpperStar _ ℓ f).obj
                ((boundedConstructibleLowerStar _ ℓ f).obj K) ⟶ K)) ≫
          (prodUpperStarCounit ℓ (prod.map_snd f f) N ▷ _) ≫
          (externalProductBraiding ℓ K N).inv) := by
  sorry

/-- An abstract chain of identities: a composite through a functor `L`, a natural
transformation `σ : Q ⋙ L ⟶ P ⋙ F` and a functor `F` is rewritten through an isomorphism `π`,
given the pieces of the chain. -/
lemma _root_.CategoryTheory.NatTrans.map_comp_map_comp_app_comp_map_comp_eq {𝒜 𝒟 𝒳 𝒴 : Type*}
    [Category 𝒜] [Category 𝒟] [Category 𝒳] [Category 𝒴] (L : 𝒜 ⥤ 𝒟) (Q : 𝒳 ⥤ 𝒜)
    (P : 𝒳 ⥤ 𝒴) (F : 𝒴 ⥤ 𝒟) (σ : Q ⋙ L ⟶ P ⋙ F) {a₀ a₁ a₂ a₃ : 𝒜} {x₂ x₃ : 𝒳} {y y₁ : 𝒴}
    {d d₁ d₂ : 𝒟} {m₁ : a₀ ⟶ a₁} {m₂ : a₁ ⟶ Q.obj x₃} {b : a₀ ⟶ a₂} {u : a₂ ⟶ a₃}
    {v : a₃ ⟶ Q.obj x₂} {z₂ : x₂ ⟶ x₃} {e : P.obj x₃ ⟶ y} {r : F.obj y ⟶ d} {π : d₁ ⟶ L.obj a₂}
    [IsIso π] {w₁ : d₁ ⟶ d₂} {w₂ : d₂ ⟶ F.obj y₁} {g : y₁ ⟶ P.obj x₂} {c : y₁ ⟶ y}
    {t : d₁ ⟶ d} {π' : d₁ ⟶ L.obj a₂} (hπ : π = π') (hR : m₁ ≫ m₂ = b ≫ u ≫ v ≫ Q.map z₂)
    (hL : π' ≫ L.map (u ≫ v) ≫ σ.app x₂ = w₁ ≫ w₂ ≫ F.map g)
    (hC : g ≫ P.map z₂ ≫ e = c) (hG : w₁ ≫ w₂ ≫ F.map c ≫ r = t) :
    L.map b ≫ inv π ≫ t = L.map m₁ ≫ L.map m₂ ≫ σ.app x₃ ≫ F.map e ≫ r := by
  subst hπ
  have hσ : L.map (Q.map z₂) ≫ σ.app x₃ = σ.app x₂ ≫ F.map (P.map z₂) := σ.naturality z₂
  have hL' : L.map (u ≫ v) ≫ σ.app x₂ = inv π ≫ w₁ ≫ w₂ ≫ F.map g := by
    rw [← hL, IsIso.inv_hom_id_assoc]
  calc L.map b ≫ inv π ≫ t
      = L.map b ≫ inv π ≫ w₁ ≫ w₂ ≫ F.map g ≫ F.map (P.map z₂) ≫ F.map e ≫ r := by
        rw [← hG, ← hC]; simp only [Functor.map_comp, Category.assoc]
    _ = L.map b ≫ L.map (u ≫ v) ≫ σ.app x₂ ≫ F.map (P.map z₂) ≫ F.map e ≫ r := by
        rw [reassoc_of% hL']
    _ = L.map b ≫ L.map (u ≫ v) ≫ L.map (Q.map z₂) ≫ σ.app x₃ ≫ F.map e ≫ r := by
        rw [reassoc_of% hσ]
    _ = L.map m₁ ≫ L.map m₂ ≫ σ.app x₃ ≫ F.map e ≫ r := by
        rw [← L.map_comp_assoc m₁ m₂, hR]; simp only [Functor.map_comp, Category.assoc]


set_option maxHeartbeats 3000000 in
/-- The base-change core of the exceptional Künneth part of identity (a) (blueprint
`lem-trf-trace-source-exchange`, Step 3): the projection formula for `p₁'`, compact-support base
change in the product square of `Y` and the pasted counit of `a_X = f ≫ a_Y` agree, through
`Π_f`, `Rq_* ≅ Rq_!`, the composition law of `q ≫ p₁' = p₁ ≫ f` and `Rf_! ≅ Rf_*`, with `Rf_!`
of the projection formula for `p₁`, base change in the product square of `X` and the counit of
`a_X`. -/
theorem lowerShriek_exceptionalKunneth_baseChange :
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)))).app
        ((boundedConstructibleLowerStar _ ℓ f).obj K)) ≫
      (((prodBaseChangeIso ℓ Y Y).hom.app
          ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint Y)).map
          ((boundedConstructibleLowerShriek _ ℓ (toPoint Y)).map
              ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
                (dualizingComplex' ℓ X)) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
              (dualizingComplex' ℓ X) ≫
            eqToHom (by rw [comp_toPoint]; rfl) ≫
            (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint X)).counit.app (𝟙_ _))) ▷
        (boundedConstructibleLowerStar _ ℓ f).obj K) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint Y))).inv ▷ _) ≫
      (λ_ _).hom =
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (dualizingComplex' ℓ X))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map (exceptionalKunnethAdjoint ℓ K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K := by
  apply NatTrans.map_comp_map_comp_app_comp_map_comp_eq
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleLowerShriek _ ℓ (prod.map f f))
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X))
    (boundedConstructibleLowerShriek _ ℓ f)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom
  case hπ => exact boundedConstructibleExceptionalProjection_app_app _ ℓ _ _ _
  case hL =>
    have h := exceptionalProjection_comp_unit_square ℓ (prod.map_fst f f) ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X))) ((boundedConstructibleLowerStar _ ℓ f).obj K)
    exact h
  case hC =>
    have h := exceptionalProjection_comp_exceptionalKunnethAdjoint ℓ
      ((boundedConstructibleUpperStar _ ℓ (prod.map f f)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X))))
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K :
        (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleLowerStar _ ℓ f).obj K) ⟶ K)
      (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X))
    exact h
  case hR =>
    have h := prodLowerStarExternalProduct_comp_inv_app ℓ f K (dualizingComplex' ℓ X)
    exact h
  case hG =>
    have h := whiskerRight_unit_square_comp_exceptionalProjection ℓ f K
    exact h

/-- **The exceptional Künneth adjoint commutes with a proper pushforward** (blueprint
`lem-trf-trace-source-exchange`, Step 3): through `Π_f`, `Rq_* ≅ Rq_!`, the composition law of
the square `q ≫ p₁' = p₁ ≫ f` and `Rf_! ≅ Rf_*`, the adjoint of the exceptional Künneth map of
`Rf_* K` precomposed with the trace `τ_f` is `Rf_*` of that of `K`. -/
theorem lowerShriek_map_trace_comp_exceptionalKunnethAdjoint :
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj K) ◁
          (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
            (lowerStarDualizingComplexTrace ℓ f)) ≫
      exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K) =
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (dualizingComplex' ℓ X))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map (exceptionalKunnethAdjoint ℓ K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K :=
  by
  refine (lowerShriek_map_whiskerLeft_comp_exceptionalKunnethAdjoint ℓ _ _).trans ?_
  rewrite [lowerShriek_map_lowerStarDualizingComplexTrace_comp_counit ℓ f]
  exact lowerShriek_exceptionalKunneth_baseChange ℓ f K


end AlgebraicGeometry.ProEtale.CondensedRing
