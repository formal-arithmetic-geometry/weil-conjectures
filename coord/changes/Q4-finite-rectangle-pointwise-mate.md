# coefficient_exchange_of_counit pointwise API

## Reason

The rectangle uses the pullback cube only at R.obj K. Moreover, the mate calculation
uses only the four exchange/projection components at K and H.obj K, without their
naturality laws. Add a proved pointwise API taking those four morphisms and their
four counit equations directly. The existing universal theorem keeps its verbatim
signature and applies that API to its components. The new coefficientPullbackSquare
predicate packages the existing cube equation with fixed category/functor arguments;
it is a real equation, with no new construction, axiom, or hole. This interface
avoids expanded metadata from inferred natural-transformation component types in
concrete derived applications. The pointwise proof is the original mate calculation
with only the unused uniform quantifiers removed; it proves a strictly stronger API.

## Old

```lean
theorem coefficient_exchange_of_counit
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (B : R ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (hB : ∀ K, V.map (B.app K) ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : ∀ K, Ve.map (Be.app K) ≫ be.counit.app (He.obj K) =
      θe.app (Re.obj K) ≫ He.map (ae.counit.app K))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : R ⋙ T₁ ⟶ T₂ ⋙ Re) (δ' : S ⋙ T₃ ⟶ T₄ ⋙ Se)
    (hδ : ∀ K, Ue.map (δ.app K) ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : ∀ K, Ve.map (δ'.app K) ≫ be.counit.app (T₄.obj K) =
      αV.inv.app (S.obj K) ≫ T₄.map (b.counit.app K))
    (hcube : ∀ K, T₄.map (θ.app K) ≫ αH.app (U.obj K) ≫
        He.map (αU.hom.app K) =
      αV.hom.app (G.obj K) ≫ Ve.map (αG.app K) ≫ θe.app (T₁.obj K))
    (K : C₂) :
    αG.app (R.obj K) ≫ Ge.map (δ.app K) ≫ Be.app (T₂.obj K) =
      T₃.map (B.app K) ≫ δ'.app (H.obj K) ≫ Se.map (αH.app K)
```

## New

```lean
def coefficientPullbackSquare
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (M : C₁) : Prop :=
  T₄.map (θ.app M) ≫ αH.app (U.obj M) ≫ He.map (αU.hom.app M) =
    αV.hom.app (G.obj M) ≫ Ve.map (αG.app M) ≫ θe.app (T₁.obj M)
```

```lean
theorem coefficient_exchange_of_counit_at
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (K : C₂)
    (B : (R ⋙ G).obj K ⟶ (H ⋙ S).obj K)
    (Be : (Re ⋙ Ge).obj (T₂.obj K) ⟶ (He ⋙ Se).obj (T₂.obj K))
    (hB : V.map B ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : Ve.map Be ≫ be.counit.app (He.obj (T₂.obj K)) =
      θe.app (Re.obj (T₂.obj K)) ≫ He.map (ae.counit.app (T₂.obj K)))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : T₁.obj (R.obj K) ⟶ Re.obj (T₂.obj K))
    (δ' : T₃.obj (S.obj (H.obj K)) ⟶ Se.obj (T₄.obj (H.obj K)))
    (hδ : Ue.map δ ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : Ve.map δ' ≫ be.counit.app (T₄.obj (H.obj K)) =
      αV.inv.app (S.obj (H.obj K)) ≫ T₄.map (b.counit.app (H.obj K)))
    (hcube : coefficientPullbackSquare θ θe αU αV αG αH (R.obj K)) :
    αG.app (R.obj K) ≫ Ge.map δ ≫ Be =
      T₃.map B ≫ δ' ≫ Se.map (αH.app K) := by
  unfold coefficientPullbackSquare at hcube
  apply (be.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [hBe]
  have hn := θe.naturality (δ)
  rw [reassoc_of% hn, ← Functor.map_comp, hδ]
  have hn' := be.counit.naturality (αH.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn'
  rw [hn', reassoc_of% (hδ')]
  rw [reassoc_of% (αV.inv.naturality (B)), ← Functor.map_comp_assoc, hB]
  simp only [Functor.map_comp, Category.assoc]
  have hnH := αH.naturality (a.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hnH
  rw [hnH]
  have hc := congrArg (fun z ↦ αV.inv.app (G.obj (R.obj K)) ≫ z ≫
    He.map (αU.inv.app (R.obj K))) hcube
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hc
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc
  simp only [Functor.comp_obj, Functor.map_id, Category.comp_id] at hc
  simpa only [Category.assoc, Functor.map_id, Category.id_comp] using congrArg
    (fun z ↦ z ≫ He.map (T₂.map (a.counit.app K))) hc.symm
```

```lean
theorem coefficient_exchange_of_counit
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (B : R ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (hB : ∀ K, V.map (B.app K) ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : ∀ K, Ve.map (Be.app K) ≫ be.counit.app (He.obj K) =
      θe.app (Re.obj K) ≫ He.map (ae.counit.app K))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : R ⋙ T₁ ⟶ T₂ ⋙ Re) (δ' : S ⋙ T₃ ⟶ T₄ ⋙ Se)
    (hδ : ∀ K, Ue.map (δ.app K) ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : ∀ K, Ve.map (δ'.app K) ≫ be.counit.app (T₄.obj K) =
      αV.inv.app (S.obj K) ≫ T₄.map (b.counit.app K))
    (hcube : ∀ K, T₄.map (θ.app K) ≫ αH.app (U.obj K) ≫
        He.map (αU.hom.app K) =
      αV.hom.app (G.obj K) ≫ Ve.map (αG.app K) ≫ θe.app (T₁.obj K))
    (K : C₂) :
    αG.app (R.obj K) ≫ Ge.map (δ.app K) ≫ Be.app (T₂.obj K) =
      T₃.map (B.app K) ≫ δ'.app (H.obj K) ≫ Se.map (αH.app K) := by
  exact coefficient_exchange_of_counit_at a b ae be θ θe K (B.app K) (Be.app (T₂.obj K))
    (hB K) (hBe (T₂.obj K)) αU αV αG αH (δ.app K) (δ'.app (H.obj K))
    (hδ K) (hδ' (H.obj K)) (hcube (R.obj K))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Adjunction.CoefficientExchange | unclaimed | Adds the predicate and proved component API; original signature retained. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Existing universal theorem application is unchanged. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | Uses the component API and the cube at R.obj K. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | new, Q4 | States the geometric cube as the explicit equation (reviewer fix: the predicate is not used in the statement); the rectangle passes it as the predicate by unfolding. |

The downstream.py --uses scan for coefficient_exchange_of_counit lists the first
two existing modules. No module held by another group is edited. No target or
existing public statement changes, and this module has zero sorries.

## Status

landed 20261020T233213-L-905022 2026-10-20 (merge of deliver/Q4/Sheaf.Paper.FiniteLevelRectangle)
