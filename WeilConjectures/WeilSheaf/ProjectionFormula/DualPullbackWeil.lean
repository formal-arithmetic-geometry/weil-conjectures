/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarConstant
public import WeilConjectures.WeilSheaf.ProjectionFormula.LisseDualPullback
/-!
# Structure isomorphisms of internal homs and evaluations

For an automorphism `g` and sheaves `M`, `N` of `ℚ̄_ℓ`-modules with structure morphisms
`s : g_* M ≅ M` and `t : g_* N ⟶ N`, the induced structure morphism
`g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N) ⟶ 𝓗om(M, N)` is determined by its composite with the
evaluation (`AlgebraicGeometry.ProEtale.uncurryHom_ihomStr`,
`AlgebraicGeometry.ProEtale.ihomStr_tensorHom_comp_evaluation`). These are the inputs for the
compatibility of the comparison `j^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(j^* G, ℚ̄_ℓ)` with Weil structures.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Endofunctor

namespace CategoryTheory

variable {D D' : Type*} [Category* D] [Category* D'] [MonoidalCategory D] [MonoidalCategory D']

/-- The algebra behind the compatibility of the comparison `j^* [G, 1] ⟶ [j^* G, 1]` with
structure morphisms, stated for evaluations `ev` and `ev'` in monoidal categories: if the
comparison `cc`, the structure morphisms `strG`, `sG` of `[G, 1]` and `G` and `strT` of
`[j^* G, 1]` are compatible with the evaluations, then so are `A cc ≫ strT` and
`E ≫ J strG ≫ cc`. -/
lemma whiskerRight_comp_evaluation_comm (J : D ⥤ D') (B : D ⥤ D) (A : D' ⥤ D')
    [J.LaxMonoidal] [B.LaxMonoidal] [A.LaxMonoidal] (E : J ⋙ A ⟶ B ⋙ J)
    (hEμ : ∀ X Y : D, μ A (J.obj X) (J.obj Y) ≫ A.map (μ J X Y) ≫ E.app (X ⊗ Y) =
      (E.app X ⊗ₘ E.app Y) ≫ μ J (B.obj X) (B.obj Y) ≫ J.map (μ B X Y))
    {Gh Gx One : D} {H' One' : D'} (ev : Gh ⊗ Gx ⟶ One) (ev' : H' ⊗ J.obj Gx ⟶ One')
    (strG : B.obj Gh ⟶ Gh) (sG : B.obj Gx ⟶ Gx) (Lb : B.obj One ⟶ One) (La : A.obj One' ⟶ One')
    (U : J.obj One ⟶ One') (cc : J.obj Gh ⟶ H') (strT : A.obj H' ⟶ H')
    (i : J.obj Gx ⟶ A.obj (J.obj Gx))
    (hi : i ≫ E.app Gx ≫ J.map sG = 𝟙 _)
    (hcc : cc ▷ J.obj Gx ≫ ev' = μ J Gh Gx ≫ J.map ev ≫ U)
    (hT : strT ▷ J.obj Gx ≫ ev' = A.obj H' ◁ i ≫ μ A H' (J.obj Gx) ≫ A.map ev' ≫ La)
    (hG : (strG ⊗ₘ sG) ≫ ev = μ B Gh Gx ≫ B.map ev ≫ Lb)
    (hEu : E.app One ≫ J.map Lb ≫ U = A.map U ≫ La) :
    (A.map cc ≫ strT) ▷ J.obj Gx ≫ ev' =
      ((E.app Gh ≫ J.map strG) ≫ cc) ▷ J.obj Gx ≫ ev' := by
  have hL : (A.map cc ≫ strT) ▷ J.obj Gx ≫ ev' =
      A.obj (J.obj Gh) ◁ i ≫ μ A (J.obj Gh) (J.obj Gx) ≫
        A.map (μ J Gh Gx ≫ J.map ev ≫ U) ≫ La := by
    rw [comp_whiskerRight_assoc, hT, ← whisker_exchange_assoc, μ_natural_left_assoc,
      ← A.map_comp_assoc, hcc]
  have hR : ((E.app Gh ≫ J.map strG) ≫ cc) ▷ J.obj Gx ≫ ev' =
      A.obj (J.obj Gh) ◁ i ≫ ((E.app Gh ≫ J.map strG) ⊗ₘ (E.app Gx ≫ J.map sG)) ≫
        μ J Gh Gx ≫ J.map ev ≫ U := by
    rw [comp_whiskerRight_assoc, hcc, tensorHom_def_assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, hi, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  have n := E.naturality ev
  simp only [Functor.comp_map] at n
  rw [hL, hR, ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← J.map_comp_assoc, hG]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hEμ Gh Gx), ← reassoc_of% n, hEu]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T T₁ T₂ : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

/-- The comparison `g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N)` along an automorphism `g` is compatible
with the evaluations. -/
lemma uncurryHom_adicLowerStarCompIhomIso_inv_app (g : T ⟶ T) [IsIso g] (M N : AdicSheaf l T) :
    Mod.uncurryHom ((adicLowerStarCompIhomIso l g M).inv.app N) =
      μ (g)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)_*[WeilCoefficients.{u} l].map (Mod.evaluation M N) := by
  have : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  exact (Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M N).symm

/-- The structure morphism of `𝓗om(M, N)` induced by structure isomorphisms `s : g_* M ≅ M` and
`t : g_* N ⟶ N` is compatible with the evaluations. -/
lemma uncurryHom_ihomStr (g : T ⟶ T) [IsIso g] (M N : AdicSheaf l T) (s : (g)_*ᵃ[l].obj M ≅ M)
    (t : (g)_*ᵃ[l].obj N ⟶ N) :
    Mod.uncurryHom ((adicLowerStarCompIhomIso l g M).inv.app N ≫ (Mod.ihomMap s.inv).app _ ≫
        (AdicSheaf.ihom M).map t) =
      _ ◁ s.inv.hom ≫ μ (g)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)_*[WeilCoefficients.{u} l].map (Mod.evaluation M N) ≫ t.hom := by
  rw [← Category.assoc, Mod.uncurryHom_comp_ihom_map, Mod.uncurryHom_comp_ihomMap,
    uncurryHom_adicLowerStarCompIhomIso_inv_app, Category.assoc, Category.assoc]
  rfl

/-- The structure morphism of `𝓗om(M, N)` induced by structure isomorphisms `s : g_* M ≅ M` and
`t : g_* N ⟶ N`, tensored with `s`, followed by the evaluation. -/
lemma ihomStr_tensorHom_comp_evaluation (g : T ⟶ T) [IsIso g] (M N : AdicSheaf l T)
    (s : (g)_*ᵃ[l].obj M ≅ M) (t : (g)_*ᵃ[l].obj N ⟶ N) :
    (((adicLowerStarCompIhomIso l g M).inv.app N ≫ (Mod.ihomMap s.inv).app _ ≫
        (AdicSheaf.ihom M).map t).hom ⊗ₘ s.hom.hom) ≫ Mod.evaluation M N =
      μ (g)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)_*[WeilCoefficients.{u} l].map (Mod.evaluation M N) ≫ t.hom := by
  have h := uncurryHom_ihomStr g M N s t
  rw [Mod.uncurryHom] at h
  have hs : s.hom.hom ≫ s.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [tensorHom_def', Category.assoc, h]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc, hs]
  rw [
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **The comparison `j^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(j^* G, ℚ̄_ℓ)` is compatible with the structure
isomorphisms** induced by a structure isomorphism `s : (b⁻¹)_* G ≅ G`, transported along an
isomorphism `e` equal to the exchange isomorphism. -/
lemma adicUpperStarDualComparison_comm (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (G : AdicSheaf l T₂)
    (s : (b.inv)_*ᵃ[l].obj G ≅ G) :
    (a.inv)_*ᵃ[l].map (adicUpperStarDualComparison l j G) ≫
        ((adicLowerStarCompIhomIso l a.inv ((j)^*ᵃ[l].obj G)).inv.app (AdicSheaf.unit l T₁) ≫
          (Mod.ihomMap (e.app G ≪≫ (j)^*ᵃ[l].mapIso s).inv).app _ ≫
          (AdicSheaf.ihom ((j)^*ᵃ[l].obj G)).map (adicLowerStarUnitIso l a.symm).hom) =
      (e.hom.app ((AdicSheaf.ihom G).obj (AdicSheaf.unit l T₂)) ≫
        (j)^*ᵃ[l].map ((adicLowerStarCompIhomIso l b.inv G).inv.app (AdicSheaf.unit l T₂) ≫
          (Mod.ihomMap s.inv).app _ ≫
          (AdicSheaf.ihom G).map (adicLowerStarUnitIso l b.symm).hom)) ≫
        adicUpperStarDualComparison l j G := by
  obtain ⟨E, hE, h₁⟩ : ∃ E : (j)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ≅
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (j)^*[WeilCoefficients.{u} l],
      E = upperStarExchange l j a b c ∧ ∀ M, (e.hom.app M).hom = E.hom.app M.X :=
    ⟨_, rfl, fun M ↦ by
      subst he
      exact adicUpperStarExchange_hom_app_hom j a b c M⟩
  have hEμ (X Y : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)) :=
    hE ▸ upperStarExchange_μ (l := l) j a b c X Y
  have hi : (e.app G ≪≫ (j)^*ᵃ[l].mapIso s).inv.hom ≫ E.hom.app G.X ≫
      (j)^*[WeilCoefficients.{u} l].map s.hom.hom = 𝟙 _ := by
    rw [← h₁, ← adicUpperStar_map_hom, ← Mod.comp_hom', ← Mod.comp_hom']
    exact congrArg Mod.Hom.hom (e.app G ≪≫ (j)^*ᵃ[l].mapIso s).inv_hom_id
  have hEu := upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom_of_eq j a b c E hE
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom, Mod.uncurryHom]
  simp only [Mod.comp_hom']
  rw [h₁, adicUpperStar_map_hom, adicLowerStar_map_hom]
  exact whiskerRight_comp_evaluation_comm (j)^*[WeilCoefficients.{u} l]
    (b.inv)_*[WeilCoefficients.{u} l] (a.inv)_*[WeilCoefficients.{u} l] E.hom hEμ
    (Mod.evaluation G (AdicSheaf.unit l T₂))
    (Mod.evaluation ((j)^*ᵃ[l].obj G) (AdicSheaf.unit l T₁)) _ s.hom.hom
    (adicLowerStarUnitIso l b.symm).hom.hom (adicLowerStarUnitIso l a.symm).hom.hom
    (adicUpperStarUnitIso l j).hom.hom _ _ _ hi
    (uncurryHom_adicUpperStarDualComparison j G)
    (uncurryHom_ihomStr a.inv ((j)^*ᵃ[l].obj G) (AdicSheaf.unit l T₁) _ _)
    (ihomStr_tensorHom_comp_evaluation b.inv G (AdicSheaf.unit l T₂) s _) hEu.symm

variable (l) in
/-- The internal hom `𝓗om(A, B)` of sheaves with structure isomorphisms `(a⁻¹)_* A ≅ A` and
`(a⁻¹)_* B ≅ B`, with the structure isomorphism
`(a⁻¹)_* 𝓗om(A, B) ≅ 𝓗om((a⁻¹)_* A, (a⁻¹)_* B) ≅ 𝓗om(A, B)`. For `a` the geometric Frobenius,
this is the internal hom of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom`). -/
noncomputable def isoAlgebraIhom (a : T ≅ T) (A B : IsoAlgebra (a.inv)_*ᵃ[l]) :
    IsoAlgebra (a.inv)_*ᵃ[l] :=
  IsoAlgebra.mk ((AdicSheaf.ihom A.carrier).obj B.carrier)
    ((adicLowerStarCompIhomIso l a.inv A.carrier).symm.app B.carrier ≪≫
      (Mod.ihomMapIso A.str.symm).app _ ≪≫ (AdicSheaf.ihom A.carrier).mapIso B.str)

lemma isoAlgebraIhom_obj_str (a : T ≅ T) (A B : IsoAlgebra (a.inv)_*ᵃ[l]) :
    (isoAlgebraIhom l a A B).obj.str =
      (adicLowerStarCompIhomIso l a.inv A.carrier).inv.app B.carrier ≫
        (Mod.ihomMap A.str.inv).app _ ≫ (AdicSheaf.ihom A.carrier).map B.str.hom :=
  rfl

/-- The comparison `j^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(j^* G, ℚ̄_ℓ)` is compatible with the structure
isomorphisms, for `G` with a structure isomorphism. -/
lemma adicUpperStarDualComparison_isoAlgebra_comm (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (G : IsoAlgebra (b.inv)_*ᵃ[l]) :
    (a.inv)_*ᵃ[l].map (adicUpperStarDualComparison l j G.carrier) ≫
        (isoAlgebraIhom l a ((IsoAlgebra.mapOfNatIso e).obj G) (isoAlgebraUnit l a)).obj.str =
      ((IsoAlgebra.mapOfNatIso e).obj
          (isoAlgebraIhom l b G (isoAlgebraUnit l b))).obj.str ≫
        adicUpperStarDualComparison l j G.carrier := by
  rw [isoAlgebraIhom_obj_str, mapOfNatIso_obj_obj_str, isoAlgebraIhom_obj_str,
    IsoAlgebra.mapOfNatIso_obj_str]
  exact adicUpperStarDualComparison_comm j a b c e he G.carrier G.str

variable (l) in
/-- **The pullback of the dual is the dual of the pullback**, for sheaves with structure
isomorphisms, when the comparison of the underlying sheaves is an isomorphism. -/
noncomputable def mapOfNatIsoIsoAlgebraIhomIso (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (G : IsoAlgebra (b.inv)_*ᵃ[l])
    [IsIso (adicUpperStarDualComparison l j G.carrier)] :
    (IsoAlgebra.mapOfNatIso e).obj (isoAlgebraIhom l b G (isoAlgebraUnit l b)) ≅
      isoAlgebraIhom l a ((IsoAlgebra.mapOfNatIso e).obj G) (isoAlgebraUnit l a) :=
  IsoAlgebra.isoMk (asIso (adicUpperStarDualComparison l j G.carrier))
    (adicUpperStarDualComparison_isoAlgebra_comm j a b c e he G)

/-- `AlgebraicGeometry.ProEtale.mapOfNatIsoIsoAlgebraIhomIso` for objects equal to the duals. -/
theorem nonempty_mapOfNatIso_obj_isoAlgebraIhom_iso_of_eq (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁)
    (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (G : IsoAlgebra (b.inv)_*ᵃ[l])
    [IsIso (adicUpperStarDualComparison l j G.carrier)] (K : IsoAlgebra (b.inv)_*ᵃ[l])
    (hK : K = isoAlgebraIhom l b G (isoAlgebraUnit l b)) (K' : IsoAlgebra (a.inv)_*ᵃ[l])
    (hK' : K' = isoAlgebraIhom l a ((IsoAlgebra.mapOfNatIso e).obj G) (isoAlgebraUnit l a)) :
    Nonempty ((IsoAlgebra.mapOfNatIso e).obj K ≅ K') := by
  subst hK hK'
  exact ⟨mapOfNatIsoIsoAlgebraIhomIso l j a b c e he G⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "𝐒" => Spec (CommRingCat.of k₀)

set_option hygiene false in
local notation "Fr[" T "]" => Scheme.Hom.geometricGaloisFrobenius (T ↘ Spec (CommRingCat.of k₀))

set_option hygiene false in
local notation "bc[" f "]" =>
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "EX[" φ "]" => adicUpperStarExchange l (bc[φ]) (Fr[X]) (Fr[Y])
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ 𝐒)).symm

/-- The dual of a lisse Weil sheaf is the internal hom into the constant sheaf, with the
structure isomorphism along the geometric Frobenius. -/
lemma dual_obj_eq_isoAlgebraIhom {T : Scheme.{u}} [T.Over 𝐒] (G : WeilSheaf k₀ l T)
    (hG : G.IsLisse) :
    (G.dual hG).obj = isoAlgebraIhom l (Fr[T]) G.obj (isoAlgebraUnit l (Fr[T])) :=
  rfl

/-- The dual of the pullback of a lisse Weil sheaf. -/
lemma dual_upperStar_obj_eq_isoAlgebraIhom (φ : X ⟶ Y) [φ.IsOver 𝐒] (G : WeilSheaf k₀ l Y)
    (hG : G.IsLisse) :
    (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj =
      isoAlgebraIhom l (Fr[X]) ((IsoAlgebra.mapOfNatIso (EX[φ])).obj G.obj)
        (isoAlgebraUnit l (Fr[X])) := by
  rw [← upperStar_eq_mapOfNatIso]
  rfl

/-- **The pullback of the dual of a lisse Weil sheaf is the dual of the pullback**:
`φ^*(G^∨) ≅ (φ^* G)^∨`, through the comparison
`AlgebraicGeometry.ProEtale.adicUpperStarDualComparison` of the underlying sheaves, an
isomorphism by `AlgebraicGeometry.ProEtale.isIso_adicUpperStarDualComparison_of_specializes`. -/
theorem nonempty_upperStar_obj_dual_iso [LocallyOfFiniteType (X ↘ 𝐒)] [QuasiCompact (X ↘ 𝐒)]
    (φ : X ⟶ Y) [φ.IsOver 𝐒] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty ((upperStar k₀ l φ).obj (G.dual hG).obj ≅
      (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj) := by
  have : IsLocallyNoetherian (X ↘ 𝐒).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ 𝐒).geometricFiberToAlgebraicClosure
  have : IsIso (adicUpperStarDualComparison l (bc[φ]) G.obj.carrier) :=
    isIso_adicUpperStarDualComparison_of_specializes _ hG fun z ↦
      Scheme.Hom.exists_specializes_of_isAlgClosed (X ↘ 𝐒).geometricFiberToAlgebraicClosure z
  rw [upperStar_eq_mapOfNatIso]
  exact nonempty_mapOfNatIso_obj_isoAlgebraIhom_iso_of_eq (l := l) (bc[φ]) (Fr[X]) (Fr[Y])
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ 𝐒)).symm
    (EX[φ]) rfl G.obj _ (dual_obj_eq_isoAlgebraIhom G hG) _
    (dual_upperStar_obj_eq_isoAlgebraIhom φ G hG)

end AlgebraicGeometry.ProEtaleWeilSheaf
