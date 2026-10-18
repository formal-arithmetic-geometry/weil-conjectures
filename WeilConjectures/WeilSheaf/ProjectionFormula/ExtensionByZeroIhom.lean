/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.ExtensionByZeroAdjunction
public import WeilConjectures.WeilSheaf.ProjectionFormula.LowerShriekIhom

/-!
# Extension by zero and internal homs out of lisse Weil sheaves

Assume that the internal hom out of a pro-étale Weil sheaf with lisse underlying sheaf is the
tensor product with its dual (`hD`). Then:

- pullback commutes with internal homs out of lisse sheaves,
  `φ^* [N, -] ≅ [φ^* N, φ^* -]`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_ihomFunctor_comp_upperStar_iso_of_duality`),
  by the compatibility of pullbacks with tensor products and with duals;
- the projection formula for the extension by zero along an open immersion `j`,
  `j_!(K ⊗ j^* N) ≅ j_! K ⊗ N` for lisse `N`, by conjugation along `j_! ⊣ j^*`
  (`nonempty_tensorFunctor_comp_extensionByZero_iso_of_duality`);
- the extension by zero commutes with internal homs out of lisse sheaves,
  `j_! [j^* M, -] ≅ [M, j_! -]`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_extensionByZero_comp_ihomFunctor_iso_of_duality`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The duality hypothesis: the internal hom out of a pro-étale Weil sheaf with lisse underlying
sheaf is the tensor product with its dual. -/
def LisseDuality (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] : Prop :=
  ∀ {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k₀))] (M : ProEtaleWeilSheaf k₀ l T),
    IsAdicLisseSheaf M.carrier →
      Nonempty (ihomFunctor k₀ l T M ≅
        tensorFunctor k₀ l T (ihom k₀ l T M (adicConstant k₀ l T)))

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- Tensor products with isomorphic pro-étale Weil sheaves are isomorphic: their right adjoints
are (`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorMapIsoLeft`). -/
noncomputable def tensorFunctorMapIso {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ≅ A') :
    tensorFunctor k₀ l X A ≅ tensorFunctor k₀ l X A' :=
  (conjugateIsoEquiv (tensorIhomAdjunction k₀ l X A') (tensorIhomAdjunction k₀ l X A)).symm
    (ihomFunctorMapIsoLeft φ)

/-- **Pullback commutes with internal homs out of lisse sheaves**, assuming the duality
`LisseDuality`: `φ^* [N, -] ≅ [φ^* N, φ^* -]`. -/
theorem nonempty_ihomFunctor_comp_upperStar_iso_of_duality (hD : LisseDuality k₀ l)
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (N : ProEtaleWeilSheaf k₀ l Y)
    (hN : IsAdicLisseSheaf N.carrier) :
    Nonempty (ihomFunctor k₀ l Y N ⋙ upperStar k₀ l φ ≅
      upperStar k₀ l φ ⋙ ihomFunctor k₀ l X ((upperStar k₀ l φ).obj N)) := by
  obtain ⟨d₁⟩ := hD N hN
  obtain ⟨d₂⟩ := hD ((upperStar k₀ l φ).obj N)
    (hN.upperStar (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))))
  obtain ⟨w⟩ := nonempty_tensorFunctorCompUpperStarIso φ (ihom k₀ l Y N (adicConstant k₀ l Y))
  obtain ⟨p⟩ := nonempty_upperStar_obj_ihom_adicConstant_iso φ N hN
  exact ⟨Functor.isoWhiskerRight d₁ _ ≪≫ w ≪≫
    Functor.isoWhiskerLeft _ (tensorFunctorMapIso p ≪≫ d₂.symm)⟩

/-- **The projection formula for the extension by zero**, assuming the duality `LisseDuality`:
`j_!(K ⊗ j^* N) ≅ j_! K ⊗ N` for an open immersion `j` and `N` with lisse underlying sheaf, by
conjugation of `j^* [N, -] ≅ [j^* N, j^* -]` along `j_! ⊣ j^*`. -/
theorem nonempty_tensorFunctor_comp_extensionByZero_iso_of_duality (hD : LisseDuality k₀ l)
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (N : ProEtaleWeilSheaf k₀ l Y)
    (hN : IsAdicLisseSheaf N.carrier) :
    Nonempty (tensorFunctor k₀ l X ((upperStar k₀ l j).obj N) ⋙ extensionByZero k₀ l j ≅
      extensionByZero k₀ l j ⋙ tensorFunctor k₀ l Y N) := by
  obtain ⟨a⟩ := nonempty_ihomFunctor_comp_upperStar_iso_of_duality hD j N hN
  exact ⟨(conjugateIsoEquiv
    ((extensionByZeroUpperStarAdjunction k₀ l j).comp (tensorIhomAdjunction k₀ l Y N))
    ((tensorIhomAdjunction k₀ l X ((upperStar k₀ l j).obj N)).comp
      (extensionByZeroUpperStarAdjunction k₀ l j))).symm a⟩

/-- **The extension by zero commutes with internal homs out of lisse sheaves**, assuming the
duality `LisseDuality`: `j_! [j^* M, -] ≅ [M, j_! -]` for an open immersion `j`. -/
theorem nonempty_extensionByZero_comp_ihomFunctor_iso_of_duality (hD : LisseDuality k₀ l)
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (M : ProEtaleWeilSheaf k₀ l Y)
    (hM : IsAdicLisseSheaf M.carrier) :
    Nonempty (extensionByZero k₀ l j ⋙ ihomFunctor k₀ l Y M ≅
      ihomFunctor k₀ l X ((upperStar k₀ l j).obj M) ⋙ extensionByZero k₀ l j) := by
  obtain ⟨d₁⟩ := hD M hM
  obtain ⟨b⟩ := nonempty_tensorFunctor_comp_extensionByZero_iso_of_duality hD j
    (ihom k₀ l Y M (adicConstant k₀ l Y)) (hM.ihom (isAdicLisseSheaf_adicConstantSheaf _))
  obtain ⟨p⟩ := nonempty_upperStar_obj_ihom_adicConstant_iso j M hM
  obtain ⟨d₂⟩ := hD ((upperStar k₀ l j).obj M)
    (hM.upperStar (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
  exact ⟨Functor.isoWhiskerLeft _ d₁ ≪≫ b.symm ≪≫
    Functor.isoWhiskerRight (tensorFunctorMapIso p ≪≫ d₂.symm) _⟩

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

open ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The projection formula for Weil complexes, from the duality of lisse sheaves**:
`Rf₀!(K) ⊗ G ≅ Rf₀!(K ⊗ f^* G)` for a lisse Weil sheaf `G`, assuming that the internal hom out
of a lisse pro-étale Weil sheaf is the tensor product with its dual (`LisseDuality`). -/
theorem nonempty_iso_derivedLowerShriek_tensorLisse_of_duality (hD : LisseDuality k₀ l)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (derivedLowerShriek k₀ l f ⋙ tensorLisse G hG ≅
      tensorLisse ((WeilSheaf.upperStar f).obj G) (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        derivedLowerShriek k₀ l f) := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  exact nonempty_iso_derivedLowerShriek_tensorLisse_of_extensionByZero f G hG
    fun j _ _ M hM ↦ nonempty_extensionByZero_comp_ihomFunctor_iso_of_duality hD j M hM

end AlgebraicGeometry.WeilComplex
