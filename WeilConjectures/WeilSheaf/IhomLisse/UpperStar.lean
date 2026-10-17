/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobeniusMate
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison
public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Pullback of the internal hom out of a lisse Weil sheaf

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pullback `φ̄^*` along its base change to the
geometric fibres is strong monoidal, and the exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`
defining the Weil structure of `φ^* F` is monoidal. Hence a pairing of Weil sheaves compatible
with the Weil structures pulls back to a compatible pairing
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar_pairing_str`). Applied to the evaluation, this
shows that the comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]`
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomComparison`) is a morphism of pro-étale Weil
sheaves; it is an isomorphism for `A` lisse, which gives
`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- A composite of monoidal natural isomorphisms is monoidal. -/
lemma isMonoidal_trans_hom {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    [H.LaxMonoidal] (e₁ : F ≅ G) (e₂ : G ≅ H) (h₁ : IsMonoidal e₁.hom)
    (h₂ : IsMonoidal e₂.hom) : IsMonoidal (e₁ ≪≫ e₂).hom := by
  rw [Iso.trans_hom]
  infer_instance

/-- The inverse of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_symm_hom {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (e : F ≅ G) (h : IsMonoidal e.hom) : IsMonoidal e.symm.hom := by
  rw [Iso.symm_hom]
  infer_instance

/-- A whiskering of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_isoWhiskerLeft_hom {E : Type*} [Category E] [MonoidalCategory E]
    (F : C ⥤ D) {G H : D ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : G ≅ H) (h : IsMonoidal e.hom) : IsMonoidal (Functor.isoWhiskerLeft F e).hom := by
  rw [Functor.isoWhiskerLeft_hom]
  infer_instance

/-- A whiskering of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_isoWhiskerRight_hom {E : Type*} [Category E] [MonoidalCategory E]
    {F G : C ⥤ D} (H : D ⥤ E) [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ≅ G) (h : IsMonoidal e.hom) : IsMonoidal (Functor.isoWhiskerRight e H).hom := by
  rw [Functor.isoWhiskerRight_hom]
  infer_instance

end CategoryTheory.NatTrans

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (j : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
  (c : a.hom ≫ j = j ≫ b.hom)

/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` is monoidal. -/
instance isMonoidal_upperStarExchangeIso_hom :
    NatTrans.IsMonoidal (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom :=
  NatTrans.isMonoidal_trans_hom _ _
    (NatTrans.isMonoidal_isoWhiskerLeft_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance))
    (NatTrans.isMonoidal_trans_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance)
      (NatTrans.isMonoidal_trans_hom _ _ inferInstance
        (NatTrans.isMonoidal_trans_hom _ _ inferInstance
          (NatTrans.isMonoidal_isoWhiskerRight_hom _ _ inferInstance))))

/-- The components of the exchange isomorphism. -/
lemma upperStarExchangeIso_hom_app (M) :
    (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*[WeilCoefficients.{u} l].obj M) ≫
        (upperStarComp _ a.hom j).inv.app M ≫ (upperStarCongr _ c).hom.app M ≫
        (upperStarComp _ j b.hom).hom.app M ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M) := by
  simp only [upperStarExchangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]

-- Stated for a variable isomorphism `α`: for `α = upperStarIsoLowerStarInv` the kernel times out
-- comparing the two objects.
private lemma inv_app_adicUpperStar_obj_X
    {P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (α : P ≅ Q)
    (M : AdicSheaf l Y) :
    α.inv.app ((j)^*ᵃ[l].obj M).X = α.inv.app ((j)^*[WeilCoefficients.{u} l].obj M.X) :=
  rfl

variable (l) in
/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` of `ℓ`-adic pullbacks along a
commutative square `a ≫ j = j ≫ b` with `a`, `b` isomorphisms. -/
noncomputable abbrev adicUpperStarExchangeIso :
    (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _

/-- The exchange isomorphism of `ℓ`-adic pullbacks is, on underlying sheaves, the exchange
isomorphism `AlgebraicGeometry.ProEtale.upperStarExchangeIso`. Stated for arbitrary `j`, `a`,
`b`: for the geometric Frobenii the kernel times out on the same proof. -/
lemma adicUpperStarExchangeIso_hom_app_hom (M : AdicSheaf l Y) :
    ((adicUpperStarExchangeIso l j a b c).hom.app M).hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M.X := by
  rw [upperStarExchangeIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]
  rw [inv_app_adicUpperStar_obj_X]

variable {j a b c}

variable (l) in
/-- The structure isomorphism `(b⁻¹)_* 𝓗om(A, B) ≅ 𝓗om(A, B)` induced by isomorphisms
`(b⁻¹)_* A ≅ A` and `(b⁻¹)_* B ≅ B`; for the geometric Frobenius `b` this is the Weil
structure of `AlgebraicGeometry.ProEtaleWeilSheaf.ihom`. -/
noncomputable abbrev ihomStr {Z : Scheme.{u}} (b : Z ≅ Z) {A B : AdicSheaf l Z}
    (sA : (b.inv)_*ᵃ[l].obj A ≅ A) (sB : (b.inv)_*ᵃ[l].obj B ≅ B) :
    (b.inv)_*ᵃ[l].obj ((AdicSheaf.ihom A).obj B) ≅ (AdicSheaf.ihom A).obj B :=
  (adicLowerStarCompIhomIso l b.inv A).symm.app B ≪≫ (Mod.ihomMapIso sA.symm).app _ ≪≫
    (AdicSheaf.ihom A).mapIso sB

/-- The evaluation `𝓗om(A, B) ⊗ A ⟶ B` is compatible with the structure isomorphisms. -/
lemma ihomStr_evaluation {Z : Scheme.{u}} (b : Z ≅ Z) {A B : AdicSheaf l Z}
    (sA : (b.inv)_*ᵃ[l].obj A ≅ A) (sB : (b.inv)_*ᵃ[l].obj B ≅ B) :
    ((ihomStr l b sA sB).hom.hom ⊗ₘ sA.hom.hom) ≫ Mod.evaluation A B =
      μ (b.inv)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom A).obj B).X A.X ≫
        (b.inv)_*[WeilCoefficients.{u} l].map (Mod.evaluation A B) ≫ sB.hom.hom := by
  have : (Mod.mapModComap (G := (b.inv)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l b.inv)).IsEquivalence := isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l b.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) A B
  have hstr : (ihomStr l b sA sB).hom.hom =
      ((adicLowerStarCompIhomIso l b.inv A).inv.app B).hom ≫
      ((Mod.ihomMap sA.inv).app _).hom ≫ ((AdicSheaf.ihom A).map sB.hom).hom := rfl
  have hφ : sA.hom.hom ≫ sA.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality A sB.hom, Mod.evaluation_ihomMap_assoc sA.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

variable (l c) in
/-- The structure isomorphism `(a⁻¹)_* j^* M ≅ j^* M` induced by `(b⁻¹)_* M ≅ M` along the
exchange isomorphism; for the geometric Frobenii this is the Weil structure of
`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar`. -/
noncomputable abbrev upperStarStr {M : AdicSheaf l Y} (sM : (b.inv)_*ᵃ[l].obj M ≅ M) :
    (a.inv)_*ᵃ[l].obj ((j)^*ᵃ[l].obj M) ≅ (j)^*ᵃ[l].obj M :=
  (adicUpperStarExchangeIso l j a b c).app M ≪≫ (j)^*ᵃ[l].mapIso sM

lemma upperStarStr_hom_hom {M : AdicSheaf l Y} (sM : (b.inv)_*ᵃ[l].obj M ≅ M) :
    (upperStarStr l c sM).hom.hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M.X ≫
        (j)^*[WeilCoefficients.{u} l].map sM.hom.hom := by
  rw [Iso.trans_hom, Mod.comp_hom', Iso.app_hom, adicUpperStarExchangeIso_hom_app_hom,
    Functor.mapIso_hom, adicUpperStar_map_hom]

/-- **Pullbacks of compatible pairings are compatible.** -/
theorem upperStarStr_pairing {P Q R : AdicSheaf l Y} (sP : (b.inv)_*ᵃ[l].obj P ≅ P)
    (sQ : (b.inv)_*ᵃ[l].obj Q ≅ Q) (sR : (b.inv)_*ᵃ[l].obj R ≅ R)
    (e : P.X ⊗ Q.X ⟶ R.X)
    (h : (sP.hom.hom ⊗ₘ sQ.hom.hom) ≫ e =
      μ (b.inv)_*[WeilCoefficients.{u} l] P.X Q.X ≫ (b.inv)_*[_].map e ≫ sR.hom.hom) :
    ((upperStarStr l c sP).hom.hom ⊗ₘ (upperStarStr l c sQ).hom.hom) ≫
        (μ (j)^*[WeilCoefficients.{u} l] P.X Q.X ≫ (j)^*[_].map e) =
      μ (a.inv)_*[WeilCoefficients.{u} l] ((j)^*[_].obj P.X) ((j)^*[_].obj Q.X) ≫
        (a.inv)_*[_].map (μ (j)^*[WeilCoefficients.{u} l] P.X Q.X ≫ (j)^*[_].map e) ≫
          (upperStarStr l c sR).hom.hom := by
  have hψ := NatTrans.IsMonoidal.tensor
    (τ := (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom) P.X Q.X
  have nψ := (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.naturality e
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj] at hψ nψ
  rw [upperStarStr_hom_hom, upperStarStr_hom_hom, upperStarStr_hom_hom,
    ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hψ, reassoc_of% nψ]

/-- **The comparison `j^* 𝓗om(A, B) ⟶ 𝓗om(j^* A, j^* B)` is compatible with the structure
isomorphisms** induced by `(b⁻¹)_* A ≅ A` and `(b⁻¹)_* B ≅ B`. -/
theorem adicUpperStarIhomComparison_str {A B : AdicSheaf l Y} (sA : (b.inv)_*ᵃ[l].obj A ≅ A)
    (sB : (b.inv)_*ᵃ[l].obj B ≅ B) :
    (a.inv)_*ᵃ[l].map (adicUpperStarIhomComparison l j A B) ≫
        (ihomStr l a (upperStarStr l c sA) (upperStarStr l c sB)).hom =
      (upperStarStr l c (ihomStr l b sA sB)).hom ≫ adicUpperStarIhomComparison l j A B := by
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom]
  apply Mod.hom_ext_of_evaluation
  have : IsIso (upperStarStr l c sA).hom.hom :=
    inferInstanceAs (IsIso ((Mod.forget _).map (upperStarStr l c sA).hom))
  have h1 := ihomStr_evaluation a (upperStarStr l c sA) (upperStarStr l c sB)
  have h2 := upperStarStr_pairing (c := c) (ihomStr l b sA sB) sA sB (Mod.evaluation A B)
    (ihomStr_evaluation b sA sB)
  have h3 := uncurryHom_adicUpperStarIhomComparison j A B
  rw [Mod.uncurryHom] at h3
  rw [← cancel_epi (_ ◁ (upperStarStr l c sA).hom.hom), comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← tensorHom_def'_assoc, h1, comp_whiskerRight_assoc,
    ← tensorHom_def'_assoc]
  erw [h3, h2, ← h3]
  exact μ_natural_left_assoc (a.inv)_*[WeilCoefficients.{u} l]
    (adicUpperStarIhomComparison l j A B).hom _ _

end AlgebraicGeometry.ProEtale
