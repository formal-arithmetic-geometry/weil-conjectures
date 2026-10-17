/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.WeilSheaf.LisseDuality
public import WeilConjectures.WeilSheaf.UpperStarTensor

/-!
# Pullbacks of duals of lisse Weil sheaves

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback of the constant pro-étale Weil sheaf
`ℚ̄_ℓ` is `ℚ̄_ℓ` (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarAdicConstantIso`), and the pullback
of the dual of a lisse Weil sheaf is the dual of its pullback
(`AlgebraicGeometry.WeilSheaf.upperStarDualIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal MonObj

namespace AlgebraicGeometry

open ProEtale Endofunctor

open scoped Obj

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtale

attribute [local instance] Abelian.hasFiniteBiproducts

open ZeroObject in
/-- **A lisse sheaf whose stalks all vanish is zero.** Here the stalk at a point `y` is taken at
a geometric point over `y` with values in an algebraic closure of the residue field. -/
theorem IsAdicLisseSheaf.isZero_of_forall_subsingleton {Y : Scheme.{u}} {H : AdicSheaf l Y}
    (hH : IsAdicLisseSheaf H)
    (h : ∀ y : Y, ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (s : Spec (.of K) ⟶ Y),
      s.base (IsLocalRing.closedPoint K) = y ∧
        Subsingleton ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X))) :
    IsZero H := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨κι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : κι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  have hn (i i' : κι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 H) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  have hsurj : ∀ y, ∃ j, y ∈ Set.range (f j) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  have hz (i : κι) : IsZero ((f i)^*ᵃ[l].obj H) := by
    by_cases hV : Nonempty (V i)
    · obtain ⟨v⟩ := hV
      suffices h0 : n i = 0 by
        refine IsZero.of_iso ?_ (e i).some
        rw [h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      by_contra hpos
      obtain ⟨K, _, _, s, hs, hsub⟩ := h (f i v)
      obtain ⟨j, w, hw⟩ := hsurj (s.base (IsLocalRing.closedPoint K))
      have hnj : 0 < n j := (hn j i w v (hw.trans hs)) ▸ Nat.pos_of_ne_zero hpos
      have := nontrivial_globalSections_upperStar_of_iso (f j) (e j).some hnj s ⟨w, hw⟩
      exact not_subsingleton _ hsub
    · have : IsEmpty (V i) := not_nonempty_iff.1 hV
      exact isZero_adicSheaf_of_isEmpty l _
  have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
    have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
    rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
    infer_instance
  exact (isZero_zero _).of_iso (asIso (0 : H ⟶ 0))

end ProEtale

namespace ProEtaleWeilSheaf

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "σX" => (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "σY" => (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "W" => WeilCoefficients.{u} l

/-- The Weil structure of the constant pro-étale Weil sheaf `ℚ̄_ℓ` preserves the unit section. -/
lemma adicConstant_one_str {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))] :
    ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W].map
          (η : 𝟙_ _ ⟶ adicConstantSheaf l (S ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (ProEtaleWeilSheaf.adicConstant k₀ l S).str.hom.hom =
        (η : 𝟙_ _ ⟶ adicConstantSheaf l (S ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  set e := (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm
  have : IsMonHom (adicConstantSheafLowerStarIso l e).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l e.hom))
  have : IsMonHom (adicConstantSheafLowerStarIso l e).hom := by
    have : IsMonHom (inv (adicConstantSheafLowerStarIso l e).inv) := inferInstance
    rwa [IsIso.Iso.inv_inv] at this
  exact IsMonHom.one_hom (f := (adicConstantSheafLowerStarIso l e).hom)

/-- A section of a pro-étale Weil sheaf is compatible with the Weil structure in pushforward form
if and only if it is in pullback form. -/
lemma unit_str_iff {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]
    (P : ProEtaleWeilSheaf k₀ l S) (e : 𝟙_ _ ⟶ P.carrier.X) :
    ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W].map e ≫
        P.str.hom.hom = e ↔
      ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[W].map e ≫
        frobeniusStr P = e := by
  set ι' := upperStarIsoLowerStarInv W (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  have hu := NatTrans.IsMonoidal.unit (τ := ι'.hom)
  rw [frobeniusStr, ι'.hom.naturality_assoc, reassoc_of% hu]


/-- The pullback of a section compatible with the Weil structure is compatible with the Weil
structure, in pullback form. -/
lemma upperStar_unit_frobeniusStr (P : ProEtaleWeilSheaf k₀ l Y) (e : 𝟙_ _ ⟶ P.carrier.X)
    (he : ε ((σY).hom)^*[W] ≫ ((σY).hom)^*[W].map e ≫ frobeniusStr P = e) :
    ε ((σX).hom)^*[W] ≫ ((σX).hom)^*[W].map (ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e) ≫
        frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) =
      ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e := by
  set ψ := (upperStarComp W (σX).hom φ̄).symm ≪≫
    upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm ≪≫
    upperStarComp _ φ̄ (σY).hom
  have hψ : NatTrans.IsMonoidal ψ.hom := by
    simp only [ψ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hfs : frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) = ψ.hom.app _ ≫
      (φ̄)^*[W].map (frobeniusStr P) := by
    rw [frobeniusStr_upperStar]
    simp [ψ]
  have hψu := NatTrans.IsMonoidal.unit (τ := ψ.hom)
  simp only [Functor.LaxMonoidal.comp_ε] at hψu
  have hn := ψ.hom.naturality e
  simp only [Functor.comp_map] at hn
  rw [hfs, Functor.map_comp_assoc, reassoc_of% hn, reassoc_of% hψu, ← Functor.map_comp,
    ← Functor.map_comp, he]

/-- The pullback of a section compatible with the Weil structure is compatible with the Weil
structure. -/
lemma upperStar_unit_str (P : ProEtaleWeilSheaf k₀ l Y) (e : 𝟙_ _ ⟶ P.carrier.X)
    (he : ε ((σY).inv)_*[W] ≫ ((σY).inv)_*[W].map e ≫ P.str.hom.hom = e) :
    ε ((σX).inv)_*[W] ≫ ((σX).inv)_*[W].map (ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e) ≫
        ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).str.hom.hom =
      ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e :=
  (unit_str_iff _ _).2 (upperStar_unit_frobeniusStr φ P e ((unit_str_iff P e).1 he))

/-- The isomorphism `φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ` is compatible with the Weil structures. -/
lemma adicUpperStarUnitIso_str :
    (WeilSheaf.frobeniusPullback k₀ l X).map (adicUpperStarUnitIso l φ̄).hom ≫
        (ProEtaleWeilSheaf.adicConstant k₀ l X).str.hom =
      ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj (ProEtaleWeilSheaf.adicConstant k₀ l Y)).str.hom ≫
        (adicUpperStarUnitIso l φ̄).hom := by
  set u := adicUpperStarUnitIso l φ̄
  set K := (adicLowerStarUnitIso l (σX).symm).symm ≪≫
    (WeilSheaf.frobeniusPullback k₀ l X).mapIso u.symm
  rw [← cancel_epi K.hom]
  apply Mod.regular_hom_ext
  have hL : K.hom ≫ (WeilSheaf.frobeniusPullback k₀ l X).map u.hom ≫
      (ProEtaleWeilSheaf.adicConstant k₀ l X).str.hom = 𝟙 _ := by
    simp only [K, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact (adicLowerStarUnitIso l (σX).symm).inv_hom_id
  rw [hL, Mod.id_hom']
  erw [Category.comp_id]
  set e := (σX).symm
  have : IsMonHom (adicConstantSheafLowerStarIso l e).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l e.hom))
  have h1 : (η : 𝟙_ _ ⟶ adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
      (adicConstantSheafLowerStarIso l e).inv = ε ((σX).inv)_*[W] ≫ ((σX).inv)_*[W].map η :=
    IsMonHom.one_hom _
  have : IsMonHom (adicUpperStarRingIso (l := l) φ̄) :=
    inferInstanceAs (IsMonHom (inv (((ProEtale.upperStarLowerStarAdjunction W φ̄).homEquiv _ _).symm
      (adicConstantSheafToLowerStar l φ̄))))
  have h2 : (η : 𝟙_ _ ⟶ adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
      adicUpperStarRingIso (l := l) φ̄ = ε (φ̄)^*[W] ≫ (φ̄)^*[W].map η :=
    IsMonHom.one_hom _
  have h3 := upperStar_unit_str φ (ProEtaleWeilSheaf.adicConstant k₀ l Y)
    (η : 𝟙_ _ ⟶ adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (adicConstant_one_str (S := Y))
  have h4 : (ε (φ̄)^*[W] ≫ (φ̄)^*[W].map
      (η : 𝟙_ _ ⟶ adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ≫
      u.hom.hom =
        (η : 𝟙_ _ ⟶ adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
    rw [← h2, Category.assoc]
    simp only [u, adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
    erw [IsIso.inv_hom_id]
    exact Category.comp_id _
  simp only [K, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Mod.comp_hom', Category.assoc]
  erw [adicLowerStar_map_hom]
  erw [reassoc_of% h1]
  rw [← Functor.map_comp_assoc]
  simp only [u, adicUpperStarUnitIso, Mod.regularIsoOfIsIso_inv_hom]
  erw [h2]
  rw [reassoc_of% h3]
  exact h4.symm

attribute [local instance] Sheaf.symmetricCategory in
/-- The comparison `φ^* [G, ℚ̄_ℓ] ⟶ [φ^* G, ℚ̄_ℓ]` is compatible with the Weil structures. -/
lemma adicUpperStarDualComparison_str (G : ProEtaleWeilSheaf k₀ l Y) :
    ((σX).inv)_*[W].map (adicUpperStarDualComparison l φ̄ G.carrier).hom ≫
        (ProEtaleWeilSheaf.ihom k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj G)
          (ProEtaleWeilSheaf.adicConstant k₀ l X)).str.hom.hom =
      ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj (ProEtaleWeilSheaf.ihom k₀ l Y G
          (ProEtaleWeilSheaf.adicConstant k₀ l Y))).str.hom.hom ≫
        (adicUpperStarDualComparison l φ̄ G.carrier).hom := by
  refine map_comp_ihom_str_of_uncurryHom (P := (ProEtaleWeilSheaf.upperStar k₀ l φ).obj
    (ProEtaleWeilSheaf.ihom k₀ l Y G (ProEtaleWeilSheaf.adicConstant k₀ l Y)))
    (M := (ProEtaleWeilSheaf.upperStar k₀ l φ).obj G) (N := ProEtaleWeilSheaf.adicConstant k₀ l X)
    (adicUpperStarDualComparison l φ̄ G.carrier) ?_
  have hp := upperStar_pairing_str φ (ProEtaleWeilSheaf.ihom k₀ l Y G
    (ProEtaleWeilSheaf.adicConstant k₀ l Y)) G (ProEtaleWeilSheaf.adicConstant k₀ l Y)
    (Mod.evaluation G.carrier (ProEtaleWeilSheaf.adicConstant k₀ l Y).carrier)
    (ihom_evaluation_str G (ProEtaleWeilSheaf.adicConstant k₀ l Y))
  have hu := congrArg Mod.Hom.hom (adicUpperStarUnitIso_str (k₀ := k₀) (l := l) φ)
  rw [Mod.comp_hom', Mod.comp_hom'] at hu
  erw [adicLowerStar_map_hom] at hu
  rw [uncurryHom_adicUpperStarDualComparison]
  erw [reassoc_of% hp]
  erw [← hu]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end ProEtaleWeilSheaf

end AlgebraicGeometry
