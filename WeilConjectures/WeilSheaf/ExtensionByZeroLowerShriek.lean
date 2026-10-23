/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LocalizationLowerShriek

/-!
# The direct image with compact support along an open immersion

For a quasi-compact open immersion `j : U ⟶ X` of `k₀`-schemes and a Weil sheaf `G` on `U`, the
direct image with compact support `Rj₀!(G[0])`, computed on the compactification
`U ⟶[a] W ⟶[g] X` of `j` chosen by Nagata's theorem, is the extension by zero `(j₀! G)[0]`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`,
clause 2 of the blueprint theorem `prop-functor-package`).

By proper base change, `Rg_* a_! ≅ j_!` for the left adjoint `j_!` of `j^*` on pro-étale Weil
sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_rightDerivedLowerStar_extensionByZero_iso`,
using the reduced closed complement of `j`). This left adjoint is the extension by zero
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLeftAdjoint_eq_extensionByZero`): the two
Frobenius exchange isomorphisms of `j̄_!` agree, since the two exchange isomorphisms of `j̄^*`
from which they are built are mates along the Frobenius equivalences
(`AlgebraicGeometry.ProEtale.leftMateIso_adicUpperStarGeometricFiberMapCompFrobeniusIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Mates along adjoint autoequivalences: let `E₁` and `E₂` be autoequivalences of `D` and `C`
and `R : D ⥤ C`. If the mate of `β : R ⋙ E₂⁻¹ ≅ E₁⁻¹ ⋙ R` along the adjunctions `E⁻¹ ⊣ E` is
`γ⁻¹` for `γ : R ⋙ E₂ ≅ E₁ ⋙ R`, then the mate of `γ` along the adjunctions `E ⊣ E⁻¹` is
`β⁻¹`. -/
lemma mateEquiv_toAdjunction_natTrans_eq_of_mateEquiv_symm (E₁ : D ≌ D) (E₂ : C ≌ C)
    (R : D ⥤ C) (β : R ⋙ E₂.inverse ≅ E₁.inverse ⋙ R) (γ : R ⋙ E₂.functor ≅ E₁.functor ⋙ R)
    (h : (mateEquiv E₁.symm.toAdjunction E₂.symm.toAdjunction
      (TwoSquare.mk _ _ _ _ β.hom)).natTrans = γ.inv) :
    (mateEquiv E₁.toAdjunction E₂.toAdjunction (TwoSquare.mk _ _ _ _ γ.hom)).natTrans =
      β.inv := by
  have hγ' (x : D) : γ.inv.app x = E₂.counitInv.app (R.obj (E₁.functor.obj x)) ≫
      E₂.functor.map (β.hom.app (E₁.functor.obj x)) ≫
        E₂.functor.map (R.map (E₁.unitInv.app x)) := by
    rw [← h]
    simp
  have hγ (x : D) : γ.hom.app x = E₂.functor.map (R.map (E₁.unit.app x)) ≫
      E₂.functor.map (β.inv.app (E₁.functor.obj x)) ≫
        E₂.counit.app (R.obj (E₁.functor.obj x)) := by
    rw [← cancel_mono (γ.inv.app x), Iso.hom_inv_id_app, hγ']
    simp [← Functor.map_comp]
  have hβ {d d' : D} (f : d ⟶ d') : β.inv.app d ≫ E₂.inverse.map (R.map f) =
      R.map (E₁.inverse.map f) ≫ β.inv.app d' :=
    (β.inv.naturality f).symm
  have hu {Y Y' : C} (f : Y ⟶ Y') {Z : C} (g : E₂.inverse.obj (E₂.functor.obj Y') ⟶ Z) :
      E₂.unit.app Y ≫ E₂.inverse.map (E₂.functor.map f) ≫ g = f ≫ E₂.unit.app Y' ≫ g :=
    (E₂.unit.naturality_assoc f g).symm
  have hc (Y : C) {Z : C} (g : E₂.inverse.obj Y ⟶ Z) :
      E₂.unit.app (E₂.inverse.obj Y) ≫ E₂.inverse.map (E₂.counit.app Y) ≫ g = g :=
    E₂.unit_inverse_comp_assoc Y g
  have hd (Y : D) :
      R.map (E₁.unit.app (E₁.inverse.obj Y)) ≫ R.map (E₁.inverse.map (E₁.counit.app Y)) =
        𝟙 _ := by
    rw [← R.map_comp]
    exact (congrArg R.map (E₁.unit_inverse_comp Y)).trans (R.map_id _)
  ext d
  have e₁ : (mateEquiv E₁.toAdjunction E₂.toAdjunction
      (TwoSquare.mk _ _ _ _ γ.hom)).natTrans.app d =
      E₂.unit.app (R.obj (E₁.inverse.obj d)) ≫ E₂.inverse.map (γ.hom.app (E₁.inverse.obj d)) ≫
        E₂.inverse.map (R.map (E₁.counit.app d)) := by
    simp
  rw [e₁, hγ, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hu, hu]
  simp only [Functor.comp_obj]
  rw [hc, hβ, ← Category.assoc, hd]
  exact Category.id_comp _

end CategoryTheory

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ]

/-- The two Frobenius exchange isomorphisms of the extension by zero `φ̄_!` along the base change
of an open immersion agree: the left mate of the exchange isomorphism of `φ̄^*` under
`φ̄_! ⊣ φ̄^*` is the exchange isomorphism
`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`,
defined as a conjugate along the Frobenius equivalences. -/
lemma leftMateIso_adicUpperStarGeometricFiberMapCompFrobeniusIso :
    IsoAlgebra.leftMateIso
        (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h) =
      adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h := by
  set jb := Scheme.Hom.geometricFiberMap φ h
  set adj := adicOpenImmersionLowerShriekAdjunction l jb
  set adjUL := adicUpperStarLowerStarAdjunction l jb
  set E₁ := adicLowerStarEquivalence l g.geometricGaloisFrobenius.symm
  set E₂ := adicLowerStarEquivalence l f.geometricGaloisFrobenius.symm
  set eR := adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h
  set eR' := adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso l φ h
  set eL := adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h
  -- the two exchange isomorphisms of `φ̄^*` are mates along the Frobenius equivalences
  have h₁ := iterated_mateEquiv_conjugateEquiv E₁.symm.toAdjunction E₂.symm.toAdjunction adjUL
    adjUL (TwoSquare.mk _ _ _ _ eR'.inv)
  rw [conjugateEquiv_adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso_inv,
    ← mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv] at h₁
  have hK := mateEquiv_toAdjunction_natTrans_eq_of_mateEquiv_symm E₁ E₂ (jb)^*ᵃ[l] eR'.symm eR
    (congrArg TwoSquare.natTrans ((mateEquiv _ _).injective h₁))
  have h₂ := iterated_mateEquiv_conjugateEquiv adj adj E₂.toAdjunction E₁.toAdjunction
    (TwoSquare.mk _ _ _ _ eL.inv)
  have h₃ : conjugateEquiv (adj.comp E₁.toAdjunction) (E₂.toAdjunction.comp adj) eL.inv =
      eR'.hom :=
    (conjugateEquiv _ _).apply_symm_apply _
  simp only [Iso.symm_inv] at hK
  rw [h₃, ← hK] at h₂
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv]
  simp only [IsoAlgebra.leftMateIso, Iso.symm_inv, asIso_hom]
  rw [← (mateEquiv E₁.toAdjunction E₂.toAdjunction).injective h₂]
  exact congrArg TwoSquare.natTrans ((mateEquiv adj adj).symm_apply_apply _)

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The left adjoint `j_!` of the pullback of pro-étale Weil sheaves along an open immersion `j`
is the extension by zero `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero`: both are the
extension by zero along `j̄`, with the same Weil structure. -/
lemma ProEtaleWeilSheaf.upperStarLeftAdjoint_eq_extensionByZero {U X : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j = ProEtaleWeilSheaf.extensionByZero k₀ l j := by
  rw [ProEtaleWeilSheaf.upperStarLeftAdjoint,
    ProEtale.leftMateIso_adicUpperStarGeometricFiberMapCompFrobeniusIso]
  rfl

attribute [local instance] Compactification.over

namespace WeilComplex

variable {X U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))]

/-- **The direct image with compact support along an open immersion is the extension by zero**
(blueprint: `prop-functor-package`, clause 2, compactification comparisons for
`Rf_! = Rf̄_* j_!` are independent of the refinement, applied to the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`; and `def-weil-extension-by-zero`). For a
quasi-compact open immersion `j` and a Weil sheaf `G` on `U`, `Rj₀!G ≅ j₀!G` in degree zero. -/
theorem nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l U) :
    Nonempty ((derivedLowerShriek k₀ l j).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.extensionByZero j).obj G)) := by
  let c := HasCompactification.compactification j (hf := hasCompactification_of_over (k₀ := k₀) j)
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  -- the reduced closed complement `i : Z ⟶ X` of `j`
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ :
      TopologicalSpace.Closeds X)
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨I.subschemeι ≫ X ↘ _⟩
  have : I.subschemeι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hij : IsCompl (Set.range j.base) (Set.range I.subschemeι.base) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simpa [I] using isCompl_compl
  -- `Rj₀! G = Rḡ_* ā_! G ≅ j_! G`
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nonempty_rightDerivedLowerStar_extensionByZero_iso j
    I.subschemeι c.i c.g c.comm.symm hij (WeilSheaf.toComplex.obj G).obj
    (WeilSheaf.toComplex.obj G).property
  refine ⟨ObjectProperty.isoMk _ (e ≪≫
    ((ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).mapDerivedCategorySingleFunctor 0).app
      G.obj ≪≫ (DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).mapIso
        (eqToIso (congrArg (fun F ↦ F.obj G.obj)
          (ProEtaleWeilSheaf.upperStarLeftAdjoint_eq_extensionByZero j))))⟩

end WeilComplex

end AlgebraicGeometry
