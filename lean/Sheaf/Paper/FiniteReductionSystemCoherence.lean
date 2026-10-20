/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteReductionSystem
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
import Sheaf.Paper.FiniteReductionFlatExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! Compatibility of the normalized comparison with successive coefficient reduction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u vC vD vH uC uD uH
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.FiniteReduction

attribute [local irreducible] extend

private theorem conj_id {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (a₁ : L₁ ⊣ R) (a₂ : L₂ ⊣ R) :
    conjugateEquiv a₂ a₁ (Adjunction.leftAdjointUniq a₁ a₂).hom = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv]
private theorem conj_iso {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv a₁ a₂ (Adjunction.leftAdjointUniq (a₁.ofNatIsoRight e) a₂).inv = e.hom := by
  ext X
  rw [conjugateEquiv_apply_app]
  rw [Adjunction.leftAdjointUniq_inv_app, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality, ← Category.assoc,
    a₁.right_triangle_components, Category.id_comp]

private theorem ordinary_coherence (T : Scheme.{u}) (l : ℕ)
    (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) :
    (ordinaryComparison T (quotient l hnm)).hom.app
        ((extend T.smallEtaleTopology (quotient l hmr)).obj Q) ≫
      (extend (Scheme.ProEt.topology T) (quotient l hnm)).map
        ((ordinaryComparison T (quotient l hmr)).hom.app Q) ≫
      (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T).obj Q) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l n)) T).map
        ((ordinaryAssociator T.smallEtaleTopology l hmr hnm).hom.app Q) ≫
      (ordinaryComparison T (quotient l (hnm.trans hmr))).hom.app Q := by
  have hq : quotient.{u} l (hnm.trans hmr) =
      (quotient.{u} l hnm).comp (quotient.{u} l hmr) := by
    apply RingHom.ext
    intro x
    change (⟨⟨ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n))
        x.down.down⟩⟩ : Coeff.{u} l n) =
      ⟨⟨ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))
        (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m)) x.down.down)⟩⟩
    congr 2
    exact DFunLike.congr_fun (Subsingleton.elim
      (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
      ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
        (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down
  have hE := conj_iso
    ((extendAdjunction T.smallEtaleTopology (quotient l hmr)).comp
      (extendAdjunction T.smallEtaleTopology (quotient l hnm)))
    (extendAdjunction T.smallEtaleTopology (quotient l (hnm.trans hmr)))
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology (quotient l hmr) (quotient l hnm)
      (quotient l (hnm.trans hmr)) hq)
  change conjugateEquiv _ _
    (ordinaryAssociator T.smallEtaleTopology l hmr hnm).inv = _ at hE
  have hP := conj_iso
    ((extendAdjunction (Scheme.ProEt.topology T) (quotient l hmr)).comp
      (extendAdjunction (Scheme.ProEt.topology T) (quotient l hnm)))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l (hnm.trans hmr)))
    (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) (quotient l hmr) (quotient l hnm)
      (quotient l (hnm.trans hmr)) hq)
  change conjugateEquiv _ _
    (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).inv = _ at hP
  have hC (s t : ℕ) (h : t ≤ s) :
      conjugateEquiv
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l s)) T).comp
          (extendAdjunction (Scheme.ProEt.topology T) (quotient l h)))
        ((extendAdjunction T.smallEtaleTopology (quotient l h)).comp
          (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l t)) T))
        (ordinaryComparison T (quotient l h)).hom = 𝟙 _ := by
    exact conj_id _ _
  have hp := conjugateEquiv_paste
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l r)) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l m)) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l n)) T)
    (extendAdjunction T.smallEtaleTopology (quotient l hmr))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l hmr))
    (extendAdjunction T.smallEtaleTopology (quotient l hnm))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l hnm))
    (extendAdjunction T.smallEtaleTopology (quotient l (hnm.trans hmr)))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l (hnm.trans hmr)))
    (ordinaryComparison T (quotient l hmr)).hom
    (ordinaryComparison T (quotient l hnm)).hom
    (ordinaryComparison T (quotient l (hnm.trans hmr))).hom
    (ordinaryAssociator T.smallEtaleTopology l hmr hnm).inv
    (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).inv (by
      rw [hE, hP]
      rw [hC, hC, hC]
      simp only [Category.comp_id]
      ext F U x
      rfl)
  have hQ := congr_app hp Q
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hQ
  apply (cancel_epi ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (Coeff.{u} l n)) T).map
      ((ordinaryAssociator T.smallEtaleTopology l hmr hnm).inv.app Q))).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  apply (cancel_mono ((ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).inv.app
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T).obj Q))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hQ

attribute [local irreducible] ordinaryComparison ordinaryAssociator

private theorem coherent_on_flat_complex
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (S : System T l)
    (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ)
    (hkQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hfQ : ∀ i, ObjectProperty.flat (Q.X i))
    (hkQm : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hfQm : ∀ i, ObjectProperty.flat
      ((((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q).X i))
    (hkQc : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapHomologicalComplex (.up ℤ)).obj Q))
    (hfQc : ∀ i, ObjectProperty.flat
      ((((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapHomologicalComplex (.up ℤ)).obj Q).X i)) :
    S.CoherentAt r m n hmr hnm (DerivedCategory.Q.obj Q) := by
  let Cr := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T
  let Cn := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l n)) T
  let Er := extend T.smallEtaleTopology (quotient.{u} l hmr)
  let Pm := extend (Scheme.ProEt.topology T) (quotient.{u} l hnm)
  let Qm := (Er.mapHomologicalComplex (.up ℤ)).obj Q
  let Qc := (Cr.mapHomologicalComplex (.up ℤ)).obj Q
  have he : IsIso ((S.proetale r n (hnm.trans hmr)).counit.app Qc) :=
    (S.proetale r n (hnm.trans hmr)).computation Qc hkQc
  let t := (S.proetale r n (hnm.trans hmr)).functor.map
      (Cr.mapDerivedCategoryFactors.hom.app Q) ≫
    (S.proetale r n (hnm.trans hmr)).counit.app Qc
  have : IsIso t := inferInstance
  have na := (S.proetaleAssociator r m n hmr hnm).hom.naturality
    (Cr.mapDerivedCategoryFactors.hom.app Q)
  have nc := (S.comparison m n hnm).hom.naturality ((S.etale r m hmr).counit.app Q)
  have ne := (S.proetale m n hnm).counit.naturality
    ((ordinaryComparisonComplex T (quotient l hmr)).hom.app Q)
  have nd := Cn.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex
      (ordinaryAssociator T.smallEtaleTopology l hmr hnm) (.up ℤ)).hom.app Q)
  have ho :
      (ordinaryComparisonComplex T (quotient l hnm)).hom.app Qm ≫
        (Pm.mapHomologicalComplex (.up ℤ)).map
          ((ordinaryComparisonComplex T (quotient l hmr)).hom.app Q) ≫
        (NatIso.mapHomologicalComplex
          (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm) (.up ℤ)).hom.app Qc =
      (Cn.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex
            (ordinaryAssociator T.smallEtaleTopology l hmr hnm) (.up ℤ)).hom.app Q) ≫
        (ordinaryComparisonComplex T (quotient l (hnm.trans hmr))).hom.app Q := by
    ext i : 1
    exact ordinary_coherence T l r m n hmr hnm (Q.X i)
  dsimp only [System.CoherentAt]
  apply (cancel_mono t).mp
  dsimp only [t]
  simp only [Category.assoc]
  rw [← reassoc_of% na, S.proetaleAssociator_model r m n hmr hnm Qc hkQc hfQc]
  simp only [← Functor.map_comp_assoc]
  rw [S.comparison_model r m hmr Q hkQ hfQ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nc]
  erw [reassoc_of% ne,
    reassoc_of% (S.comparison_model m n hnm Qm hkQm hfQm)]
  rw [S.comparison_model r n (hnm.trans hmr) Q hkQ hfQ]
  simp only [← Functor.map_comp_assoc]
  rw [S.etaleAssociator_model r m n hmr hnm Q hkQ hfQ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nd]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [ho]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem flat_resolution_terms
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (Λ₀ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C))
    (P : CochainComplex C ℤ) :
    ∀ i, ObjectProperty.flat ((Λ₀.reduced.resolutionFunctor.obj P).X i) := by
  let : (ObjectProperty.flat (A := C)).IsClosedUnderColimitsOfShape ℤ :=
    CochainComplex.closedUnderColimitsOfShape_flat C ℤ
  let p := Λ₀.reduced.colimitOfShapeFlatResolutionFunctorObj
    ObjectProperty.flat.essImage_ι_le P
  intro i
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) p.isColimit)
    (fun j ↦ (p.prop_diag_obj j).1 i)

private theorem exists_common_flat_resolution
    {C : Type uC} {D : Type uD} {H : Type uH}
    [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
    [Abelian C] [Abelian D] [Abelian H]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [IsGrothendieckAbelian.{vH} H]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [MonoidalCategory H] [MonoidalPreadditive H] [MonoidalClosed H] [BraidedCategory H]
    [Abelian.HasFunctorialFlatResolution C]
    (F : C ⥤ D) (G : C ⥤ H) [F.Additive] [G.Additive]
    [F.PreservesFlat] [G.PreservesFlat] [F.IsLeftAdjoint] [G.IsLeftAdjoint]
    (P : CochainComplex C ℤ) :
    ∃ (Q : CochainComplex C ℤ) (π : Q ⟶ P), QuasiIso π ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q ∧
      (∀ i, ObjectProperty.flat (Q.X i)) ∧
      (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) ∧
      (∀ i, ObjectProperty.flat (((F.mapHomologicalComplex (.up ℤ)).obj Q).X i)) ∧
      (HomologicalComplex.quasiIso H (.up ℤ)).kFlat
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) ∧
      (∀ i, ObjectProperty.flat (((G.mapHomologicalComplex (.up ℤ)).obj Q).X i)) := by
  let Λ₀ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  let Λ := Λ₀.reduced
  let Q := Λ.resolutionFunctor.obj P
  have hfQ : ∀ i, ObjectProperty.flat (Q.X i) := flat_resolution_terms Λ₀ P
  exact ⟨Q, Λ.resolutionNatTrans.app P, inferInstance,
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P, hfQ,
    F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
      ObjectProperty.flat.essImage_ι_le P,
    fun i ↦ Functor.PreservesFlat.flat_obj (F := F) (hfQ i),
    G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
      ObjectProperty.flat.essImage_ι_le P,
    fun i ↦ Functor.PreservesFlat.flat_obj (F := G) (hfQ i)⟩

/-- The representative normalizations force compatibility with successive reduction.
Source: blueprint sk-lem-sp-reduction, final sentence of its first paragraph;
Stacks Tags 03EL, 06YT and 06YY
(blueprint: lem-pur-finite-reduction-system-coherence).

Proof: choose a functorial flat K-flat resolution Q of a complex representing K.
Extension of scalars preserves flat terms; applying the reduced flat resolution and
comparison pullback gives K-flat complexes on which all the counits are invertible.
First check the ordinary comparison-associator square: conjugate both routes through
the extension/restriction and site-comparison adjunctions. The conjugates are the same
restriction map, since restriction of scalars is sectionwise and its composition
comparison is the identity on sections. Thus the ordinary routes agree; equivalently
both send (q tensor b) tensor c to the image of q tensored with bc.
Postcompose the desired derived square at Q by the comparison factorization followed
by the counit for direct reduction r to n. Both are invertible on this resolution.
Naturality moves the factorization through the pro-etale associator. Use the three
normalization equations of System, at Q, its first coefficient extension, and its
comparison pullback. Naturality of the counit and of the exact comparison factorization
reduces the two composites to Q applied to the ordinary square just checked.
Cancel the invertible maps. Finally naturality transports equality along the
isomorphism from Q to K. Identity reductions, exponent zero, and the zero complex
are included in the same argument. No constructibility or Tor bound is used. -/
theorem System.coherentAt (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (S : System T l) (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (K : DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))) :
    S.CoherentAt r m n hmr hnm K := by
  let C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))
  let P := DerivedCategory.Q.objPreimage K
  let Er := extend T.smallEtaleTopology (quotient.{u} l hmr)
  let Cr := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T
  let Cn := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l n)) T
  have hq : Function.Surjective (quotient.{u} l hmr) := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow l hmr) y.down.down
    exact ⟨⟨⟨x⟩⟩, congrArg (fun z ↦ (⟨⟨z⟩⟩ : Coeff.{u} l m)) hx⟩
  let : Er.PreservesFlat := ⟨fun hX ↦
    flat_extend_of_surjective T.smallEtaleTopology (quotient l hmr) hq hX⟩
  let : Er.IsLeftAdjoint := (extendAdjunction T.smallEtaleTopology (quotient l hmr)).isLeftAdjoint
  obtain ⟨Q, π, hπ, hkQ, hfQ, hkQm, hfQm, hkQc, hfQc⟩ :=
    exists_common_flat_resolution Er Cr P
  let := hπ
  let α : (S.etale r m hmr).functor ⋙ (S.etale m n hnm).functor ⋙ Cn.mapDerivedCategory ⟶
      Cr.mapDerivedCategory ⋙ (S.proetale r n (hnm.trans hmr)).functor :=
    Functor.whiskerLeft (S.etale r m hmr).functor (S.comparison m n hnm).hom ≫
      Functor.whiskerRight (S.comparison r m hmr).hom (S.proetale m n hnm).functor ≫
      Functor.whiskerLeft Cr.mapDerivedCategory (S.proetaleAssociator r m n hmr hnm).hom
  let β : (S.etale r m hmr).functor ⋙ (S.etale m n hnm).functor ⋙ Cn.mapDerivedCategory ⟶
      Cr.mapDerivedCategory ⋙ (S.proetale r n (hnm.trans hmr)).functor :=
    Functor.whiskerRight (S.etaleAssociator r m n hmr hnm).hom Cn.mapDerivedCategory ≫
      (S.comparison r n (hnm.trans hmr)).hom
  have hres : α.app (DerivedCategory.Q.obj Q) = β.app (DerivedCategory.Q.obj Q) := by
    exact coherent_on_flat_complex T l S r m n hmr hnm Q hkQ hfQ hkQm hfQm hkQc hfQc
  let e : DerivedCategory.Q.obj Q ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have h : α.app K = β.app K := by
    apply (cancel_epi
      (((S.etale r m hmr).functor ⋙
        (S.etale m n hnm).functor ⋙ Cn.mapDerivedCategory).map e.hom)).mp
    rw [α.naturality, β.naturality, hres]
  exact h

end AlgebraicGeometry.FiniteReduction
