/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverOrdinaryKernel
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverOrdinaryEpi

/-! The ordinary derived tower open-cover boundary and its naturality.
Source: latest blueprint, sec-smooth-purity/sk-prop-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-complex-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

private theorem presentation_naturality
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {L : B ⥤ A} {R : A ⥤ B} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) {LD : DerivedCategory B ⥤ DerivedCategory A}
    (d : LD ⊣ R.mapDerivedCategory)
    {I J : CochainComplex A ℤ} {M N : DerivedCategory A}
    (eM : DerivedCategory.Q.obj I ≅ M) (eN : DerivedCategory.Q.obj J ≅ N)
    (h : M ⟶ N) (f : I ⟶ J)
    (hf : h ≫ eN.inv = eM.inv ≫ DerivedCategory.Q.map f) :
    LD.map (R.mapDerivedCategory.map h) ≫ (a.derivedPresentation d J eN).hom =
      (a.derivedPresentation d I eM).hom ≫ DerivedCategory.Q.map
        ((L.mapHomologicalComplex (.up ℤ)).map
          ((R.mapHomologicalComplex (.up ℤ)).map f)) := by
  have hR : R.mapDerivedCategory.map h ≫ R.mapDerivedCategory.map eN.inv ≫
        R.mapDerivedCategoryFactors.hom.app J =
      R.mapDerivedCategory.map eM.inv ≫ R.mapDerivedCategoryFactors.hom.app I ≫
        DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f) := by
    rw [← R.mapDerivedCategory.map_comp_assoc, hf,
      R.mapDerivedCategory.map_comp, Category.assoc]
    exact congrArg (fun k ↦ R.mapDerivedCategory.map eM.inv ≫ k)
      (R.mapDerivedCategoryFactors.hom.naturality f)
  have hL := L.mapDerivedCategoryFactors.hom.naturality
    ((R.mapHomologicalComplex (.up ℤ)).map f)
  dsimp only [Functor.comp_map] at hL
  have hu := (d.leftAdjointUniq a.onDerivedCategory).hom.naturality
    (R.mapDerivedCategory.map h)
  dsimp only [Adjunction.derivedPresentation, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hu]
  simp only [← L.mapDerivedCategory.map_comp_assoc]
  rw [hR]
  simp only [L.mapDerivedCategory.map_comp, Category.assoc]
  rw [hL]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- A short exact complex presentation of the normalized open-cover arrows.
This asserts neither a connecting morphism nor a distinguished triangle.

Source: latest blueprint, tower-geometric Gluing paragraph, and Stacks Tag 0152.
(blueprint: lem-dla1-tower-open-cover-complex-presentation).

Proof: Choose a K-injective representative J(M) of each derived tower using
Base.kinjective. For each degree of J(M), apply the site open-cover extension
sequence to the two subterminal opens, at each coefficient level. The comparison
from geometric opens to localized sites identifies the intersection by the given
pullback square. Its nested extension maps are the ordinary adjunction transposes;
compatibility with quotient scalar restriction makes them strict tower maps.
Componentwise exactness in Base.calculus gives a short exact sequence of towers.
Degreewise application yields T(M), with signs (+,-) in its first map. Exact
restriction and extension, the mapDerivedCategory comparison, and the chosen
Q(J(M)) ≅ M supply p, q, r. The termwise unit, counit and compositor equations in
Operations identify the two transported maps with first and second. For a derived
morphism h, full faithfulness of localization on K-injectives supplies a chain map
J(M) → J(N) representing it. Apply the three exact support functors to this chain
map and use the ordinary naturality squares to obtain g and the three displayed
comparison equations. No coherent choice of chain-map representatives is asserted.
The construction works for zero complexes and empty or repeated opens. -/
theorem tower_open_cover_complex_presentation {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (_intersection : IsPullback aU aV jU jV)
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (_cover : Set.range jU ∪ Set.range jV = Set.univ) :
    ∃ (T : SpTowerShriek.D l E X →
        ShortComplex (CochainComplex (SpTowerShriek.S l E X) ℤ))
      (_ht : ∀ M, (T M).ShortExact)
      (p : ∀ M, (support l E b o jW).obj M ≅ DerivedCategory.Q.obj (T M).X₁)
      (q : ∀ M, ((support l E b o jU).obj M ⊞ (support l E b o jV).obj M) ≅
        DerivedCategory.Q.obj (T M).X₂)
      (r : ∀ M, M ≅ DerivedCategory.Q.obj (T M).X₃),
      (∀ M, first l E b o aU aV jU jV jW wU wV M =
        (p M).hom ≫ DerivedCategory.Q.map (T M).f ≫ (q M).inv) ∧
      (∀ M, second l E b o jU jV M =
        (q M).hom ≫ DerivedCategory.Q.map (T M).g ≫
          (r M).inv) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N), ∃ g : T M ⟶ T N,
        (support l E b o jW).map h ≫ (p N).hom =
          (p M).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
        biprod.map ((support l E b o jU).map h) ((support l E b o jV).map h) ≫
            (q N).hom =
          (q M).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
        h ≫ (r N).hom = (r M).hom ≫ DerivedCategory.Q.map g.τ₃) := by
  classical
  let : Abelian.HasKInjectiveResolutions (SpTowerShriek.S l E X) := b.kinjective X
  have hrep (M : SpTowerShriek.D l E X) :=
    DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  choose I hI ei using hrep
  let e (M : SpTowerShriek.D l E X) : DerivedCategory.Q.obj (I M) ≅ M :=
    (Classical.choice (ei M)).symm
  let T M := ordinaryComplexSequence l E b o aU aV jU jV jW wU wV (I M)
  have ht (M) : (T M).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have hk := ordinarySequence_kernel l E b o aU aV jU jV jW
      _intersection wU wV _cover ((I M).X n)
    let s := ordinarySequence l E b o aU aV jU jV jW wU wV ((I M).X n)
    have hs : s.ShortExact :=
      { exact := hk.1
        mono_f := hk.2
        epi_g := ordinaryCounitSum_epi l E b o jU jV _cover ((I M).X n) }
    let H := HomologicalComplex.eval (SpTowerShriek.S l E X) (.up ℤ) n
    let p := H.mapBiprod
      (((o.openOp jU).extension.mapHomologicalComplex (.up ℤ)).obj
        (((o.geometry jU).pull.mapHomologicalComplex (.up ℤ)).obj (I M)))
      (((o.openOp jV).extension.mapHomologicalComplex (.up ℤ)).obj
        (((o.geometry jV).pull.mapHomologicalComplex (.up ℤ)).obj (I M)))
    apply ShortComplex.shortExact_of_iso _ hs
    refine ShortComplex.isoMk (Iso.refl _) p.symm (Iso.refl _) ?_ ?_
    · simp only [Iso.refl_hom, Category.id_comp]
      change H.map (biprod.lift _ _) = biprod.lift _ _ ≫ p.inv
      have hu : H.map (ordinaryAlphaComplex l E b o aU jU jW wU (I M)) =
          (ordinaryAlpha l E b o aU jU jW wU).app ((I M).X n) := rfl
      have hv : H.map (ordinaryAlphaComplex l E b o aV jV jW wV (I M)) =
          (ordinaryAlpha l E b o aV jV jW wV).app ((I M).X n) := rfl
      simpa only [Functor.map_neg, hu, hv] using
        (biprod.lift_mapBiprod H _ _
          (ordinaryAlphaComplex l E b o aU jU jW wU (I M))
          (-ordinaryAlphaComplex l E b o aV jV jW wV (I M))).symm
    · simp only [Iso.refl_hom, Category.comp_id]
      change p.inv ≫ H.map (biprod.desc _ _) = biprod.desc _ _
      exact biprod.mapBiprod_inv_map_desc H _ _ _ _
  let pU M := (o.openOp jU).ordinaryAdjunction.derivedPresentation
    (o.openOp jU).derivedAdjunction (I M) (e M)
  let pV M := (o.openOp jV).ordinaryAdjunction.derivedPresentation
    (o.openOp jV).derivedAdjunction (I M) (e M)
  let pW M := (o.openOp jW).ordinaryAdjunction.derivedPresentation
    (o.openOp jW).derivedAdjunction (I M) (e M)
  have (A B : CochainComplex (SpTowerShriek.S l E X) ℤ) :
      PreservesBinaryBiproduct A B DerivedCategory.Q :=
    preservesBinaryBiproduct_of_preservesBiproduct DerivedCategory.Q A B
  let qb M := DerivedCategory.Q.mapBiprod
    (((o.openOp jU).extension.mapHomologicalComplex (.up ℤ)).obj
      (((o.geometry jU).pull.mapHomologicalComplex (.up ℤ)).obj (I M)))
    (((o.openOp jV).extension.mapHomologicalComplex (.up ℤ)).obj
      (((o.geometry jV).pull.mapHomologicalComplex (.up ℤ)).obj (I M)))
  let q M := biprod.mapIso (pU M) (pV M) ≪≫ (qb M).symm
  have hm {A : Scheme.{u}} (a : W ⟶ A) (j : A ⟶ X)
      [IsOpenImmersion a] [IsOpenImmersion j] (w : a ≫ j = jW) (M) :
      (pW M).hom ≫ DerivedCategory.Q.map (ordinaryAlphaComplex l E b o a j jW w (I M)) =
        alpha l E b o a j jW w M ≫
          ((o.openOp j).ordinaryAdjunction.derivedPresentation
            (o.openOp j).derivedAdjunction (I M) (e M)).hom := by
    have hc : (Functor.mapDerivedCategoryCompIso (o.geometry j).pull
          (o.geometry a).pull).symm ≪≫
        Functor.mapDerivedCategoryNatIso (o.ordinaryComp a j ≪≫
          eqToIso (congrArg (fun h ↦ (o.geometry h).pull) w)) =
        o.comp a j ≪≫ eqToIso (congrArg
          (fun h ↦ SpTowerShriek.pull l E b (o.geometry h)) w) := by
      cases w
      simpa only [eqToIso_refl, Iso.trans_refl] using (o.comp_termwise a j).symm
    have h := Adjunction.derivedPresentation_mate
      (o.openOp j).ordinaryAdjunction (o.openOp jW).ordinaryAdjunction
      (o.ordinaryComp a j ≪≫ eqToIso (congrArg (fun h ↦ (o.geometry h).pull) w))
      (o.openOp j).derivedAdjunction (o.openOp jW).derivedAdjunction (I M) (e M)
      (ordinaryAlphaComplex l E b o a j jW w (I M))
      (by intro n; simp [ordinaryAlphaComplex, ordinaryAlpha])
    dsimp only at h
    rw [hc] at h
    exact h
  refine ⟨T, ht, pW, q, fun M ↦ (e M).symm, ?_, ?_, ?_⟩
  · intro M
    apply (cancel_mono (q M).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply (cancel_mono (qb M).hom).1
    dsimp only [q, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    · simpa [T, ordinaryComplexSequence, first, qb, Category.assoc,
        Functor.mapBiprod_hom, ← Functor.map_comp] using (hm aU jU wU M).symm
    · simpa [T, ordinaryComplexSequence, first, qb, Category.assoc,
        Functor.mapBiprod_hom, ← Functor.map_comp] using
        congrArg Neg.neg (hm aV jV wV M).symm
  · intro M
    simp only [Iso.symm_inv]
    dsimp only [q, Iso.trans_hom, Iso.symm_hom]
    apply biprod.hom_ext'
    · simpa [T, ordinaryComplexSequence, second, qb, pU,
        Category.assoc, Functor.mapBiprod_inv, ← Functor.map_comp_assoc] using
        ((o.openOp jU).ordinaryAdjunction.derivedPresentation_counit
          (o.openOp jU).derivedAdjunction (I M) (e M)).symm
    · simpa [T, ordinaryComplexSequence, second, qb, pV,
        Category.assoc, Functor.mapBiprod_inv, ← Functor.map_comp_assoc] using
        ((o.openOp jV).ordinaryAdjunction.derivedPresentation_counit
          (o.openOp jV).derivedAdjunction (I M) (e M)).symm
  · intro M N h
    let : (I N).IsKInjective := hI N
    obtain ⟨f, hf⟩ := CochainComplex.IsKInjective.exists_Q_map_eq (I M) (I N)
      ((e M).hom ≫ h ≫ (e N).inv)
    have he : h ≫ (e N).inv = (e M).inv ≫ DerivedCategory.Q.map f := by
      rw [hf]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    let g := ordinaryComplexSequenceMap l E b o aU aV jU jV jW wU wV f
    refine ⟨g, ?_, ?_, he⟩
    · exact presentation_naturality (o.openOp jW).ordinaryAdjunction
        (o.openOp jW).derivedAdjunction (e M) (e N) h f he
    · have hu := presentation_naturality (o.openOp jU).ordinaryAdjunction
        (o.openOp jU).derivedAdjunction (e M) (e N) h f he
      have hv := presentation_naturality (o.openOp jV).ordinaryAdjunction
        (o.openOp jV).derivedAdjunction (e M) (e N) h f he
      let fu := ((o.openOp jU).extension.mapHomologicalComplex (.up ℤ)).map
        (((o.geometry jU).pull.mapHomologicalComplex (.up ℤ)).map f)
      let fv := ((o.openOp jV).extension.mapHomologicalComplex (.up ℤ)).map
        (((o.geometry jV).pull.mapHomologicalComplex (.up ℤ)).map f)
      have hg : DerivedCategory.Q.map g.τ₂ ≫ (qb N).hom =
          (qb M).hom ≫ biprod.map (DerivedCategory.Q.map fu)
            (DerivedCategory.Q.map fv) := by
        apply biprod.hom_ext <;>
          simp [g, ordinaryComplexSequenceMap, fu, fv, qb, Category.assoc,
            ← Functor.map_comp]
      apply (cancel_mono (qb N).hom).1
      dsimp only [q, Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hg]
      simp only [Iso.inv_hom_id_assoc]
      apply biprod.hom_ext
      · simpa [fu, pU, support, Category.assoc] using
          congrArg (fun k ↦ (biprod.fst :
            _ ⊞ (support l E b o jV).obj M ⟶ _) ≫ k) hu
      · simpa [fv, pV, support, Category.assoc] using
          congrArg (fun k ↦ (biprod.snd :
            (support l E b o jU).obj M ⊞ _ ⟶ _) ≫ k) hv

end AlgebraicGeometry.ProEtale.TowerOpenCover
