/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W8
-/
module

public import Sheaf.Paper.SfClopenRestrictionData
import all Sheaf.AlgebraicGeometry.ProEtaleClopenScalarComparisonDescent
import Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatDetection
import all Sheaf.Algebra.Homology.RingIsomorphismTensorTransport

/-! # Descent of an ordinary scalar comparison

Source: Stacks Project, sites-cohomology.tex, Tag 06YY, Lemma pullback-K-flat;
derived.tex, Tag 06XN.
(blueprint: lem-sf-clopen-scalar-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.sheafify
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.locallyBijective

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures


private theorem sfClopenRestrictionKFlat
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U)
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U.toScheme)
      ((sfClopenComplexRestriction d).obj P) := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  let W : T.Opens := ⟨(U : Set T)ᶜ, hU.isOpen_compl⟩
  let pieces : Bool → T.Opens := fun b ↦ if b then W else U
  let j (b : Bool) := (pieces b).ι
  have (b : Bool) : IsOpenImmersion (j b) := by dsimp [j]; infer_instance
  have (b : Bool) : IsClosedImmersion (j b) := by
    apply IsClosedImmersion.of_isPreimmersion
    cases b
    · simpa only [j, pieces, Bool.false_eq_true, ↓reduceIte, Opens.range_ι] using hU
    · change IsClosed (Set.range W.ι)
      simpa only [Opens.range_ι] using
        (show IsClosed (W : Set T) from U.isOpen.isClosed_compl)
  have hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))) := by
    intro i k h
    cases i <;> cases k
    · exact (h rfl).elim
    · simpa [j, pieces, Opens.range_ι, W] using
        (disjoint_compl_right : Disjoint (U : Set T) (U : Set T)ᶜ)
    · simpa [j, pieces, Opens.range_ι, W] using
        (disjoint_compl_left : Disjoint (U : Set T)ᶜ (U : Set T))
    · exact (h rfl).elim
  have hc : ∀ x : T, ∃ i, x ∈ Set.range (j i) := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨false, by simpa [j, pieces, Opens.range_ι] using hx⟩
    · exact ⟨true, by simpa [j, pieces, Opens.range_ι, W] using hx⟩
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let R' := AlgebraicGeometry.Scheme.ProEt.ClopenData.clopenTensorRings.{t, u} U.ι |>.obj R
  let c : completedIntegralCommRingSheafUnrestricted l E U.toScheme ≅ R' :=
    (sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimageIso
        d.completion
  let Q := (AlgebraicGeometry.Scheme.ProEt.ClopenData.clopenTensorComplexRestriction.{t, u}
    U.ι R).obj P
  have hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R') Q :=
    ((ProEt.clopen_kflat_detection T Bool (fun b ↦ (pieces b).toScheme) j hd hc R P).mp hP)
      false
  obtain ⟨b, _⟩ := SheafOfModules.scalarRestriction_braided c
  let := b
  have ht := (SheafOfModules.scalarRestriction_kflat c Q).mpr hQ
  have hc : (sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c.hom =
      d.completion.hom := by
    apply Functor.map_preimage
  change CochainComplex.IsKFlatIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E U.toScheme)
    (((SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat RingCat)).map c.hom)).mapHomologicalComplex (.up ℤ)).obj Q) at ht
  rw [hc] at ht
  exact ht

private def sfClopenCounitNat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (n : ℕ) :
    letI := scalarReductionExtensionAdditive l E T n
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension l E T n ⟶
      (scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  letI := scalarReductionExtensionAdditive l E T n
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (scalarReductionDerivedExtension l E T n) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _) (scalarReductionCounit l E T n) ≫
    Functor.whiskerRight ((scalarReductionExtension l E T n).mapHomotopyCategoryFactors
      (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft ((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

private theorem sfClopenCounitNat_app
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (sfClopenCounitNat l E T n).app P = sfClopenReductionCounit T n P := rfl

private theorem sfClopenCounitNat_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P) :
    IsIso ((sfClopenCounitNat l E T n).app P) := by
  have := unrestrictedTowerCounit_isIso l E T n P hP
  dsimp only [sfClopenCounitNat, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

attribute [local irreducible] sfClopenCounitNat
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

/-- An ordinary natural scalar comparison descends through K-flat localization,
with its universal counit square on every complex.

Source: Stacks Project, sites-cohomology.tex, Lemma derived-base-change (Tag 06YY),
Lemma pullback-K-flat; derived.tex, Tag 06XN.
(blueprint: lem-sf-clopen-scalar-comparison-descent).

Proof: restriction to the clopen component is projection under the finite-clopen
module equivalence. Its termwise application preserves K-flat complexes with flat
terms, since acyclicity and tensor products are componentwise. For such a complex,
the two universal scalar-extension counits compute the two derived functors.
Conjugating the ordinary comparison by these counits and the exact-restriction
localization comparisons gives an isomorphism, natural on K-flat representatives.
The K-flat localization equivalence descends it and its inverse to a natural
isomorphism of the derived functors. For an arbitrary complex P, choose a K-flat
resolution Q to P. The counit square commutes at Q by construction. Naturality of
the ordinary comparison, both universal counits and the localization comparisons
transports the square along Q to P; the resolution is inverted in the source
derived category, so cancel its image. This proves the equation at P, without
assuming P K-flat. The only comparison assumed here is between ordinary module
functors; finite or completed quotient chain isomorphisms are not assumed. -/
theorem sf_clopen_scalar_comparison_descent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) (n : ℕ)
    (c : scalarReductionExtension l E T n ⋙
        sfClopenModuleRestriction U _ _ (d.finite n) ≅
      sfClopenModuleRestriction U (completedIntegralCoefficientSheafUnrestricted l E T)
        (completedIntegralCoefficientSheafUnrestricted l E U.toScheme) d.completion ⋙
        scalarReductionExtension l E U.toScheme n) :
    letI := scalarReductionExtensionAdditive l E T n
    letI := scalarReductionExtensionAdditive l E U.toScheme n
    letI := d.additive
    letI := d.finite_additive n
    ∃ reduction : scalarReductionDerivedExtension l E T n ⋙
        sfClopenFiniteDerivedRestriction d n ≅
      sfClopenDerivedRestriction d ⋙ scalarReductionDerivedExtension l E U.toScheme n,
      ∀ P : CochainComplex (scalarReductionSource l E T) ℤ,
      (sfClopenFiniteDerivedRestriction d n).map (sfClopenReductionCounit T n P) ≫
          (sfClopenFiniteLocalizationIso d n
            (unrestrictedTowerFiniteComplex l E T n P)).hom ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).app P).hom =
        reduction.hom.app (DerivedCategory.Q.obj P) ≫
          (scalarReductionDerivedExtension l E U.toScheme n).map
            (sfClopenLocalizationIso d P).hom ≫
          sfClopenReductionCounit U.toScheme n ((sfClopenComplexRestriction d).obj P) := by
  classical
  let := scalarReductionExtensionAdditive l E T n
  let := scalarReductionExtensionAdditive l E U.toScheme n
  let := d.additive
  let := d.finite_additive n
  let := d.limits
  let := d.colimits
  let := d.finite_limits n
  let := d.finite_colimits n
  let L := sfClopenModuleRestriction U _ _ d.completion
  let N := sfClopenModuleRestriction U _ _ (d.finite n)
  let A := scalarReductionDerivedExtension l E T n
  let B := scalarReductionDerivedExtension l E U.toScheme n
  let EC := (scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)
  let LC := L.mapHomologicalComplex (.up ℤ)
  let FC := (scalarReductionExtension l E U.toScheme n).mapHomologicalComplex (.up ℤ)
  let good (P : CochainComplex (scalarReductionSource l E T) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P
  have hres : ∀ K, ∃ (P : CochainComplex (scalarReductionSource l E T) ℤ) (f : P ⟶ K),
      good P ∧ QuasiIso f := by
    intro K
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E T) K
    exact ⟨P, f, hP, hf⟩
  obtain ⟨e, he, _⟩ := ProEt.ClopenScalar.descendComparison L N
    (scalarReductionExtension l E T n) (scalarReductionExtension l E U.toScheme n)
    A B (sfClopenCounitNat l E T n) (sfClopenCounitNat l E U.toScheme n)
    good hres (sfClopenCounitNat_isIso l E T n)
    (fun P hP ↦ sfClopenCounitNat_isIso l E U.toScheme n _
      (sfClopenRestrictionKFlat hU d P hP)) c
  refine ⟨e, ?_⟩
  intro P
  let H := LC ⋙ FC ⋙ (DerivedCategory.Q : CochainComplex (scalarReductionTarget l E
    U.toScheme n) ℤ ⥤ _)
  let a : DerivedCategory.Q ⋙ (A ⋙ N.mapDerivedCategory) ⟶ H :=
    Functor.whiskerRight (sfClopenCounitNat l E T n) N.mapDerivedCategory ≫
      Functor.whiskerLeft EC N.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ (A ⋙ N.mapDerivedCategory) ⟶ H :=
    Functor.whiskerLeft DerivedCategory.Q e.hom ≫
      Functor.whiskerRight L.mapDerivedCategoryFactors.hom B ≫
      Functor.whiskerLeft LC (sfClopenCounitNat l E U.toScheme n)
  suffices h : a.app P = b.app P by
    simpa only [a, b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, sfClopenCounitNat_app,
      sfClopenFiniteDerivedRestriction, sfClopenDerivedRestriction,
      sfClopenFiniteLocalizationIso, sfClopenLocalizationIso,
      sfClopenComplexRestriction, Iso.app_hom, Iso.app_inv,
      L, N, A, B, EC, LC, FC, H, unrestrictedTowerFiniteComplex,
      Functor.comp_obj, Category.assoc] using h
  obtain ⟨K, f, hK, hf⟩ := hres P
  let : QuasiIso f := hf
  have : IsIso ((DerivedCategory.Q ⋙ (A ⋙ N.mapDerivedCategory)).map f) := by
    dsimp only [Functor.comp_map]
    infer_instance
  apply (cancel_epi ((DerivedCategory.Q ⋙ (A ⋙ N.mapDerivedCategory)).map f)).mp
  calc
    _ = a.app K ≫ H.map f := a.naturality f
    _ = b.app K ≫ H.map f := congrArg (fun z ↦ z ≫ H.map f) (he K hK).symm
    _ = _ := (b.naturality f).symm

end WeilConjectures
