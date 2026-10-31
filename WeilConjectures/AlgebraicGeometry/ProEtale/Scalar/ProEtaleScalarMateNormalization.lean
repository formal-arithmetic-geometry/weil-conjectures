/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarTensorNormalization

/-! # Pro-etale scalar mate normalization

Source: Stacks Project, Tag 0B56, equation-projection-formula-map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Restriction of the specified scalar mate is precisely the counit-defined projection.
Source: Stacks 0B56, equation-projection-formula-map
(blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: (1) scalarMateDerivedTensorIso gives the natural h identifications from step 1,
normalized on balanced tensors. (2) Apply the ring-sheaf change adjunction to the
constant coefficient square, which commutes by naturality of constant sections.
Its canonical d compares the direct images without asserting that restriction
preserves K-injectives. (3) Resolve N and B by flat-term K-flat complexes. Both
pullback/tensor routes send x tensor b to the same pullbacks, by the ordinary
pure-tensor normalizations. They preserve bidegrees and signed total differentials.
The resolution-of-B maps are quasi-isomorphisms after tensoring with the K-flat
first factors, so cancel them after localization. Resolving-class descent gives
the square for every N, including nonflat B. (4) Take N=Ru_* M and transpose the
restricted scalar mate using the ring-sheaf change adjunction. The square of step 3
and naturality of h identify its transpose with the pullback tensor comparison
followed by epsilon_M tensor identity and the coefficient identification v.
This is exactly the specified projection arrow, so adjunction injectivity gives
the first equality. (5) The mate-counit formula gives the second equality before
restriction. All constructions are natural in M; complexes and resolutions are
unbounded and neither flatness nor boundedness was used. -/
theorem proEtaleScalarMateNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V)
    (aV : Scheme.ProEtaleTensorModel V (Scheme.proEtaleConstantRing V A))
    (aT : Scheme.ProEtaleTensorModel T (Scheme.proEtaleConstantRing T A))
    (M : Scheme.proEtaleDerivedCategory T A) :
    ((scalarMateDerivedTensorIso φ V aV).inv.app ((directImageConstantPush A f).obj M) ≫
      (scalarMateRestriction φ V).mapDerivedCategory.map
        ((directImageScalarComparison φ f).app M) ≫
      (scalarMateRestrictionPush φ f).hom.app ((directImageScalarExtension φ T).obj M) ≫
      (directImageConstantPush A f).map ((scalarMateDerivedTensorIso φ T aT).hom.app M) =
    CategoryTheory.derivedProjectionFormulaMate
      (Scheme.proEtaleConstantRingDerivedPullback A f) (directImageConstantPush A f)
      (directImageConstantAdjunction A f) aV.tensor aT.tensor
      (Scheme.proEtaleCanonicalTensorComparison f
        (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
        (Scheme.proEtaleConstantRingComparison f A) aV aT)
      M (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ V)) ≫
      (directImageConstantPush A f).map
        (aT.tensor.map (Prod.mkHom (𝟙 M) (scalarMateDerivedCoefficientPullback φ f).hom))) ∧
    ((Scheme.proEtaleConstantRingDerivedPullback B f).map
      ((directImageScalarComparison φ f).app M) ≫
        (directImageConstantAdjunction B f).counit.app
          ((directImageScalarExtension φ T).obj M) =
      (directImageScalarPullbackIso φ f).hom.app ((directImageConstantPush A f).obj M) ≫
        (directImageScalarExtension φ T).map
          ((directImageConstantAdjunction A f).counit.app M)) := by
  refine ⟨?_, ?_⟩
  · let LA := Scheme.proEtaleConstantRingDerivedPullback A f
    let GA := directImageConstantPush A f
    let SA := directImageScalarExtension φ V
    let ST := directImageScalarExtension φ T
    let UV := (scalarMateRestriction φ V).mapDerivedCategory
    let UT := (scalarMateRestriction φ T).mapDerivedCategory
    let adjA := directImageConstantAdjunction A f
    let adjB := directImageConstantAdjunction B f
    let n := GA.obj M
    let t := (directImageScalarPullbackIso φ f).hom.app n ≫ ST.map (adjA.counit.app M)
    have ht : adjB.homEquiv _ _ t = (directImageScalarComparison φ f).app M := by
      apply (adjB.homEquiv _ _).symm.injective
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact (mateEquiv_counit adjA adjB (directImageScalarPullbackIso φ f).hom M).symm
    have hc := (Scheme.proEtaleRingSheafChangeAdjunction f
      (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
      (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
      (Scheme.proEtaleConstantRingMap (T := V) φ)
      (Scheme.proEtaleConstantRingMap (T := T) φ)
      (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
      (Scheme.proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift φ))).symm).2.2 (SA.obj n) (ST.obj M) t
    change adjA.homEquiv _ _ (_ ≫ UT.map t) =
      UV.map (adjB.homEquiv _ _ t) ≫ (scalarMateRestrictionPush φ f).hom.app (ST.obj M) at hc
    rw [ht] at hc
    have hn := (proEtaleScalarTensorNormalization φ f aV aT).1 n
    have hnat := (scalarMateDerivedTensorIso φ T aT).hom.naturality (adjA.counit.app M)
    change UT.map (ST.map (adjA.counit.app M)) ≫
      (scalarMateDerivedTensorIso φ T aT).hom.app M =
      (scalarMateDerivedTensorIso φ T aT).hom.app (LA.obj n) ≫
        aT.tensor.map (Prod.mkHom (adjA.counit.app M)
          (𝟙 (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ T)))) at hnat
    rw [← Category.assoc (UV.map _) _ (GA.map _), ← hc]
    rw [← adjA.homEquiv_naturality_right]
    erw [← adjA.homEquiv_naturality_left]
    apply (adjA.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, adjA.homEquiv_naturality_right_symm]
    have hp : (adjA.homEquiv _ _).symm
        (CategoryTheory.derivedProjectionFormulaMate LA GA adjA aV.tensor aT.tensor
          (Scheme.proEtaleCanonicalTensorComparison f
            (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
            (Scheme.proEtaleConstantRingComparison f A) aV aT) M
          (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ V))) =
        (Scheme.proEtaleCanonicalTensorComparison f
          (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
          (Scheme.proEtaleConstantRingComparison f A) aV aT).hom.app
            (n, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ V)) ≫
        aT.tensor.map (Prod.mkHom (adjA.counit.app M)
          (𝟙 (LA.obj (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ V))))) := by
      simpa [derivedProjectionFormulaMate, n, LA, GA] using
        adjA.homEquiv_symm_rightAdjointProjectionMap_app_app
          (T_C := Functor.curry.obj aT.tensor) (T_D := Functor.curry.obj aV.tensor)
          (Functor.curry.map (Scheme.proEtaleCanonicalTensorComparison f
            (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
            (Scheme.proEtaleConstantRingComparison f A) aV aT).hom ≫
            (Functor.curryObjProdComp LA LA aT.tensor).hom) M
          (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ V))
    erw [hp]
    dsimp only [t]
    rw [UT.map_comp]
    simp only [Category.assoc]
    rw [hnat]
    simp only [← Category.assoc] at hn ⊢
    erw [hn]
    simp only [Category.assoc, ← aT.tensor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id]
    congr 2
    apply Prod.hom_ext
    · exact (Category.comp_id _).symm
    · exact (Category.id_comp _).symm
  · exact mateEquiv_counit (directImageConstantAdjunction A f)
      (directImageConstantAdjunction B f) (directImageScalarPullbackIso φ f).hom M

end AlgebraicGeometry.ProEtale
