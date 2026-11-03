/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralQcqsReductionConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import all WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedSectionSquares
import WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CofinalCoefficientProjectionCocone
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Constructible cohomology of the evaluated strict reductions

Source: blueprint latest, normalized-towers-reduction, constructibility paragraph;
Stacks Tags 093M, 093U, 06YY, 08J5.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

-- Fix the site universe before imported max-universe coefficient instances are tried.
private local instance (priority := 10000) fixedSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private noncomputable local instance (priority := 10000) fixedRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} X

private noncomputable local instance (priority := 10000) fixedAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} X

private local instance (priority := 10000) fixedLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

private noncomputable local instance (priority := 10000) fixedModuleAbelian
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    Abelian (ringedSiteModules.{u + 1} R) := SheafOfModules.instAbelian R

private local instance positiveUniformizerFinite (j : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (j + 1)) :=
  Padic.finite_coefficientExtensionRing l E (j + 1) (by omega)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem normalized_uniformizer_constructible
    [CompactSpace T] [QuasiSeparatedSpace T]
    (A : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hA : Mon.mk (DerivedNakayama.integerRing l E) = A) [IsCommMonObj A.X]
    (c : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (condensedRingObj A.X T) ≅
        WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
    (hc : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map c.hom =
      eqToHom (congrArg (fun B ↦ (coefficientRing T B).X)
        (hA.symm.trans (integralPointMon_eq l E))) ≫
        (integralLimitAbComparison l E T).hom)
    (N : DerivedCategory (ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (condensedRingObj A.X T)))))
    (hN :
      letI := Functor.additive_of_preserves_binary_products
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (condensedRingObj A.X T)).inverse
      constantModelBoundedConstructible A.X T
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (condensedRingObj A.X T)).inverse.mapDerivedCategory.obj N)) :
    ∀ j i, Scheme.IsConstructibleProEtaleModuleSheaf T
      (Padic.coefficientExtensionRing l E (j + 1))
      ((DerivedCategory.homologyFunctor _ i).obj
        ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).obj
          ((restrictScalars.{u + 1} ((sheafCompose _
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).mapDerivedCategory.obj
              N))) := by
  classical
  cases hA
  have he : c = integralSectionRingIso l E T := by
    apply (integralSectionRingIso_existsUnique l E T).unique
    · simpa only [eqToHom_refl, Category.comp_id] using hc
    · exact (integralSectionRingIso_existsUnique l E T).exists.choose_spec
  subst c
  let B := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (AdicCompletion.ring l E T)
  let : B.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : B.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let r := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (integralSectionRingIso l E T)
  let G := restrictScalars.{u + 1} r.inv
  let : G.IsEquivalence := restriction_isEquivalence r.symm
  let K := B.inverse.mapDerivedCategory.obj N
  have hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T K := hN
  have z : (integralSectionDerivedEquivalence l E T).functor.obj K ≅
      G.mapDerivedCategory.obj N :=
    (Functor.mapDerivedCategoryCompIso B.functor G).app K ≪≫
      G.mapDerivedCategory.mapIso (B.mapDerivedCategory.counitIso.app N)
  let C := integralEncoding l E T
  obtain ⟨e, a, ha⟩ := IntegralPresentation.fixed_integral_section_squares l E T C
    (integralLimitAbComparison l E T)
    (integralLimitAbComparison_existsUnique l E T).exists.choose_spec
    (integralSectionAbIdentifications l E T).1
    (integralSectionAbIdentifications l E T).2
    (integralSectionRingIso_existsUnique l E T).exists.choose_spec
  intro j i
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let R := Padic.coefficientExtensionRing l E (j + 1)
  let : Finite R := Padic.finite_coefficientExtensionRing l E (j + 1) (by omega)
  let : DiscreteTopology R := FiniteModelQuotient.finiteTopology_discrete l E j
  let enc : ∀ Y : Scheme.{u}, FiniteDiscreteOrdinary.Encoding R Y :=
    Function.update (fun Y ↦ (FiniteDiscreteOrdinary.encoding_exists R Y).some) T (e j)
  have hc' := qcqs_finite_sheaf_criterion R enc T
  simp only [enc, Function.update_self] at hc'
  have hred := integralReduction_qcqs_constantModelBoundedConstructible l E T K hK j
  have hout := (FiniteDiscreteOrdinary.derived_boundedConstructible R T (e j) hc' _).mp hred
  let b := (IntegralPresentation.finiteComparison_existsUnique l E T C j (e j) (a j)).exists.choose
  let q := (b.app K).symm ≪≫
    (WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).mapIso z
  exact Scheme.constructibleProEtale_of_iso T R
    ((DerivedCategory.homologyFunctor _ i).mapIso q) (hout.2 i)

private theorem quotient_scalar_constructible
    (I : Ideal (Padic.coefficientExtensionIntegers l E))
    [Finite (Padic.coefficientExtensionIntegers l E ⧸ I)]
    (j : ℕ) (hI : I = Padic.coefficientExtensionIdeal l E (j + 1))
    (q : WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T ⟶
      Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸ I))
    (hq : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q ≫
        (sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
                ((Ideal.Quotient.factor hI.le).comp ULift.ringEquiv.{u, u + 1}.toRingHom)))) =
          limit.π (WeilConjectures.integralCoefficientSheafSystem.{u, u} l E T) (op j))
    (s : SystemScalarModel.{u + 1, u, u + 1} q)
    (N : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hN : ∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
      (Padic.coefficientExtensionRing l E (j + 1))
      ((DerivedCategory.homologyFunctor _ i).obj
        ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).obj N))) :
    ∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
      (Padic.coefficientExtensionIntegers l E ⧸ I)
      ((DerivedCategory.homologyFunctor _ i).obj (s.model.T.obj N)) := by
  subst I
  have hfactor : (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
      ((Ideal.Quotient.factor (le_refl (Padic.coefficientExtensionIdeal l E (j + 1)))).comp
        ULift.ringEquiv.{u, u + 1}.toRingHom))) =
      𝟙 (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (j + 1)))) := by
    ext x
    simp [Ideal.Quotient.factor_eq]
  rw [hfactor, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at hq
  have hq' : q =
      WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E T j := by
    apply (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
    exact hq
  subst q
  let adj := (WeilConjectures.derivedScalarExtensionRestrictionAdjunction.{u, u} l E T j).choose
  let b := s.adjunction.leftAdjointUniq adj
  intro i
  exact Scheme.constructibleProEtale_of_iso T _
    ((DerivedCategory.homologyFunctor _ i).mapIso (b.app N).symm) (hN i)

private noncomputable def scalar_coefficient_iso
    (D : SpCoefficientTowersAbelian.{u, u} l E T)
    {R S B : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    (c : R ≅ S) (q : S ⟶ B) :
    (D.scalar (c.hom ≫ q)).model.T ≅
      (restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).mapDerivedCategory ⋙
          (D.scalar q).model.T := by
  let f := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let a := restrictionEquivalence (f.mapIso c).symm
  let : a.functor.Additive := by
    change (restrictScalars.{u + 1} (f.map c.inv)).Additive
    infer_instance
  let : a.inverse.Additive := by
    change (restrictScalars.{u + 1} (f.map c.hom)).Additive
    infer_instance
  let e := a.mapDerivedCategory
  let : PreservesFiniteLimits (restrictScalars.{u + 1} (f.map c.hom ≫ f.map q)) := by
    rw [← f.map_comp]
    exact systemScalarRestrictionLimits (c.hom ≫ q)
  let : PreservesFiniteColimits (restrictScalars.{u + 1} (f.map c.hom ≫ f.map q)) := by
    rw [← f.map_comp]
    exact systemScalarRestrictionColimits (c.hom ≫ q)
  let z := (Functor.mapDerivedCategoryCompIso (restrictScalars.{u + 1} (f.map q))
      (restrictScalars.{u + 1} (f.map c.hom))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (IntegralPresentation.restrictComp
      (f.map c.hom) (f.map q)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg restrictScalars.{u + 1} (f.map_comp _ _).symm))
  exact (D.scalar (c.hom ≫ q)).adjunction.leftAdjointUniq
    ((e.toAdjunction.comp (D.scalar q).adjunction).ofNatIsoRight z)

/-- Evaluated reductions of a bounded constructible integral complex have
constructible cohomology. Only constructibility is asserted, without any Tor bound
or normalization condition on a tower.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction,
constructibility paragraph; Stacks Tags 093M, 093U(3), 06YY, 08J5
(blueprint: lem-sp-reduction-tower-level-constructibility).

Proof:
1. The finite-model sheaf quotient theorem computes positive uniformizer reductions
by two-term finite free matrices. Finite-coefficient bounded constructibility is
triangulated on every scheme. Its inverse image under derived reduction and the
exact normalized encoding is triangulated, so bounded truncation devissage gives
constructibility of reductions of every bounded constructible integral complex.
Only qcqs is used to identify the global finite constant-model stratification.
2. The spectral-norm and absolute-value integral coefficient objects are equal.
Uniqueness of the normalized abelian comparison identifies the given coefficient
isomorphism with the canonical section-ring comparison after this equality.
The exact section equivalence counit and normalized finite restriction squares
compare its uniformizer derived reductions, preserving the quotient action.
3. Write ell = v*pi^e with e positive. For level n choose j+1=e*(n+1).
Then (ell^(n+1))=(pi^(j+1)). The cofinal projection cocone identifies the two
completed coefficient projections after the quotient factor map. Eliminating
the equality of ideals makes that factor the identity.
4. Restriction along the coefficient isomorphism is an exact equivalence.
Composition of scalar restrictions and uniqueness of derived left adjoints
compare the specified scalar model with the canonical quotient reduction.
Apply homology to these comparisons and to the supplied evaluation isomorphism;
constructibility is invariant under isomorphism. Zero objects, empty schemes and
the first positive quotient are included throughout.
-/
theorem sp_reduction_tower_level_constructibility
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (coefficient_normalized : ∀ (U : T.ProEtᵒᵖ)
      (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
      coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red)
    [CompactSpace T] [QuasiSeparatedSpace T]
    (M : DerivedCategory (spIntegralSectionModules l E T))
    (hM : constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj M)) :
    ∀ (n : ℕ) (i : ℤ), Scheme.IsConstructibleProEtaleModuleSheaf T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
      ((@DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
        _ _ (HasDerivedCategory.standard _) i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M))) := by
  classical
  have hcmp : spIntegralAbComparison l E T = integralLimitAbComparison l E T := by
    apply (integralLimitAbComparison_existsUnique l E T).unique
    · let H := sfb_integral_coefficient_limit l E T
      let a := H.choose
      let c := H.choose_spec.choose
      let j := H.choose_spec.choose_spec.choose
      have h := H.choose_spec.choose_spec.choose_spec
      have he := h.2.2.2.2.2.choose_spec.1
      exact ⟨he.1, he.2.1, a, c, j, h.1, h.2.1, he.2.2⟩
    · exact (integralLimitAbComparison_existsUnique l E T).exists.choose_spec
  have hcoefficient : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map coefficient.hom =
      eqToHom (congrArg (fun B ↦ (coefficientRing T B).X)
        ((integralPointMon_eq l E).symm.trans (integralPointMon_eq l E))) ≫
        (integralLimitAbComparison l E T).hom := by
    ext U x
    rw [← hcmp]
    exact coefficient_normalized U x
  have hcons := normalized_uniformizer_constructible l E T (sfbCondensedIntegers l E)
    (integralPointMon_eq l E) coefficient hcoefficient M hM
  obtain ⟨e, v, he, hfactor⟩ := (sp_completed_coefficients_regular l E T).1
  obtain ⟨H, hH, _⟩ := sp_cofinal_coefficient_projection_cocone l E T e he v hfactor
  intro n i
  let j := e * (n + 1) - 1
  have hj : j + 1 = e * (n + 1) := by
    have hp : 0 < e * (n + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hI : spEllIdeal l E ^ (n + 1) =
      Padic.coefficientExtensionIdeal l E (j + 1) := by
    change Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1) = _
    rw [hfactor, Ideal.span_singleton_mul_left_unit v.isUnit,
      ← Ideal.span_singleton_pow, ← pow_mul, ← hj]
    rfl
  let q := spIntegralEllProjection l E T n
  have hp : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q =
      (sp_completed_coefficient_limit l E T).choose.hom ≫
        limit.π (spCoefficientRings l E T) (op n) := by
    have he' : (sp_completed_coefficient_limit l E T).exists.choose =
        (sp_completed_coefficient_limit l E T).choose :=
      (sp_completed_coefficient_limit l E T).unique
        (sp_completed_coefficient_limit l E T).exists.choose_spec
        (sp_completed_coefficient_limit l E T).choose_spec.1
    dsimp only [q, spIntegralEllProjection]
    rw [CategoryTheory.Functor.map_preimage, he']
  have hq := (hH n j hj.le).2.2.2.1
  rw [← hp] at hq
  have hout := quotient_scalar_constructible l E T (spEllIdeal l E ^ (n + 1))
    j hI q hq (D.scalar q)
    ((restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        coefficient.inv)).mapDerivedCategory.obj M) (hcons j)
  let z := (evaluation n).app M ≪≫
    (scalar_coefficient_iso l E T D coefficient q).app M
  exact Scheme.constructibleProEtale_of_iso T _
    ((DerivedCategory.homologyFunctor _ i).mapIso z.symm) (hout i)

end AlgebraicGeometry.ProEtale
