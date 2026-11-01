/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitInsertion
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitComposition
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! Unit and successive-quotient normalization for finite dualizing coefficients. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped CategoryTheory.Functor
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem compact_coefficient_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    {T Y : Scheme.{u}} {f : T ⟶ Y}
    (c : Compactification f) (K : Etale.DerivedCategoryModule A T) :
    (Etale.scalarExtension ψ Y).map (Etale.ExceptionalCoefficients.compactSupportMap φ c K) ≫
      Etale.ExceptionalCoefficients.compactSupportMap ψ c
        ((Etale.scalarExtension φ T).obj K) ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
        ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ
          χ hχ).hom.app K) =
    (ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology φ ψ
      χ hχ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
      Etale.ExceptionalCoefficients.compactSupportMap χ c K := by
  subst χ
  have ho := (Etale.etaleOpenScalarComparisons φ c.i).successive_scalar ψ K
  rw [← Etale.compactScalarOpen_eq, ← Etale.compactScalarOpen_eq,
    ← Etale.compactScalarOpen_eq] at ho
  have hp := Etale.finiteCoefficientDirectImageMap_coefficientChain φ ψ c.g
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K)
  rw [Etale.finiteCoefficientDirectImage_scalarMate,
    Etale.finiteCoefficientDirectImage_scalarMate,
    Etale.finiteCoefficientDirectImage_scalarMate] at hp
  have hn := (Etale.scalarMate ψ c.g).naturality
    ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K)
  dsimp only [Functor.comp_map] at hn
  dsimp only [Etale.ExceptionalCoefficients.compactSupportMap,
    Etale.rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp]
  rw [ho]
  rw [hp]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem restriction_unit_id
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u})
    (φ : A →+* A) (hφ : φ = RingHom.id A) :
    Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ) =
      (ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology φ hφ).inv.app
        (𝟙_ _) := by
  subst φ
  apply Sheaf.hom_ext_of_ε_comp
  rw [Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose]
  have hη : Functor.LaxMonoidal.ε ((Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
      (ModuleCat.restrictScalars.{u + 1} (RingHom.id A))) = 𝟙 _ := by
    ext U : 2
    apply ModuleCat.hom_ext
    ext
    erw [ModuleCat.restrictScalars_η]
    rfl
  rw [hη, Category.id_comp]
  ext U : 2
  apply ModuleCat.hom_ext
  ext
  rfl

private theorem unit_identity_transport
    {C : Type*} [Category C] (F : C ⥤ C) (α : F ≅ 𝟭 C)
    {A B : C} (i : A ≅ B) (a : F.obj B ⟶ B)
    (h : F.map i.hom ≫ a ≫ i.inv = α.hom.app A) :
    a = α.hom.app B := by
  have hn := α.hom.naturality i.hom
  dsimp only [Functor.id_map] at hn
  apply (cancel_epi (F.map i.hom)).1
  apply (cancel_mono i.inv).1
  calc
    (F.map i.hom ≫ a) ≫ i.inv = α.hom.app A := by
      simpa only [Category.assoc] using h
    _ = (F.map i.hom ≫ α.hom.app B) ≫ i.inv := by
      rw [hn, Category.assoc, i.hom_inv_id]
      exact (Category.comp_id _).symm

private theorem adjoint_identity_unit
    {C : Type*} [Category C] {F R : C ⥤ C} (ad : F ⊣ R)
    (e : R ≅ 𝟭 C) (M : C) :
    (ad.homEquiv _ _).symm (e.inv.app M) =
      (Adjunction.leftAdjointIdIso ad e).hom.app M := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have h := unit_conjugateEquiv (Adjunction.id) ad
    (Adjunction.leftAdjointIdIso ad e).hom M
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  change 𝟙 _ ≫ e.inv.app M = ad.unit.app M ≫ R.map _ at h
  erw [Category.id_comp] at h
  exact h

private theorem insertion_identity
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (R : C ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory C}
    (a : L ⊣ R.mapDerivedCategory) (e : R ≅ 𝟭 C) (M : C)
    (f : M ⟶ R.obj M) (hf : f = e.inv.app M) :
    SheafExactDegreeZero.adjointInsertion R a f =
      (Adjunction.leftAdjointIdIso a
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C)).hom.app
          ((_root_.DerivedCategory.singleFunctor C 0).obj M) := by
  have h := SheafExactDegreeZero.raw_unit_id R e M f hf
  unfold SheafExactDegreeZero.adjointInsertion
  rw [h]
  exact adjoint_identity_unit _ _ _

private theorem scalar_unit_id
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u})
    (φ : A →+* A) (hφ : φ = RingHom.id A) :
    (Etale.ExceptionalCoefficients.unitIso φ T).hom =
      (ProEtale.normalizedOriginScalarUnit T.smallEtaleTopology φ hφ).hom.app
        (Etale.constantComplex A T) := by
  apply unit_identity_transport (Etale.scalarExtension φ T)
    (ProEtale.normalizedOriginScalarUnit T.smallEtaleTopology φ hφ)
    (_root_.DerivedCategory.singleFunctorObjUnitIso
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
  rw [Etale.scalarUnit_eq_adjointInsertion]
  let R := Sheaf.restrictScalars T.smallEtaleTopology φ
  let e := ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology φ hφ
  exact insertion_identity R
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    e (𝟙_ _) (Functor.LaxMonoidal.ε R) (restriction_unit_id T φ hφ)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The regular scalar unit and the two successive-quotient equations for finite
 dualizing coefficients.  The scalar unit is identified with the normalized
origin unit at the base.  The two remaining equations are the mate-pasting
identities for compact support and for the regular coefficient unit.  Expanding
the proper/open factorization, applying the coefficient comparison cocycle,
and cancelling the invertible scalar mates proves all three equations.  The
argument is valid for equal levels and for arbitrary (possibly non-flat)
quotient maps.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md`, paragraphs 1--3 and
final sentence.
(blueprint: lem-coef-dualizing-quotient-normalization)
-/
theorem finiteDualizing_quotient_normalization :
    (∀ n : ℕ, (Etale.ExceptionalCoefficients.unitIso
        (finiteDualizingQuotient l E (le_refl n)) (Spec (.of D.k))).hom =
      (ProEtale.normalizedOriginScalarUnit (Spec (.of D.k)).smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
      (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E r) X),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) (Spec (.of D.k))).map
          (Etale.ExceptionalCoefficients.compactSupportMap
            (finiteDualizingQuotient l E hrm) (finiteDualizingCompactification D X) K) ≫
        Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E hmn)
          (finiteDualizingCompactification D X)
          ((Etale.scalarExtension (finiteDualizingQuotient l E hrm) X).obj K) ≫
        (finiteDualizingEtaleSupport l E D X n).map
          ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
            (finiteDualizingQuotient_comp l E hrm hmn)).hom.app K) =
      (ProEtale.pbcFixedScalarExtensionComp (Spec (.of D.k)).smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
          ((finiteDualizingEtaleSupport l E D X r).obj K) ≫
        Etale.ExceptionalCoefficients.compactSupportMap
          (finiteDualizingQuotient l E (hmn.trans hrm))
          (finiteDualizingCompactification D X) K) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) (Spec (.of D.k))).map
          (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E hrm)
            (Spec (.of D.k))).hom ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E hmn)
          (Spec (.of D.k))).hom =
      (ProEtale.pbcFixedScalarExtensionComp (Spec (.of D.k)).smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
          (Etale.constantComplex (finiteDualizingCoeff l E r) (Spec (.of D.k))) ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E
          (hmn.trans hrm)) (Spec (.of D.k))).hom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact scalar_unit_id _ _ (finiteDualizingQuotient_id l E n)
  · intro r m n hrm hmn K
    exact compact_coefficient_chain _ _ _ (finiteDualizingQuotient_comp l E hrm hmn)
      (finiteDualizingCompactification D X) K
  · intro r m n hrm hmn
    exact Etale.normalizedScalarUnit_comp _ _ _ (finiteDualizingQuotient_comp l E hrm hmn) _

end WeilConjectures
