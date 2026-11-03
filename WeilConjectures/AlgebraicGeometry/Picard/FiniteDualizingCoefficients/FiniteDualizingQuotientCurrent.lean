/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.AlgebraicGeometry.GeneralFieldFiniteDualizingCoefficientChange
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientUnitInsertion
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.CategoryTheory.Normalized.NormalizedScalarUnitAdjunction
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison

/-! # Finite quotient change for the dualizing object in the current field scope

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.md and its proof; geometric scope per Wei Yang #1441, items 28--29
(blueprint: lem-coef-finite-dualizing).

The maps use the fixed-coefficient derived scalar adjunction and its canonical mates.
Positive natural indices are the actual exponents, including exponent one.
The pro-etale clause specifies transport
through the existing dualizing-object comparison, without an ambient pro-etale adjoint.
The proper factor reuses only the unrestricted counit-normalized direct-image maps,
not the finite direct-image isomorphism theorem. These helpers present the compact
comparison already specified by lem-pur-etale-compact-scalar-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace WeilConjectures

namespace FiniteDualizingCoefficients

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

open AlgebraicGeometry.FiniteCoefficientOrdinary
open scoped CategoryTheory.Functor

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Restriction commutes with site inverse image: conjugate sectionwise commutation of
comparison restriction with coextension, then descend the exact square.
Source: Stacks 03D2 and 06YY (blueprint: lem-coef-finite-dualizing). -/
def siteRestriction (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.{u + 1, u + 1} ⋙
        @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
          inferInstance inferInstance φ ≅
      Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology φ ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.{u + 1, u + 1} :=
  let e : ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T :=
    ((conjugateIsoEquiv
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).comp
        (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ))
      ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).comp
        (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T))).symm (Iso.refl _)).symm
  Functor.mapDerivedCategorySquareIso e

/-- The scalar/site arrow is the mate of the exact restriction square for the fixed
scalar adjunctions. Source: Stacks 07A4 (blueprint: lem-coef-finite-dualizing). -/
def siteMap (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.{u + 1, u + 1} ⋙
        @Sheaf.fixedCoefficientDerivedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
          inferInstance inferInstance φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension.{u} T.smallEtaleTopology φ ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.{u + 1, u + 1} :=
  ((mateEquiv (scalarAdjunction.{u} T.smallEtaleTopology φ)
    (@scalarAdjunction.{u} T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
      inferInstance inferInstance φ)).symm
      (TwoSquare.mk _ _ _ _ (siteRestriction φ T).inv)).natTrans

private theorem counit_dualizingMap [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (dualizingMap φ f) ≫
      (Etale.rightDerivedUpperShriekAdjunction B f).counit.app (𝟙_ _) =
    comparisonInverse φ (HasCompactification.compactification f)
        (Etale.dualizingComplex A f) ≫
      (Sheaf.fixedCoefficientDerivedScalarExtension.{u} Y.smallEtaleTopology φ).map
        ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
      unitMap φ Y := by
  simpa only [dualizingMap, Adjunction.homEquiv_counit] using
    (Etale.rightDerivedUpperShriekAdjunction B f).homEquiv _ _ |>.symm_apply_apply
      (comparisonInverse φ (HasCompactification.compactification f)
          (Etale.dualizingComplex A f) ≫
        (Sheaf.fixedCoefficientDerivedScalarExtension.{u} Y.smallEtaleTopology φ).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
        unitMap φ Y)

private theorem openIso_eq {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    openIso φ j = Etale.ExceptionalCoefficients.openIso φ j := by
  rfl

private theorem siteMap_eq (T : Scheme.{u}) :
    siteMap φ T = (ProEtale.OrdinaryScalarSite.delta φ T).hom := by
  rfl

private theorem scalarId_eq {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (ρ : R →+* R) (hρ : ρ = RingHom.id R) :
    scalarId J ρ hρ = ProEtale.normalizedOriginScalarUnit J ρ hρ := by
  rfl

private theorem unitMap_eq (T : Scheme.{u}) :
    unitMap φ T = (Etale.ExceptionalCoefficients.unitIso φ T).hom := by
  rw [finiteCoefficient_unit_eq_scalarInsertion]
  unfold unitMap SheafExactDegreeZero.scalarAdjointInsertion
    SheafExactDegreeZero.adjointInsertion
  dsimp only
  rw [SheafExactDegreeZero.single_unit_inv, SheafExactDegreeZero.single_unit_hom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  rfl

set_option maxHeartbeats 2000000 in
-- Comparing the chosen derived adjunctions unfolds their normalization data.
private theorem restrictionIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.leftDerivedUpperStarRestrictScalarsIso φ f =
      Etale.scalarRestrictionPullbackIso φ f := by
  have hs : Etale.upperStarRestrictScalarsIsoSheaf φ f =
      Etale.upperStarRestrictScalarsIso φ f := by
    apply Iso.ext
    apply (conjugateEquiv
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
        (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ))
      ((Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).comp
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).injective
    rw [Etale.conjugateEquiv_upperStarRestrictScalarsIso_hom]
    exact Equiv.apply_symm_apply _ _
  unfold Etale.leftDerivedUpperStarRestrictScalarsIso Etale.scalarRestrictionPullbackIso
  rw [hs]

private theorem scalar_mate_counit
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    {S : C₁ ⥤ C₂} {U : C₂ ⥤ C₁} {T : D₁ ⥤ D₂} {V : D₂ ⥤ D₁}
    {F : C₁ ⥤ D₁} {G : D₁ ⥤ C₁} {F' : C₂ ⥤ D₂} {G' : D₂ ⥤ C₂}
    (a : S ⊣ U) (b : T ⊣ V) (d : F ⊣ G) (d' : F' ⊣ G')
    (α : TwoSquare U F' F V) (β : TwoSquare S F F' T)
    (hβ : ∀ K, ((mateEquiv a b).symm α).app K ≫ β.app K = 𝟙 _) (K : D₁) :
    F.map (a.unit.app (G.obj K)) ≫ α.app _ ≫
        V.map (F'.map ((mateEquiv d d' β).app K) ≫ d'.counit.app _) =
      d.counit.app K ≫ b.unit.app K := by
  rw [← Category.assoc, unit_mateEquiv_symm a b α]
  rw [mateEquiv_counit d d' β]
  simp only [Category.assoc, Functor.id_obj]
  rw [← V.map_comp, ← Category.assoc]
  erw [hβ, Category.id_comp]
  exact (b.unit.naturality (d.counit.app K)).symm

private theorem scalarMate_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.DerivedCategoryModule A X) :
    (L(Etale.upperStar (ModuleCat.{u + 1} A) f)).map
        ((scalarAdjunction.{u} Y.smallEtaleTopology φ).unit.app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
      (Etale.leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
        ((Etale.scalarExtension φ Y).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
      (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ).map
        ((L(Etale.upperStar (ModuleCat.{u + 1} B) f)).map ((Etale.scalarMate φ f).app K) ≫
          (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
            ((Etale.scalarExtension φ X).obj K)) =
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
        (scalarAdjunction.{u} X.smallEtaleTopology φ).unit.app K := by
  rw [restrictionIso_eq]
  apply scalar_mate_counit
    (scalarAdjunction.{u} Y.smallEtaleTopology φ)
    (scalarAdjunction.{u} X.smallEtaleTopology φ)
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso φ f).hom)
    (TwoSquare.mk _ _ _ _ (Etale.scalarPullbackIso φ f).hom)
  intro M
  rw [← Etale.scalarPullback_eq φ f]
  have := (ProEtale.scalarPullbackReverse_isIso φ f).2
  exact (asIso (ProEtale.scalarPullbackReverseEtale φ f)).hom_inv_id_app M

private theorem directImage_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    directImageMaps.etale φ f = Etale.scalarMate φ f := by
  let d : DirectImageMaps.{u} :=
    { directImageMaps with
      etale := @Etale.scalarMate.{u}
      etale_counit := @scalarMate_normalization.{u} }
  have hd : d = directImageMaps := by
    obtain ⟨z, _, hz⟩ := directImageMaps_existsUnique.{u}
    exact (hz d trivial).trans (hz directImageMaps trivial).symm
  exact (congrArg (fun t : DirectImageMaps.{u} ↦ t.etale φ f) hd).symm

private theorem compactMap_eq {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) :
    compactMap φ c M = Etale.ExceptionalCoefficients.compactSupportMap φ c M := by
  unfold compactMap Etale.ExceptionalCoefficients.compactSupportMap
  rw [directImage_eq, openIso_eq]

private theorem comparisonInverse_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : Etale.DerivedCategoryModule A X) :
    comparisonInverse φ c M = Etale.ExceptionalCoefficients.comparisonInverse φ c M := by
  classical
  exact congrArg (fun b ↦ if h : IsIso b then @inv _ _ _ _ b h else 0)
    (compactMap_eq φ c M)

set_option maxHeartbeats 2000000 in
-- Comparing the chosen derived adjunctions unfolds their normalization data.
private theorem dualizingMap_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    dualizingMap φ f = Etale.generalFieldFiniteDualizingMap φ f := by
  unfold dualizingMap Etale.generalFieldFiniteDualizingMap
    Etale.ExceptionalCoefficients.dualizingScalarMap Etale.ExceptionalCoefficients.mateMap
  rw [comparisonInverse_eq, unitMap_eq]
  dsimp only [Etale.dualizingComplex]
  erw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

private theorem compactMap_isIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (M : Etale.DerivedCategoryModule A X) :
    IsIso (compactMap φ c M) := by
  rw [compactMap_eq]
  exact (Etale.etaleCompactScalarCoherence φ f c).1 M

private theorem quotient_annihilator
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) :
    (ell ^ n : Padic.coefficientExtensionRing ell E n) = 0 := by
  let R := Padic.coefficientExtensionIntegers ell E
  let J := Padic.coefficientExtensionMaximalIdeal ell E
  have h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := ℚ_[ell]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} : Set R) = J :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hell : (ell : R) ∈ J := by
    apply (h.2.1 _).mpr
    change spectralNorm ℚ_[ell] E (ell : E) < 1
    rw [← map_natCast (algebraMap ℚ_[ell] E) ell, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hm : (ell : R) ^ n ∈ Padic.coefficientExtensionIdeal ell E n := by
    change (ell : R) ^ n ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer ell E} : Set R) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hell _
  simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

private theorem dualizingMap_identity [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (ρ : A →+* A) (hρ : ρ = RingHom.id A)
    (hi : Etale.generalFieldFiniteDualizingMap (RingHom.id A) f =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
        (RingHom.id A) rfl).hom.app (Etale.dualizingComplex A f)) :
    dualizingMap ρ f =
      (scalarId X.smallEtaleTopology ρ hρ).hom.app (Etale.dualizingComplex A f) := by
  subst ρ
  simpa only [dualizingMap_eq, scalarId_eq] using hi

private theorem dualizingMap_composition [Finite A] [Finite B]
    {C : Type (u + 1)} [CommRing C] [Finite C]
    (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (hc : (scalarComposition X.smallEtaleTopology φ ψ).hom.app
        (Etale.dualizingComplex A f) ≫ Etale.generalFieldFiniteDualizingMap (ψ.comp φ) f =
      (Etale.scalarExtension ψ X).map (Etale.generalFieldFiniteDualizingMap φ f) ≫
        Etale.generalFieldFiniteDualizingMap ψ f) :
    (Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.smallEtaleTopology ψ).map
        (dualizingMap φ f) ≫ dualizingMap ψ f =
      (Adjunction.leftAdjointCompIso (scalarAdjunction.{u} X.smallEtaleTopology φ)
        (scalarAdjunction.{u} X.smallEtaleTopology ψ)
        (scalarAdjunction.{u} X.smallEtaleTopology χ)
        (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hχ)).hom.app
          (Etale.dualizingComplex A f) ≫ dualizingMap χ f := by
  subst χ
  simp only [dualizingMap_eq, scalarComposition] at *
  exact hc.symm

end FiniteDualizingCoefficients

open AlgebraicGeometry.FiniteCoefficientOrdinary
open FiniteDualizingCoefficients

set_option maxHeartbeats 2000000 in
-- Assemble the derived comparisons without changing their canonical representatives.
/-- The canonical quotient-coefficient dualizing map is invertible, preserves the counit,
and satisfies the identity and quotient cocycle. Its finite pro-etale realization is
uniquely specified by the scalar/site square and is an isomorphism.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.md, whole statement; current DAG proof steps 1--2, with Wei Yang
#1441, items 28--29 (blueprint: lem-coef-finite-dualizing).

Proof: (1) Apply lem-sf-general-field-finite-dualizing-coefficient-change to the actual
quotient homomorphism O_E/(varpi^n) -> O_E/(varpi^m). Its proper scalar counit mate and
open balancing are exactly the compactMap presentation of the comparison in
lem-pur-etale-compact-scalar-coherence. Adjunction identifies its dualizing map with
dualizingMap. Invertibility is local:
restrict to affine charts, embed in affine space, use the independent closed-support
coefficient comparison and affine-space adjunction, before biduality. Transposing the
local map under the composite adjunction gives the structure-morphism counit, so the
maps agree on overlaps. (2) The finite site-comparison construction already proves its
specified dualizing-object arrows invertible. The scalar/site mate is its ordinary delta.
Compose the inverse scalar image of the first comparison, delta, the realized etale map,
and the second comparison. All factors are invertible; cancellation proves the square
and uniqueness. The general-field coefficient-composition and identity equations give
the displayed quotient cocycle and unit equation, using the actual quotient ring-map
identities. Reduction modulo the uniformizer is not used to infer equality or coherence. -/
theorem finiteDualizingQuotientCurrent
    (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime]
    (_hfield : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ ell)
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    let c := NagataCompactification aX
    letI := c.hasCompactification
    letI (n : ℕ+) : Finite (Padic.coefficientExtensionRing ell E n) :=
      Padic.finite_coefficientExtensionRing ell E n n.property
    let A := fun n : ℕ+ ↦ ULift.{u + 1, u} (Padic.coefficientExtensionRing ell E n)
    let q := fun (n m : ℕ+) (h : m ≤ n) ↦ RingHom.ulift.{u + 1, u + 1}
      (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal ell E n)
        (T := Padic.coefficientExtensionIdeal ell E m) (Ideal.pow_le_pow_right h))
    let omega := fun n : ℕ+ ↦ Etale.dualizingComplex (A n) aX
    let F := fun n : ℕ+ ↦ Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A n)) aX
    let eps := fun n : ℕ+ ↦ (Etale.rightDerivedUpperShriekAdjunction (A n) aX).counit.app
      (𝟙_ (Etale.DerivedCategoryModule (A n) (Spec (.of k))))
    let uMap := fun (n m : ℕ+) (h : m ≤ n) ↦
      dualizingMap (q n m h) aX
    (∀ (n m : ℕ+) (h : m ≤ n),
      IsIso (compactMap (q n m h) c (omega n)) ∧
      IsIso (uMap n m h) ∧
      (F m).map (uMap n m h) ≫ eps m =
        comparisonInverse (q n m h) c (omega n) ≫
          (Sheaf.fixedCoefficientDerivedScalarExtension.{u} (Spec (.of k)).smallEtaleTopology
            (q n m h)).map (eps n) ≫
          unitMap (q n m h) (Spec (.of k)) ∧
      IsIso (ProEtale.finiteDualityObjectMap (Padic.coefficientExtensionRing ell E n) c) ∧
      IsIso (ProEtale.finiteDualityObjectMap (Padic.coefficientExtensionRing ell E m) c) ∧
      ∃! v : (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
          inferInstance inferInstance (q n m h)).obj
          (ProEtale.finiteDualityProEtaleObject (Padic.coefficientExtensionRing ell E n) c) ⟶
            ProEtale.finiteDualityProEtaleObject (Padic.coefficientExtensionRing ell E m) c,
        IsIso v ∧
        (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
          inferInstance inferInstance (q n m h)).map
            (ProEtale.finiteDualityObjectMap (Padic.coefficientExtensionRing ell E n) c) ≫ v =
          (siteMap (q n m h) X).app (omega n) ≫
            (Functor.mapDerivedCategory.{u + 1, u + 1}
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A m)) X)).map (uMap n m h) ≫
            ProEtale.finiteDualityObjectMap (Padic.coefficientExtensionRing ell E m) c) ∧
    (∀ n : ℕ+, uMap n n (le_refl n) =
      (scalarId X.smallEtaleTopology (q n n (le_refl n))
        (RingHom.ext (fun x ↦ congrArg ULift.up
          (DFunLike.congr_fun Ideal.Quotient.factor_eq x.down)))).hom.app (omega n)) ∧
    (∀ (n m h : ℕ+) (hmn : m ≤ n) (hhm : h ≤ m),
      (Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.smallEtaleTopology (q m h hhm)).map
          (uMap n m hmn) ≫ uMap m h hhm =
        (Adjunction.leftAdjointCompIso
          (scalarAdjunction.{u} X.smallEtaleTopology (q n m hmn))
          (scalarAdjunction.{u} X.smallEtaleTopology (q m h hhm))
          (scalarAdjunction.{u} X.smallEtaleTopology (q n h (hhm.trans hmn)))
          (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
          (RingHom.ext (fun x ↦ congrArg ULift.up
            (Ideal.Quotient.factor_comp_apply (Ideal.pow_le_pow_right hmn)
              (Ideal.pow_le_pow_right hhm) x.down).symm)))).hom.app (omega n) ≫
          uMap n h (hhm.trans hmn)) := by
  classical
  dsimp only
  let c := NagataCompactification aX
  letI := c.hasCompactification
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  let R := fun n : ℕ+ ↦ Padic.coefficientExtensionRing ell E n
  letI (n : ℕ+) : Finite (R n) :=
    Padic.finite_coefficientExtensionRing ell E n n.property
  let A := fun n : ℕ+ ↦ ULift.{u + 1, u} (R n)
  let q := fun (n m : ℕ+) (h : m ≤ n) ↦ RingHom.ulift.{u + 1, u + 1}
    (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal ell E n)
      (T := Padic.coefficientExtensionIdeal ell E m) (Ideal.pow_le_pow_right h))
  have hR (n : ℕ+) : (ell ^ (n : ℕ) : R n) = 0 :=
    quotient_annihilator ell E n
  have hA (n : ℕ+) : ∃ r : ℕ, ∀ x : A n, (ell ^ r : A n) * x = 0 := by
    have hz : (ell ^ (n : ℕ) : A n) = 0 := by
      apply ULift.down_injective
      exact hR n
    exact ⟨n, fun x ↦ by rw [hz, zero_mul]⟩
  have hd (n m : ℕ+) (h : m ≤ n) :
      Etale.GeneralFieldFiniteDualizingCoefficientChange ell (q n m h) aX :=
    Etale.generalFieldFiniteDualizingCoefficientChange k (ringChar k) ell
      (Fact.out) rfl _hfield (Fact.out) (Ne.symm _hchar) (hA n) (hA m) (q n m h)
  have hu (n m : ℕ+) (h : m ≤ n) : IsIso (dualizingMap (q n m h) aX) := by
    rw [dualizingMap_eq]
    exact (hd n m h).etale_isIso
  have hw (n : ℕ+) : IsIso (ProEtale.finiteDualityObjectMap (R n) c) := by
    exact ProEtale.isIso_objectMap (R n) c
  refine ⟨?_, ?_, ?_⟩
  · intro n m h
    have := hu n m h
    have := hw n
    have := hw m
    have : IsIso ((siteMap (q n m h) X).app (Etale.dualizingComplex (A n) aX)) := by
      rw [siteMap_eq]
      exact (hd n m h).canonical_delta_isIso
    refine ⟨compactMap_isIso (q n m h) c _, hu n m h,
      counit_dualizingMap (q n m h) aX, hw n, hw m, ?_⟩
    let S := @Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
      inferInstance inferInstance (q n m h)
    let w := S.map (ProEtale.finiteDualityObjectMap (R n) c)
    let t := (siteMap (q n m h) X).app (Etale.dualizingComplex (A n) aX) ≫
      (Functor.mapDerivedCategory.{u + 1, u + 1}
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A m)) X)).map
          (dualizingMap (q n m h) aX) ≫
        ProEtale.finiteDualityObjectMap (R m) c
    let v := inv w ≫ t
    have hv : w ≫ v = t := by simp [v]
    refine ⟨v, ⟨?_, hv⟩, ?_⟩
    · dsimp only [v, t, w, S]
      infer_instance
    · intro z hz
      exact (cancel_epi w).mp (hz.2.trans hv.symm)
  · intro n
    exact dualizingMap_identity aX (q n n (le_refl n))
      (RingHom.ext (fun x ↦ congrArg ULift.up
        (DFunLike.congr_fun Ideal.Quotient.factor_eq x.down)))
      (hd n n (le_refl n)).identity.1
  · intro n m h hmn hhm
    exact dualizingMap_composition (q n m hmn) (q m h hhm)
      (q n h (hhm.trans hmn))
      (RingHom.ext (fun x ↦ congrArg ULift.up
        (Ideal.Quotient.factor_comp_apply (Ideal.pow_le_pow_right hmn)
          (Ideal.pow_le_pow_right hhm) x.down).symm)) aX
      ((hd n m hmn).composition (hA n) (hA m) (hA h) (q m h hhm))

end WeilConjectures
