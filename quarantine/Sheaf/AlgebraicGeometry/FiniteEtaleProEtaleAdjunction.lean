/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleReverseAdjunction
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible

/-!
# The reverse adjunction for a finite etale pro-etale direct image

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
order 2062 (blueprint: prop-exc-finite-etale-adjoint).
Positive coefficient levels are indexed by `n : ℕ` with exponent `n+1`; this includes
exactly every exponent at least one. The ordinary clause is for arbitrary schemes.
Only the compact-support clause uses the ambient finite-type finite-field setting.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The published positive-level finiteness theorem supplies the coefficient instance;
this changes no coefficient ring or site universe. Source: blueprint order 2062,
coefficient convention (blueprint: prop-exc-finite-etale-adjoint). -/
noncomputable instance finiteEtaleAdjunction_coefficientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- The published exact inverse image, transported by the canonical constant-scalar
realization equivalences and applied termwise to all integer-indexed complexes.
The two `letI` declarations expose additivity of the already fixed realization;
no coefficient map, adjunction or equivalence is chosen independently.
Source: blueprint order 2062, inverse-image convention;
`def-weil-derived-pullback-tensor-hom`, finite-level clause
(blueprint: prop-exc-finite-etale-adjoint). -/
noncomputable def finiteEtaleAdjunction_inverseImage {V X : Scheme.{u}} (e : V ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory V A :=
  letI : (sfIntrinsicModuleEquivalence X A).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization X A).Additive
  letI : (sfIntrinsicModuleEquivalence V A).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization V A).Additive
  ((sfIntrinsicModuleEquivalence X A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e ⋙
    (sfIntrinsicModuleEquivalence V A).functor).mapDerivedCategory

/-- Exactness, termwise computation, and the reverse derived adjunction for finite
etale direct image. No boundedness, nonempty-fibre, or constructibility condition occurs.
Source: blueprint order 2062, first displayed adjunction
(blueprint: prop-exc-finite-etale-adjoint).

Proof: use the underived finite-etale adjunction from
`ProEtale.finiteEtale_reverseModuleAdjunction` and conjugate it by the canonical
constant-coefficient realization equivalences. The normalized direct-image
comparison identifies its left functor with the recorded intrinsic direct image.
This functor already preserves finite limits, and the transported left adjunction
gives finite colimits. Exactness identifies its total right derived functor with
its termwise derived functor; the factorization through `DerivedCategory.Q` gives
the displayed termwise computation. Derive the transported adjunction, then use
the exactness comparisons on both sides to identify its functors with the two
functors in the statement. All constructions use the ordinary unbounded derived
category; no boundedness or constructibility is introduced. -/
theorem finiteEtale_proEtale_exact_derived_adjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) {V X : Scheme.{u}} (e : V ⟶ X)
    [IsFinite e] [Etale e]
    (_hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    PreservesFiniteLimits
      (proEtaleConstantModuleDirectImage e (Padic.coefficientExtensionRing l E (n + 1))) ∧
    PreservesFiniteColimits
      (proEtaleConstantModuleDirectImage e (Padic.coefficientExtensionRing l E (n + 1))) ∧
    Nonempty
      (DerivedCategory.Q ⋙
          proEtaleConstantDerivedDirectImage e (Padic.coefficientExtensionRing l E (n + 1)) ≅
        (proEtaleConstantModuleDirectImage e
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    Nonempty
      (proEtaleConstantDerivedDirectImage e (Padic.coefficientExtensionRing l E (n + 1)) ⊣
        finiteEtaleAdjunction_inverseImage e (Padic.coefficientExtensionRing l E (n + 1))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let qV := sfIntrinsicModuleEquivalence V A
  let qX := sfIntrinsicModuleEquivalence X A
  obtain ⟨a⟩ := ProEtale.finiteEtale_reverseModuleAdjunction e (ULift.{u + 1, u} A)
  let transport : proEtaleConstantModuleDirectImage e A ≅
      qV.inverse ⋙ ProEtale.lowerStar B e ⋙ qX.functor :=
    (Functor.isoWhiskerLeft qV.inverse (sfIntrinsicDirectImageComparison e A).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight qV.counitIso _ ≪≫ Functor.leftUnitor _).symm
  let adj : proEtaleConstantModuleDirectImage e A ⊣ sfIntrinsicPullback A e :=
    ((qV.symm.toAdjunction.comp a).comp qX.toAdjunction).ofNatIsoLeft transport.symm
  have hlim : PreservesFiniteLimits (proEtaleConstantModuleDirectImage e A) :=
    (proEtaleConstantModuleDirectImage_additive_leftExact e A).2
  have hcol : PreservesFiniteColimits (proEtaleConstantModuleDirectImage e A) := by
    have : PreservesColimitsOfSize.{0, 0} (proEtaleConstantModuleDirectImage e A) :=
      adj.leftAdjoint_preservesColimits
    infer_instance
  let rd := (proEtaleConstantModuleDirectImage e A).rightDerivedFunctorIsoMapDerivedCategory
  refine ⟨hlim, hcol, ⟨?_⟩, ⟨?_⟩⟩
  · exact Functor.isoWhiskerLeft DerivedCategory.Q rd ≪≫
      (proEtaleConstantModuleDirectImage e A).mapDerivedCategoryFactors
  · exact (adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (sfIntrinsicPullback A e).rightDerivedFunctorIsoMapDerivedCategory).ofNatIsoLeft rd.symm

/-- For the proper identity compactification the compact-support candidate is the
ordinary total direct image and has inverse image as right adjoint, on the entire
unbounded derived categories. Restricting this identification to the etale-origin
subcategory gives the usual compactification-independent notation `Re_! = Re_*`.
Source: blueprint order 2062, compact-support clause
(blueprint: prop-exc-finite-etale-adjoint).

Proof: a finite map is proper (lem-weil-pbc-finite-proper), so
`Compactification.ofIsProper e.left` is exactly `(id_V,e)`. The formula of
def-weil-compact-support-candidate and def-compact-support-direct-image-detailed is
`Re_*` after extension by zero for the identity. In the defining presheaf every
test object has its unique factorization through the identity, giving the original
module sheaf and its restrictions; sheafification adds nothing. Thus that extension
is naturally the identity, and the candidate is naturally `Re_*`. The previous
clause supplies the adjunction and termwise interpretation. On the etale-origin
subcategory compactification independence permits suppression of the superscript.
No compactification independence on arbitrary unbounded objects is invoked. -/
theorem finiteEtale_proEtale_identityCompactification_adjunction
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (V X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (e : V ⟶ X) [IsFinite e.left] [Etale e.left] :
    Nonempty
      (sfIntrinsicCompactSupport (Compactification.ofIsProper e.left)
          (Padic.coefficientExtensionRing l E (n + 1)) ≅
        proEtaleConstantDerivedDirectImage e.left (Padic.coefficientExtensionRing l E (n + 1))) ∧
    Nonempty
      (sfIntrinsicCompactSupport (Compactification.ofIsProper e.left)
          (Padic.coefficientExtensionRing l E (n + 1)) ⊣
        finiteEtaleAdjunction_inverseImage e.left
          (Padic.coefficientExtensionRing l E (n + 1))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let q := sfIntrinsicModuleEquivalence V.left A
  let : q.functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive V.left A
  let ei : ProEtale.openImmersionLowerShriek B (𝟙 V.left) ≅ 𝟭 _ :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction B (𝟙 V.left)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (ProEtale.upperStarId B V.left).symm)
  let ez : sfIntrinsicExtensionByZero (𝟙 V.left) A ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft q.inverse
      (Functor.isoWhiskerRight ei q.functor ≪≫ Functor.leftUnitor q.functor) ≪≫
        q.counitIso
  let ed := Functor.mapDerivedCategoryNatIso ez ≪≫ Functor.mapDerivedCategoryIdIso _
  let ec : sfIntrinsicCompactSupport (Compactification.ofIsProper e.left) A ≅
      proEtaleConstantDerivedDirectImage e.left A :=
    Functor.isoWhiskerRight ed _ ≪≫ Functor.leftUnitor _
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have hunit (T : Over (Spec (CommRingCat.of D.k))) (t : T.left) :
      IsUnit (l : T.left.presheaf.stalk t) := by
    have h := hk.map ((StructureSheaf.toStalk (CommRingCat.of D.k) (T.hom t)) ≫
      T.hom.stalkMap t).hom
    simpa only [map_natCast] using h
  obtain ⟨adj⟩ :=
    (finiteEtale_proEtale_exact_derived_adjunction l E n e.left
      (hunit V) (hunit X)).2.2.2
  exact ⟨⟨ec⟩, ⟨adj.ofNatIsoLeft ec.symm⟩⟩

end AlgebraicGeometry.Scheme
