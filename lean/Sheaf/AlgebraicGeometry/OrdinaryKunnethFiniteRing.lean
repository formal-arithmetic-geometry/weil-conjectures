/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.OrdinaryKunnethMap
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.AbsoluteKunnethComparison

/-!
# Ordinary Kunneth for a finite p-adic coefficient ring

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-a1-kummer,
node lem-pur-ordinary-kunneth-finite-ring, order 1937
(blueprint: lem-pur-ordinary-kunneth-finite-ring).

## Main definitions

- `derivedConstantPullbackIso`: the canonical comparison for constant derived complexes.
- `ordinaryKunnethPulledCounit`: the global-sections counit pulled back to the product.
- `ordinaryKunnethTensorMate`: the abstract tensor-of-counits adjunct.
- `ordinaryGlobalKunnethMap`: the canonical absolute exterior-product arrow.

## Main statements

- `isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`: invertibility at positive finite level.
-/

@[expose] public section

universe u uA uC vC uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

noncomputable section


private theorem constantPresheaf_monoidal_eq
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    etaleConstantPresheafMonoidal Λ X =
      Functor.Monoidal.const X.Etaleᵒᵖ (ModuleCat.{u + 1} Λ) := by
  apply Functor.Monoidal.toLaxMonoidal_injective
  ext1
  · apply NatTrans.ext
    funext U
    exact (Classical.choose_spec (exists_etaleConstantPresheafCoreMonoidal Λ X)).1 U
  · funext M N
    apply NatTrans.ext
    funext U
    exact (Classical.choose_spec (exists_etaleConstantPresheafCoreMonoidal Λ X)).2 M N U

private theorem constantSheaf_monoidal_eq
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    etaleConstantSheafMonoidal Λ X =
      monoidalConstantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let combine (h : (Functor.const X.Etaleᵒᵖ (C := ModuleCat.{u + 1} Λ)).Monoidal) :
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Monoidal :=
    letI := h
    inferInstanceAs (Functor.const X.Etaleᵒᵖ ⋙
      presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Monoidal
  change combine (etaleConstantPresheafMonoidal Λ X) =
    combine (Functor.Monoidal.const X.Etaleᵒᵖ (ModuleCat.{u + 1} Λ))
  exact congrArg combine (constantPresheaf_monoidal_eq Λ X)

private theorem isIso_ordinaryGlobalKunnethMap_of_relative
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {S X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (w : q ≫ g = p ≫ f)
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    [(constantSheaf S.smallEtaleTopology A).IsEquivalence]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    [hZ : (constantSheaf Z.smallEtaleTopology A).Monoidal]
    (hcanon : hZ = monoidalConstantSheaf Z.smallEtaleTopology A)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    [IsIso (kunnethMap A p q f g (p ≫ f) rfl w K M)] :
    IsIso (ordinaryGlobalKunnethMap A p q K M) := by
  cases hcanon
  rw [ordinaryGlobalKunnethMap_eq_relative A p q f g w K M]
  unfold ordinaryRelativeGlobalKunnethMap ordinaryKunnethTensorMate
  rw [Adjunction.homEquiv_unit]
  infer_instance

private theorem isIso_ordinaryGlobalKunnethMap_finiteRing
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsSepClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    (p : Z ⟶ X) (q : Z ⟶ Y) (sq : IsPullback p q f g)
    (K : DerivedCategoryModule Λ X) (M : DerivedCategoryModule Λ Y) :
    IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} Λ) p q K M) := by
  have := isIso_kunnethMap_of_isSepClosed Λ f g p q sq K M
  let e := constantSheafEquivalenceOfIsSepClosed Λ (k := k)
  have : (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).IsEquivalence := e.isEquivalence_functor
  exact isIso_ordinaryGlobalKunnethMap_of_relative (ModuleCat.{u + 1} Λ)
    p q f g sq.w.symm (constantSheaf_monoidal_eq Λ Z) K M

private theorem finiteCoefficientRing_invertibleExponent
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar D.k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    HasInvertibleExponent (Padic.coefficientExtensionRing l E n)
      (Spec (CommRingCat.of D.k)) := by
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (hdvr.2.1 _).2
    change spectralNorm (Padic l) E (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E),
      spectralNorm_extends (K := Padic l) (L := E)]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    rw [Nat.cast_pow]
    change (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hm n
  have hlk : (l : D.k) ≠ 0 := fun hz ↦
    hl (CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm
  refine ⟨l ^ n, pow_pos (Nat.Prime.pos Fact.out) _, hkill, ?_⟩
  simpa only [map_pow, map_natCast, Nat.cast_pow] using
    ((Ne.isUnit hlk).pow n).map (Scheme.ΓSpecIso (.of D.k)).inv.hom

-- Use the ring underlying the quotient CommRing, as in the abstract-ring theorem.
-- This avoids comparing it with the separate direct quotient Ring instance.
attribute [local instance 2000] CommRing.toRing

/-- The canonical exterior-product arrow is invertible for arbitrary unbounded complexes
on separated finite-type schemes over the fixed algebraic closure of a finite field,
with coefficients in the positive-level quotient of a finite p-adic extension.

Source: blueprint order 1937, lem-pur-ordinary-kunneth-finite-ring.md
(blueprint: lem-pur-ordinary-kunneth-finite-ring).

Proof: The coefficient ring is finite. The spectral norm of `l` is less than one, so
`l` lies in the maximal ideal generated by the recorded uniformizer. Hence `l ^ n`
annihilates the level `n` quotient. Its image in the base field is a unit because
`l` differs from the characteristic. Thus this actual coefficient ring satisfies
`HasInvertibleExponent`.

The base field is separably closed, so the adopted arbitrary-finite-ring theorem
`isIso_kunnethMap_of_isSepClosed` makes the relative canonical Kunneth map invertible.
The constants functor on the point is an equivalence. Its derived adjunction unit,
counit and tensor comparison are therefore isomorphisms. Transport relative Kunneth
through these adjunctions, and use `ordinaryGlobalKunnethMap_eq_relative` to identify
that composite with the specified absolute arrow. The identity-component normalization
of the chosen constant-presheaf monoidal core identifies it with the standard core.
This argument uses neither coefficient restriction nor residue-field devissage.
-/
theorem isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar D.k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X.left)
    (M : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y.left) :
    IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
      (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom) K M) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let Λ := Padic.coefficientExtensionRing l E n
  have : Finite Λ := Padic.finite_coefficientExtensionRing l E n _hn
  have : HasInvertibleExponent Λ (Spec (CommRingCat.of D.k)) :=
    finiteCoefficientRing_invertibleExponent D l _hl E n
  exact isIso_ordinaryGlobalKunnethMap_finiteRing Λ X.hom Y.hom
    (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom)
    (IsPullback.of_hasPullback X.hom Y.hom) K M

end

end AlgebraicGeometry.Etale
