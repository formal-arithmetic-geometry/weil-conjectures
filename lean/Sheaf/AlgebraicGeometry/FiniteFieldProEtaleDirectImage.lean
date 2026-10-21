/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import all Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Finite-field pro-etale direct-image finiteness

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.2 specialized
at a finite field, with Lemma 5.4.3 and Theorem 6.7.1
(blueprint: lem-sfb-finite-field-proetale-direct-image).

The categories are the ordinary uncompleted categories of intrinsic modules over the
constant ring sheaf. The total right derived functor is the recorded universal
K-injective construction, with its resolution hypothesis supplied by the existing
K-injective resolution instance. No separatedness or restriction on the base field
beyond its positive characteristic different from the coefficient characteristic is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Ordinary total direct image preserves bounded constructible complexes with finite
field coefficients of characteristic invertible in the base field.
Source: Bhatt--Scholze, Lemmas 6.7.2 and 5.4.3, Theorem 6.7.1, finite-field case
(blueprint: lem-sfb-finite-field-proetale-direct-image).

Proof:
1. The source is locally Noetherian, hence quasi-separated; the given quasi-compact
   morphism is therefore qcqs. No separatedness is required.
2. Restrict to constant scalars using `proEtaleModuleRestriction_isEquivalence` and
   `proEtaleModuleRestriction_constructible_iff`. Exactness transports the input bounds
   and constructibility. The proved `fixedDerivedOrigin` helper of
   `lem-sf-proetale-constructible-origin` supplies a bounded constructible etale antecedent.
   This uses global finite stratifications directly, avoiding affine-local gluing.
3. Positive characteristic of k is prime. If ell vanished in k, its characteristic
   would divide ell and hence equal ell, contrary to the hypothesis. Thus ell is a unit
   in k and annihilates A. Apply `thm-dg-finite-type-constructibility` to the antecedent.
4. Apply `prop-weil-pbc-comparison-direct-image` in the bounded-below category. The
   full/plus compatibility isomorphisms and the proved `restrictionDerivedDirectImageIso`
   helper identify its value with the intrinsic ordinary derived direct image.
5. Choose a K-injective representative of K. Both the standard derived functor and the
   specified arbitrary-resolution functor evaluate to the direct image of this same
   representative, giving an isomorphism between their values.
6. Apply the homology comparison isomorphisms. Exact comparison preserves zero homology
   and constructibility, and scalar restriction reflects them. This transports the
   output interval and each constructible cohomology sheaf to the asserted value. -/
theorem finiteField_proEtale_directImage_bounded_constructible
    (ell p : ℕ) (hell : ell.Prime) (hp : 0 < p) (hne : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (A : Type u) [Field A] [Finite A] [CharP A ell]
    {T V : Scheme.{u}} (aT : T ⟶ Spec (.of k)) (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (f : T ⟶ V) (hf : f ≫ aV = aT) [LocallyOfFiniteType f] [QuasiCompact f]
    (K : proEtaleDerivedCategory T A)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K))
    (hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)) :
    (fun L : proEtaleDerivedCategory V A ↦
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules V (proEtaleConstantRing V A)) q).obj L)) ∧
      ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf V A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules V (proEtaleConstantRing V A)) q).obj L))
      (((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorOfQuasiIsoResolutions
        (fun C ↦ (Abelian.HasKInjectiveResolutions.exists_isKInjective C).elim
          (fun I hI ↦ hI.elim (fun hI hs ↦ hs.elim
            (fun s hs ↦ ⟨I, s, hI, hs.2⟩))))).obj K) := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  let B := ULift.{u + 1, u} A
  let RX := proEtaleModuleRestriction T A
  let RY := proEtaleModuleRestriction V A
  have : RX.Additive := { map_add := by intros; rfl }
  have : RY.Additive := { map_add := by intros; rfl }
  have : RX.IsEquivalence := proEtaleModuleRestriction_isEquivalence T A
  have : RY.IsEquivalence := proEtaleModuleRestriction_isEquivalence V A
  let M := RX.mapDerivedCategory.obj K
  have hc (q : ℤ) : ProEtale.IsConstructible B
      ((DerivedCategory.homologyFunctor _ q).obj M) := by
    exact ProEtale.isConstructible_of_iso
      ((RX.mapDerivedCategoryHomologyFunctorIso q).app K)
      ((proEtaleModuleRestriction_constructible_iff T A _).mp (hconstructible q))
  obtain ⟨a, b, _, hv⟩ := hbounded
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := ProEtale.fixedDerivedOrigin T B M hc a b
    (fun q hq ↦ RX.isZero_homologyFunctor_mapDerivedCategory_obj (hv q hq))
  have hellk : IsUnit (ell : k) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hdvd := (CharP.cast_eq_zero_iff k p ell).mp h
    rcases (Nat.dvd_prime hell).mp hdvd with he | he
    · have hpprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp.ne'
      exact hpprime.ne_one he
    · exact hne he
  have hB : Etale.IsSmoothBaseChangeCoefficients ell B (Spec (.of k)) := by
    refine ⟨hell.pos, inferInstance, ?_, ?_⟩
    · apply ULift.down_injective
      exact CharP.cast_eq_zero A ell
    · simpa only [map_natCast] using hellk.map (Scheme.ΓSpecIso (.of k)).inv.hom
  let νX := ProEtale.comparisonUpperStar (ModuleCat B) T
  let νY := ProEtale.comparisonUpperStar (ModuleCat B) V
  let F := Etale.lowerStar (ModuleCat B) f
  let G := ProEtale.lowerStar (ModuleCat B) f
  have hFJ := Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    k B ell hB aT aV f hf J hJ
  obtain ⟨aJ, bJ, _, hvJ⟩ := hJ.2
  let Jp : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat B)) :=
    ⟨J, ⟨aJ, (DerivedCategory.isGE_iff J aJ).2
      (fun q hq ↦ hvJ q (Or.inl hq))⟩⟩
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (ProEtale.lowerStarComparisonUpperStarBaseChange f (ModuleCat B))) :=
    ProEtale.isIso_comparisonDirectImagePlus B f
  let e := asIso (Functor.rightDerivedFunctorPlusBaseChange
    (ProEtale.lowerStarComparisonUpperStarBaseChange f (ModuleCat B)))
  let er := (ProEtale.restrictionDerivedDirectImageIso f A).app K
  let eOut : νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj J) ≅
      RY.mapDerivedCategory.obj ((proEtaleConstantDerivedDirectImage f A).obj K) :=
    νY.mapDerivedCategory.mapIso (F.rightDerivedFunctorPlusCompatibility.app Jp).symm ≪≫
      (νY.mapDerivedCategoryPlusCompatibility.app (F.rightDerivedFunctorPlus.obj Jp)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso (e.app Jp) ≪≫
      G.rightDerivedFunctorPlusCompatibility.app (νX.mapDerivedCategoryPlus.obj Jp) ≪≫
      G.rightDerivedFunctor.mapIso (νX.mapDerivedCategoryPlusCompatibility.app Jp) ≪≫
      G.rightDerivedFunctor.mapIso eJ ≪≫ er.symm
  let P := proEtaleConstantModuleDirectImage f A
  let hres : ∀ C : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ,
      ∃ (I : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
        (s : C ⟶ I), I.IsKInjective ∧ QuasiIso s :=
    fun C ↦ (Abelian.HasKInjectiveResolutions.exists_isKInjective C).elim
    (fun I hI ↦ hI.elim (fun hI hs ↦ hs.elim (fun s hs ↦ ⟨I, s, hI, hs.2⟩)))
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have := hI
  let eTotal : (proEtaleConstantDerivedDirectImage f A).obj K ≅
      (P.rightDerivedFunctorOfQuasiIsoResolutions hres).obj K :=
    P.rightDerivedFunctor.mapIso eI ≪≫ P.rightDerivedFunctorObjQIso I ≪≫
      (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hres (𝟙 I)).symm ≪≫
      (P.rightDerivedFunctorOfQuasiIsoResolutions hres).mapIso eI.symm
  obtain ⟨aO, bO, habO, hvO⟩ := hFJ.2
  refine ⟨⟨aO, bO, habO, fun q hq ↦ ?_⟩, fun q ↦ ?_⟩
  · apply RY.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (νY.map_isZero (hvO q hq)).of_iso
      ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso
          (eOut ≪≫ RY.mapDerivedCategory.mapIso eTotal)).symm
  · apply (proEtaleModuleRestriction_constructible_iff V A _).mpr
    have hq : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj (F.rightDerivedFunctor.obj J)) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)
    exact ProEtale.isConstructible_of_iso
      ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso
          (eOut ≪≫ RY.mapDerivedCategory.mapIso eTotal) ≪≫
        (RY.mapDerivedCategoryHomologyFunctorIso q).symm.app _)
      (ProEtale.isConstructible_comparisonUpperStar_obj _)

end AlgebraicGeometry.Scheme
