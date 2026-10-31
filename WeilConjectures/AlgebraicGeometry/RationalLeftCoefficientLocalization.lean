/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Over
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import Mathlib.Algebra.CharP.CharAndCard

/-! # Localization of normalized integral left coefficient laws

Source: Weil blueprint, exceptional inverse image, extracted normalized coefficient
argument, old Step 5 (blueprint: lem-sf-rational-left-coefficient-localization).
The categories are the intrinsic completed integral categories and their raw scalar
localizations. The scalar comparisons are the published balanced-tensor comparisons.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A A' B B' : C} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hA
  cases hB
  cases h
  rfl

private theorem app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ⟶ G) {K K' : C} (h : K = K') :
    HEq (a.app K) (a.app K') := by
  cases h
  rfl

private theorem comp_heq {C : Type*} [Category C]
    {A A' B B' C₀ C₀' : C} (hA : A = A') (hB : B = B') (hC : C₀ = C₀')
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ C₀} {b' : B' ⟶ C₀'}
    (ha : HEq a a') (hb : HEq b b') : HEq (a ≫ b) (a' ≫ b') := by
  cases hA
  cases hB
  cases hC
  cases ha
  cases hb
  rfl

private theorem coordinates_one
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    {K K' : sfIntegralConstructibleCategory l E X} (h : K ⟶ K') :
    (sfRationalHomCoordinates l E X _ _).symm
      (h ⊗ₜ[Padic.coefficientExtensionIntegers l E] (1 : E)) =
      (sfRationalConstructibleLocalization l E X).map h := by
  apply (sfRationalHomCoordinates l E X _ _).injective
  rw [AddEquiv.apply_symm_apply]
  symm
  simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
    sfRationalHomCoordinates, map_one]
    using (sfRationalHomCoordinates_existsUnique l E X _ _).exists.choose_spec 1 h

private theorem scalar_map_localization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (p : ℕ) (hl : l ≠ p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {K K' : sfIntegralConstructibleCategory l E X} (h : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E X p hl L ι).map
      ((sfRationalConstructibleLocalization l E X).map h))
      ((sfRationalConstructibleLocalization l L X).map
        ((sfConstructibleIntegralScalarExtension p l hl E L ι X).map h)) := by
  simpa only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, map_one] using
    (sfRationalScalarExtension_existsUnique l E X p hl L ι).exists.choose_spec.2.2 K K' h 1

private theorem comp_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u}) (p : ℕ) (hl : l ≠ p)
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (κ : L →ₐ[Padic l] M) (K : sfRationalConstructibleCategory l E X) :
    HEq ((sfRationalScalarComp l E L ι X p hl M κ).hom.app K)
      ((sfRationalConstructibleLocalization l M X).map
        ((sfIntegralScalarComp l E L ι X p hl M κ).hom.app K.obj)) :=
  (sfRationalScalarComp_existsUnique l E L ι X p hl M κ).exists.choose_spec K

private theorem unit_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (p : ℕ) (hl : l ≠ p)
    (K : sfRationalConstructibleCategory l E X) :
    HEq ((sfRationalScalarUnit l E X p hl).hom.app K)
      ((sfRationalConstructibleLocalization l E X).map
        ((sfIntegralScalarUnit l E X p hl).hom.app K.obj)) :=
  (sfRationalScalarUnit_existsUnique l E X p hl).exists.choose_spec K

attribute [local irreducible] sfRationalScalarComp sfRationalScalarUnit
  sfIntegralScalarComp sfIntegralScalarUnit sfRationalHomCoordinates
  sfRationalScalarExtension

/-- Normalized integral coefficient laws hold for the given rational functors on arrows.
Source: Weil blueprint, exceptional inverse image, extracted normalized coefficient
argument, old Step 5 (blueprint: lem-sf-rational-left-coefficient-localization).

Proof:
1. Raw localization changes no objects. Take the unchanged integral representative.
Since l differs from the characteristic, l is invertible on X. The residue-Tor lemma
identifies integral constructibility with one Tor interval for every positive reduction.
2. The scalar transition sends a localized integral arrow to its integral scalar image
localized. Apply the finite-sum normalization to a singleton with coefficient one.
It identifies the given functor's image of each localized integral arrow with the
localized integral functor image, in particular for the normalized associator and unit.
3. Apply raw localization to the integral composition equation. Its functor law
preserves the three factors. The normalized q components, scalar morphism formula,
and Step 2 identify these factors with the displayed rational composition equation.
The middle q is evaluated at the actual integral scalar extension representative.
4. Apply localization to the integral identity equation and use the same substitutions.
Every rational object was covered in Step 1. Algebra embeddings are accepted directly,
including identities and all repeated-field cases. Equality is only transported forward;
no faithfulness or reflection of equality by localization is used. -/
theorem rational_left_coefficient_localization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_c : Compactification f)
    (Fint : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E],
      sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (F : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E],
      sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (qint : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L),
      Fint E ⋙ sfConstructibleIntegralScalarExtension D.p l hl E L ι Y ≅
        sfConstructibleIntegralScalarExtension D.p l hl E L ι X ⋙ Fint L)
    (q : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L),
      F E ⋙ sfRationalScalarExtension l E Y D.p hl L ι ≅
        sfRationalScalarExtension l E X D.p hl L ι ⋙ F L)
    (hobj : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfIntegralConstructibleCategory l E X),
      (F E).obj ((sfRationalConstructibleLocalization l E X).obj K) =
        (sfRationalConstructibleLocalization l E Y).obj ((Fint E).obj K))
    (hmap : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K K' : sfIntegralConstructibleCategory l E X)
      (n : ℕ) (a : Fin n → E) (h : Fin n → (K ⟶ K')),
      HEq ((F E).map
        ((sfRationalHomCoordinates l E X _ _).symm
          (∑ i : Fin n, h i ⊗ₜ[Padic.coefficientExtensionIntegers l E] a i)))
        ((sfRationalHomCoordinates l E Y _ _).symm
          (∑ i : Fin n, (Fint E).map (h i) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            a i)))
    (hq : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (K : sfIntegralConstructibleCategory l E X),
      HEq ((q E L ι).hom.app ((sfRationalConstructibleLocalization l E X).obj K))
        ((sfRationalConstructibleLocalization l L Y).map ((qint E L ι).hom.app K)))
    (hcomp : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
      (M : Type u) [Field M] [Algebra (Padic l) M]
      [FiniteDimensional (Padic l) M] (ι : E →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M)
      (K : sfIntegralConstructibleCategory l E X),
      (sfConstructibleIntegralScalarExtension D.p l hl L M κ Y).map ((qint E L ι).hom.app K) ≫
        (qint L M κ).hom.app ((sfConstructibleIntegralScalarExtension D.p l hl E L ι X).obj K) ≫
        (Fint M).map ((sfIntegralScalarComp l E L ι X D.p hl M κ).hom.app K) =
      (sfIntegralScalarComp l E L ι Y D.p hl M κ).hom.app ((Fint E).obj K) ≫
        (qint E M (κ.comp ι)).hom.app K)
    (hunit : ∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfIntegralConstructibleCategory l E X),
      (qint E E (AlgHom.id (Padic l) E)).hom.app K ≫
        (Fint E).map ((sfIntegralScalarUnit l E X D.p hl).hom.app K) =
      (sfIntegralScalarUnit l E Y D.p hl).hom.app ((Fint E).obj K)) :
    (∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfRationalConstructibleCategory l E X),
      ∃ Kint : sfIntegralConstructibleCategory l E X,
        (sfRationalConstructibleLocalization l E X).obj Kint = K ∧
          finiteTorConstructibleIntegral l E X Kint.obj) ∧
    (∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
      (M : Type u) [Field M] [Algebra (Padic l) M]
      [FiniteDimensional (Padic l) M] (ι : E →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M)
      (K : sfRationalConstructibleCategory l E X),
      (sfRationalScalarExtension l L Y D.p hl M κ).map ((q E L ι).hom.app K) ≫
        (q L M κ).hom.app ((sfRationalScalarExtension l E X D.p hl L ι).obj K) ≫
        (F M).map ((sfRationalScalarComp l E L ι X D.p hl M κ).hom.app K) =
      (sfRationalScalarComp l E L ι Y D.p hl M κ).hom.app ((F E).obj K) ≫
        (q E M (κ.comp ι)).hom.app K) ∧
    (∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfRationalConstructibleCategory l E X),
      (q E E (AlgHom.id (Padic l) E)).hom.app K ≫
        (F E).map ((sfRationalScalarUnit l E X D.p hl).hom.app K) =
      (sfRationalScalarUnit l E Y D.p hl).hom.app ((F E).obj K)) ∧
    (∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
      (M : Type u) [Field M] [Algebra (Padic l) M]
      [FiniteDimensional (Padic l) M] (ι : E →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M)
      (K : sfIntegralConstructibleCategory l E X),
      HEq ((F M).map ((sfRationalScalarComp l E L ι X D.p hl M κ).hom.app
        ((sfRationalConstructibleLocalization l E X).obj K)))
        ((sfRationalConstructibleLocalization l M Y).map
          ((Fint M).map ((sfIntegralScalarComp l E L ι X D.p hl M κ).hom.app K)))) ∧
    (∀
      (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfIntegralConstructibleCategory l E X),
      HEq ((F E).map ((sfRationalScalarUnit l E X D.p hl).hom.app
        ((sfRationalConstructibleLocalization l E X).obj K)))
        ((sfRationalConstructibleLocalization l E Y).map
          ((Fint E).map ((sfIntegralScalarUnit l E X D.p hl).hom.app K)))) := by
  classical
  have hm (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] {K K' : sfIntegralConstructibleCategory l E X}
      (h : K ⟶ K') :
      HEq ((F E).map ((sfRationalConstructibleLocalization l E X).map h))
        ((sfRationalConstructibleLocalization l E Y).map ((Fint E).map h)) := by
    have hh := hmap E K K' 1 (fun _ ↦ 1) (fun _ ↦ h)
    simp only [Fin.sum_univ_one] at hh
    rw [coordinates_one l E X h, coordinates_one l E Y ((Fint E).map h)] at hh
    exact hh
  have ho (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfRationalConstructibleCategory l E X) :
      (F E).obj K =
        (sfRationalConstructibleLocalization l E Y).obj ((Fint E).obj K.obj) :=
    hobj E K.obj
  have hc (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
      (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
      (ι : E →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M)
      (K : sfIntegralConstructibleCategory l E X) :
      HEq ((F M).map ((sfRationalScalarComp l E L ι X D.p hl M κ).hom.app
        ((sfRationalConstructibleLocalization l E X).obj K)))
        ((sfRationalConstructibleLocalization l M Y).map
          ((Fint M).map ((sfIntegralScalarComp l E L ι X D.p hl M κ).hom.app K))) := by
    have ha := comp_component l E L ι X D.p hl M κ
      ((sfRationalConstructibleLocalization l E X).obj K)
    exact (map_heq (F M)
      (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (sfRationalScalarExtension_obj l E X D.p hl M (κ.comp ι) _) ha).trans (hm M _)
  have hu (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (K : sfIntegralConstructibleCategory l E X) :
      HEq ((F E).map ((sfRationalScalarUnit l E X D.p hl).hom.app
        ((sfRationalConstructibleLocalization l E X).obj K)))
        ((sfRationalConstructibleLocalization l E Y).map
          ((Fint E).map ((sfIntegralScalarUnit l E X D.p hl).hom.app K))) := by
    have ha := unit_component l E X D.p hl
      ((sfRationalConstructibleLocalization l E X).obj K)
    exact (map_heq (F E) (sfRationalScalarExtension_obj l E X D.p hl E
      (AlgHom.id (Padic l) E) _) rfl ha).trans (hm E _)
  refine ⟨?_, ?_, ?_, hc, hu⟩
  · intro E _ _ _ K
    refine ⟨K.obj, rfl, ?_⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
    have hbase : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
      intro hdiv
      exact hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
    have hk : IsUnit (l : D.k) := by
      simpa only [map_natCast] using hbase.map (algebraMap D.k₀ D.k)
    let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦ by
      let φ : D.k →+* X.residueField x :=
        ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop ≫
          X.Γevaluation x).hom
      exact (map_natCast φ l ▸ hk.map φ).invertible
    rw [← (integral_residue_tor D l hl E X).2]
    exact K.obj.property
  · intro E _ _ _ L _ _ _ M _ _ _ ι κ K
    have ha := (map_heq (sfRationalScalarExtension l L Y D.p hl M κ)
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (hq E L ι K.obj)).trans (scalar_map_localization l L Y D.p hl M κ _)
    have hb := (app_heq (q L M κ).hom
      (sfRationalScalarExtension_obj l E X D.p hl L ι K)).trans
      (hq L M κ ((sfConstructibleIntegralScalarExtension D.p l hl E L ι X).obj K.obj))
    have hd := hc E L M ι κ K.obj
    have hleft := comp_heq
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization]) ha
      (comp_heq
        (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
          sfRationalConstructibleLocalization, ScalarLocalization.localization])
        (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
          sfRationalConstructibleLocalization, ScalarLocalization.localization])
        (by simp only [ho, sfRationalScalarExtension_obj,
          sfRationalConstructibleLocalization, ScalarLocalization.localization]) hb hd)
    have he := (app_heq (sfRationalScalarComp l E L ι Y D.p hl M κ).hom (ho E K)).trans
      (comp_component l E L ι Y D.p hl M κ
        ((sfRationalConstructibleLocalization l E Y).obj ((Fint E).obj K.obj)))
    have hright := comp_heq
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization]) he
      (hq E M (κ.comp ι) K.obj)
    have hi := congrArg ((sfRationalConstructibleLocalization l M Y).map)
      (hcomp E L M ι κ K.obj)
    simp only [Functor.map_comp] at hi
    exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))
  · intro E _ _ _ K
    have hleft := comp_heq
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, ho, sfRationalScalarExtension_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (ho E K) (hq E E (AlgHom.id (Padic l) E) K.obj) (hu E K.obj)
    have hright := (app_heq (sfRationalScalarUnit l E Y D.p hl).hom (ho E K)).trans
      (unit_component l E Y D.p hl
        ((sfRationalConstructibleLocalization l E Y).obj ((Fint E).obj K.obj)))
    have hi := congrArg ((sfRationalConstructibleLocalization l E Y).map) (hunit E K.obj)
    rw [Functor.map_comp] at hi
    exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

end WeilConjectures
