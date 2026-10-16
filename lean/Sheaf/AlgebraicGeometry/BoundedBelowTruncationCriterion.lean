/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Bounded-below truncation criterion

Source: blueprint sec-smooth-base-change/sk-rem-rest,
node sbc-lem-bounded-below-truncation-criterion, order 1439
(blueprint: sbc-lem-bounded-below-truncation-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The upper tail of the truncation triangle vanishes in both adjacent degrees. -/
private theorem truncation_map_isIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (E : DerivedCategory A) (a : ℤ), E.IsGE a → (F.obj E).IsGE a)
    (E : DerivedCategory A) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor B n).map
      (F.map ((DerivedCategory.TStructure.t.truncLEι n).app E))) := by
  let t := DerivedCategory.TStructure.t (C := A)
  have hbound : (F.obj ((t.truncGT n).obj E)).IsGE (n + 1) :=
    hF _ _ (inferInstanceAs (t.IsGE ((t.truncGT n).obj E) (n + 1)))
  have hzero (i : ℤ) (hi : i < n + 1) :
      IsZero ((DerivedCategory.homologyFunctor B i).obj
        (F.obj ((t.truncGT n).obj E))) := by
    have := hbound
    exact DerivedCategory.isZero_of_isGE _ (n + 1) i hi
  exact DerivedCategory.isIso_homologyMap_mor₁ _
    (F.map_distinguished _ (t.triangleLEGT_distinguished n E)) (n - 1) n (by omega)
    (hzero (n - 1) (by omega)) (hzero n (by omega))

/-- Transport bounded-below negative vanishing along the total-derived comparison. -/
private theorem direct_image_bound {V W : Scheme.{u}} (g : V ⟶ W)
    (E : DerivedCategory (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a : ℤ) (ha : E.IsGE a) : ((hypercohomologyFirstFunctor g).obj E).IsGE a := by
  let Eplus : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) := ⟨E, ⟨a, ha⟩⟩
  have : Eplus.IsGE a := (Eplus.isGE_ι_obj_iff a).1 ha
  refine (DerivedCategory.isGE_iff _ a).2 fun i hi ↦ ?_
  exact (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    (lowerStar AddCommGrpCat.{u + 1} g) Eplus a hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.app
          Eplus)).symm

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The initial E-term vanishes, and kernels and quotients preserve that vanishing. - /
private theorem hypercohomology_page_negative
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (E : DerivedCategory A) (a : ℤ), E.IsGE a → (F.obj E).IsGE a)
    (L : CochainComplex.Plus A) (r : ℕ) (p q : ℤ) (hp : p < 0) :
    IsZero ((hypercohomologyCouple F L).page r p q) := by
  have hE : IsZero ((hypercohomologyCouple F L).E p q) := by
    change IsZero ((DerivedCategory.homologyFunctor B (p + q)).obj
      (F.obj (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex L q).obj)))
    have hge : (DerivedCategory.Q.obj
        (TruncationCouple.cohomologyComplex L q).obj).IsGE q := by
      dsimp [TruncationCouple.cohomologyComplex]
      infer_instance
    have := hF _ q hge
    exact DerivedCategory.isZero_of_isGE _ q _ (by omega)
  have hzero (k : ℕ) : IsZero (((hypercohomologyCouple F L).pageCouple k).E p q) := by
    induction k with
    | zero => exact hE
    | succ k ih =>
      change IsZero (cokernel _)
      apply IsZero.of_epi (cokernel.π _)
      exact IsZero.of_mono (kernel.ι _) ih
  exact hzero (r - 2)
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- Canonical truncation above n does not change the degree-n cohomology of the three
hypercohomology functors. In each truncation spectral sequence all terms above q = n
on the degree-n diagonal vanish, on every page starting at E₂. The support assertion
is expressed on every bounded-below representative of K, so involves no choice of resolution.
Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1439
(blueprint: sbc-lem-bounded-below-truncation-criterion).

Proof:
1. Choose a lower cohomology bound a and a representative vanishing below a, using
   def-sbc-standard-tstructure-derived-category. The three spectral sequences of
   def-weil-pbc-hypercohomology-filtrations have p ≥ 0; hence p + q = n forces q ≤ n.
   This remains true on later pages, which are subquotients of the preceding pages.
2. Apply part 5 of thm-sp-truncation-e2 to g_*: its canonical map c_n is invertible.
   The substitutions in def-sp-etale-dictionary identify this with the first map here.
3. prop-weil-pbc-inverse-image-exact and lem-weil-pbc-exact-functor-bounded-below
   identify the second map with f⁻¹ applied to the first, hence it is invertible.
4. Exactness of e⁻¹ identifies its termwise image of the canonical truncation and
   inclusion with those of e⁻¹K. Apply part 5 of thm-sp-truncation-e2 to h_* to get
   invertibility of the third map. No torsion-preservation hypothesis is needed. - /
theorem boundedBelow_truncation_criterion
    {Y T X S : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)
    (_sq : ChosenCartesianSquare e h g f) (P : Set ℕ)
    (K : AbelianDerivedCategoryPlusTorsionOfPrimes T P) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((hypercohomologyFirstFunctor g).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((hypercohomologyBaseChangeFunctor g f).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((hypercohomologySecondFunctor h e).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ∧
    (∀ L : CochainComplex.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
      Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj) →
      ∀ (r : ℕ) (q : ℤ), 2 ≤ r → n < q →
        IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor g) L).page r (n - q) q) ∧
        IsZero ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor g f) L).page
          r (n - q) q) ∧
        IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor h e) L).page
          r (n - q) q)) := by
  -- Use left t-exactness on the upper tail instead of the full convergence theorem.
  have hfirstGE (E : DerivedCategory
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (a : ℤ) (ha : E.IsGE a) :
      ((hypercohomologyFirstFunctor g).obj E).IsGE a :=
    direct_image_bound g E a ha
  have hbaseGE (E : DerivedCategory
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (a : ℤ) (ha : E.IsGE a) :
      ((hypercohomologyBaseChangeFunctor g f).obj E).IsGE a := by
    have := hfirstGE E a ha
    exact (upperStar AddCommGrpCat.{u + 1} f).isGE_mapDerivedCategory_obj _ a
  have hsecondGE (E : DerivedCategory
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (a : ℤ) (ha : E.IsGE a) :
      ((hypercohomologySecondFunctor h e).obj E).IsGE a := by
    have := ha
    have := (upperStar AddCommGrpCat.{u + 1} e).isGE_mapDerivedCategory_obj E a
    exact direct_image_bound h _ a (by assumption)
  refine ⟨truncation_map_isIso _ hfirstGE K.obj n,
    truncation_map_isIso _ hbaseGE K.obj n, truncation_map_isIso _ hsecondGE K.obj n, ?_⟩
  intro L _ r q _ hnq
  exact ⟨hypercohomology_page_negative _ hfirstGE L r (n - q) q (by omega),
    hypercohomology_page_negative _ hbaseGE L r (n - q) q (by omega),
    hypercohomology_page_negative _ hsecondGE L r (n - q) q (by omega)⟩
-/

end AlgebraicGeometry.Etale
