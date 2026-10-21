/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.SiteDerivedTensorRestriction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# Signed shifts on the published site derived tensor

Source: Stacks Project, more-algebra.tex, Tag 0FNH, item-shift-tensor;
sites-cohomology.tex, Tags 06YS and 06YU; Categories, Tag 04VK.
(blueprint: lem-weil-pbc-derived-tensor-shift-descent)

The representative comparison is the published resolving comparison exposed by
`tensorDescentPair`. The predicates below spell out its normalization and the
universal fixed-comparison conclusion; they do not choose another tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

/-- A transparent abbreviation of Mathlib's existing total tensor functor, exposing its
canonical signed shift instances. This is definitionally `SiteTensorComplexFunctor R`.
Source: Stacks, Tags 06YM and 0FNH
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
abbrev tensorShiftTotal :=
  (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).map₂CochainComplex

/-- The prescribed restriction of both shift comparisons to flat-term K-flat pairs.
This is the conjugation by the published representative comparison and the canonical
localization shift comparison, written without inverse arrows by clearing the two
invertible initial factors.
Source: Stacks, Tags 0FNH and 06YU
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
def tensorResolvingShiftCompatible
    (stable : ∀ (P : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (P⟦n⟧))
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int) : Prop :=
  letI := s
  ∀ (P S : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : TensorFlatRepresentative (J := J) (R := R) P)
    (hS : TensorFlatRepresentative (J := J) (R := R) S) (n : ℤ),
    ((tensorDescentPair (J := J) (R := R)
        (P⟦n⟧) S (stable P hP n) hS).hom ≫
        ((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj S)).map (((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
            P) ≫
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj S)).commShiftIso n).hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₁Iso P S
            (MonoidalCategory.curriedTensor _) n).hom ≫
        ((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
          (((tensorShiftTotal (R := R)).obj P).obj S) ≫
        (tensorDescentPair (J := J) (R := R) P S hP hS).hom⟦n⟧') ∧
    ((tensorDescentPair (J := J) (R := R)
        P (S⟦n⟧) hP (stable S hS n)).hom ≫
        ((siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj P)).map (((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
            S) ≫
        (((siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj P)).commShiftIso n).hom.app (DerivedCategory.Q.obj S) =
      DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₂Iso P S
            (MonoidalCategory.curriedTensor _) n).hom ≫
        ((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
          (((tensorShiftTotal (R := R)).obj P).obj S) ≫
        (tensorDescentPair (J := J) (R := R) P S hP hS).hom⟦n⟧')

/-- Every fixed-factor comparison normalized on resolving objects respects the signed shifts.
The natural isomorphisms are pulled back to complexes along the full homotopy quotient.
Thus their naturality is exactly naturality on the homotopy category; the quotient's
canonical shift comparison identifies these squares with the homotopy-level squares.
`NatTrans.CommShift` says that the given shifts coincide with the shifts descended in
one variable under this factorization.
Source: Stacks, Tags 06YS, 06YU and 04VK
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
def tensorFixedComparisonsShiftCompatible
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int) : Prop :=
  letI := s
  ∀ (A : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hA : TensorFlatRepresentative (J := J) (R := R) A),
    (∀ (B B' : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (f : B ⟶ B'),
      QuasiIso f → QuasiIso (((tensorShiftTotal (R := R)).obj A).map f) ∧
        QuasiIso (((tensorShiftTotal (R := R)).flip.obj A).map f)) →
    (∀ eL : (tensorShiftTotal (R := R)).obj A ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj A),
      (∀ (B : CochainComplex (ringedSiteModules.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
        (hB : TensorFlatRepresentative (J := J) (R := R) B),
        eL.app B = tensorDescentPair (J := J) (R := R) A B hA hB) → NatTrans.CommShift eL.hom ℤ) ∧
    (∀ eR : (tensorShiftTotal (R := R)).flip.obj A ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj A),
      (∀ (B : CochainComplex (ringedSiteModules.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
        (hB : TensorFlatRepresentative (J := J) (R := R) B),
        eR.app B = tensorDescentPair (J := J) (R := R) B A hB hA) → NatTrans.CommShift eR.hom ℤ)

/-- Uniqueness of the normalized natural isomorphisms themselves, without assuming
coherence laws on a competing isomorphism. Once the restriction of a candidate agrees
with the prescribed shifts on resolving pairs, all of its components agree.
Source: Stacks, Tag 04VK, and the arbitrary-transformation clause of tensor descent
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
def tensorShiftComparisonsUnique
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int) : Prop :=
  letI := s
  (∀ (n : ℤ)
    (α : (shiftFunctor _ n).prod (𝟭 _) ⋙
        siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ≅
      siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ⋙ shiftFunctor _ n),
    (∀ (P S : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      TensorFlatRepresentative (J := J) (R := R) S →
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj S)).commShiftIso n).hom.app (DerivedCategory.Q.obj P)) →
    ∀ (M N : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
      α.hom.app (M, N) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj N).commShiftIso n).hom.app M) ∧
  (∀ (n : ℤ)
    (α : (𝟭 _).prod (shiftFunctor _ n) ⋙
        siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ≅
      siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ⋙ shiftFunctor _ n),
    (∀ (P S : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      TensorFlatRepresentative (J := J) (R := R) S →
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj P)).commShiftIso n).hom.app (DerivedCategory.Q.obj S)) →
    ∀ (M N : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
      α.hom.app (M, N) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).obj M).commShiftIso n).hom.app N)

/-- The published derived tensor has unique normalized coherent signed integer shifts,
and every normalized fixed-factor comparison respects them.
Source: Stacks, Tag 0FNH (item-shift-tensor), Tags 06YS, 06YU and 04VK
(blueprint: lem-weil-pbc-derived-tensor-shift-descent).

Proof plan:
1. On resolving pairs conjugate the chain shift comparisons by the published tensor
   comparison and the localization shift comparisons. Shift stability supplies all
   shifted resolving representatives. Naturality gives transformations on resolving pairs.
2. Use arbitrary-transformation extension in lem-weil-pbc-site-derived-tensor-descent
   to extend both transformations and their inverses. Faithfulness makes them inverse
   and proves uniqueness on this specified tensor.
3. Check the zero and addition identities after restriction. When a shifted localized
   representative occurs, rewrite it by naturality along the localization shift iso
   before applying the restriction formula. Cancel consecutive representative comparisons;
   the chain and localization coherence identities give the required equalities.
4. The same restriction argument descends the mixed identity from
   lem-weil-pbc-total-tensor-integer-shifts. Its sign is (-1)^(ab), since the two
   second-factor extractions use first degrees p and p+a. Additive localization and
   conjugation preserve that sign. These laws are exactly Functor.CommShift₂Int.
5. Its commShift_map and commShift_flip_map fields give compatibility for every derived
   fixed-argument morphism. Invert the squares for quasi-isomorphisms and paste them
   along any localization word. Functoriality removes dependence on the word.
6. For a normalized eL, the two sides of its shift square agree on a resolving B,
   by substitution of the restriction formula; B[n] is resolving too.
7. For arbitrary B choose a flat-term K-flat resolution P → B using
   lem-pc-kflat-resolution. Naturality compares the square at B with that at P.
   The image of H(P[n]) → H(B[n]) is invertible by quasi-isomorphism preservation;
   cancel it. The same argument with the tensor order reversed handles eR.
8. The localization universal property uniquely descends the one-variable signed shifts
   of H_A and H^A. The squares just proved say precisely that the restrictions of our
   bifunctor shifts have that characterization, so the descended shifts agree.
   No bound on any complex occurs.
-/
theorem derived_tensor_shift_descent
    (stable : ∀ (P : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (P⟦n⟧)) :
    ∃ s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int,
      tensorResolvingShiftCompatible (J := J) (R := R) stable s ∧
      tensorShiftComparisonsUnique (J := J) (R := R) s ∧
      tensorFixedComparisonsShiftCompatible (J := J) (R := R) s := by
  sorry

end SheafOfModules
