/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Sheaf.CategoryTheory.AdditiveLocalizationDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Normalized exact localization of fixed tensor

Source: Stacks Project, sites-cohomology.tex, Tag 06YU and its preceding construction;
categories.tex, Tags 04VG and 04VK; derived.tex, definition-distinguished-triangle.
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison)

The abbreviations expose the published resolving tensor and comparison, rather than choosing
new resolutions or a new tensor. `NormalizedDescent` packages the conclusions for one side.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Pretriangulated MonoidalCategory

namespace SheafOfModules.FixedTensorLocalization

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The recorded module-sheaf category. Source: Stacks, Modules on Sites, 03DA
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Unbounded complexes. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Complexes := CochainComplex (Modules R) ℤ

/-- The homotopy category. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Homotopy := HomotopyCategory (Modules R) (.up ℤ)

/-- Quotient by chain homotopy. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev quotient := HomotopyCategory.quotient (Modules R) (.up ℤ)

/-- The direct-sum total tensor with its canonical signs. Source: Stacks, Tag 06YM
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev totalTensor :=
  (@curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)).map₂CochainComplex

variable [HasDerivedCategory.{w} (Modules R)]

/-- The chosen-universe derived category. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Derived := DerivedCategory (Modules R)

/-- Homotopy localization. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Q := DerivedCategory.Qh (C := Modules R)

/-- The resolving full subcategory selected by the published descent theorem.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev resolving : ObjectProperty (Homotopy R) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose

/-- The published total tensor on the homotopy category. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev tensorK : Homotopy R × Homotopy R ⥤ Homotopy R :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1.choose

/-- The published tensor on the derived category. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev tensorD := Functor.curry.obj
  (siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R)

/-- The specified natural homotopy comparison. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev chainComparison :
    ((quotient R).prod (quotient R)) ⋙ tensorK R ≅
      Functor.uncurry.obj (totalTensor R) ⋙ quotient R :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.1.some

/-- The specified resolving comparison, with its original naturality in both variables.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev resolvingComparison :
    ((resolving R).ι.prod (resolving R).ι) ⋙ tensorK R ⋙ Q R ≅
      (((resolving R).ι ⋙ Q R).prod ((resolving R).ι ⋙ Q R)) ⋙
        siteDerivedTensorIndependentCoefficients J R :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.2.choose_spec.some

/-- A flat-term K-flat complex as an object of the published resolving class.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
def resolvingObject (A : Complexes R)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    (hAf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (A.X n)) :
    (resolving R).FullSubcategory :=
  ⟨(quotient R).obj A,
    ((site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
      J R).choose_spec.1 _).2 ⟨hA, hAf⟩⟩

/-- Inverse of the image of an inverted quasi-isomorphism, using the stated hypothesis.
Source: Stacks, Categories, Tag 04VK
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
def invertedMapIso (H : Homotopy R ⥤ Homotopy R)
    (hU : (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).IsInvertedBy (H ⋙ Q R))
    {X Y : Homotopy R} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (Modules R) (.up ℤ) f) :
    (Q R).obj (H.obj X) ≅ (Q R).obj (H.obj Y) :=
  @asIso _ _ _ _ ((H ⋙ Q R).map f) (hU f hf)

/-- Explicit shift compatibility of the factorization, with both canonical comparisons
of Q inserted. Source: Stacks, Categories, Tag 04VK; Cohomology on Sites, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
def ShiftCompatible (H : Homotopy R ⥤ Homotopy R) [H.CommShift ℤ]
    (G : Derived R ⥤ Derived R) (s : G.CommShift ℤ)
    (η : H ⋙ Q R ≅ Q R ⋙ G) : Prop :=
  ∀ (n : ℤ) (X : Homotopy R),
    η.hom.app (X⟦n⟧) ≫ G.map (((Q R).commShiftIso n).hom.app X) ≫
      (s.commShiftIso n).hom.app ((Q R).obj X) =
    (Q R).map ((H.commShiftIso n).hom.app X) ≫
      ((Q R).commShiftIso n).hom.app (H.obj X) ≫ (shiftFunctor (Derived R) n).map (η.hom.app X)

/-- Full conclusions on one side: coherent exact descent; unique normalized comparison;
resolution formula; and unique compatible change of factorization. Naturality on arbitrary
derived arrows is part of the natural isomorphisms d and θ. `IsTriangulated` uses mapTriangle,
whose last arrow is G(w) followed by the specified shift comparison, including the connecting
arrow. No boundedness or cohomology-flatness is imposed.
Source: Stacks, Tag 06YU; Categories, Tag 04VK
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
def NormalizedDescent (H : Homotopy R ⥤ Homotopy R) [H.CommShift ℤ]
    (hU : (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).IsInvertedBy (H ⋙ Q R))
    (F : Derived R ⥤ Derived R)
    (c : ∀ P : (resolving R).FullSubcategory,
      (Q R).obj (H.obj P.obj) ≅ F.obj ((Q R).obj P.obj)) : Prop :=
  ∃ (G : Derived R ⥤ Derived R) (s : G.CommShift ℤ),
    G.Additive ∧ G.IsTriangulated ∧
    ∃ η : H ⋙ Q R ≅ Q R ⋙ G,
      ShiftCompatible R H G s η ∧
      (∀ s' : G.CommShift ℤ, ShiftCompatible R H G s' η → s' = s) ∧
      ∃ d : G ≅ F,
        (∀ P : (resolving R).FullSubcategory,
          η.hom.app P.obj ≫ d.hom.app ((Q R).obj P.obj) = (c P).hom) ∧
        (∀ d' : G ≅ F,
          (∀ P : (resolving R).FullSubcategory,
            η.hom.app P.obj ≫ d'.hom.app ((Q R).obj P.obj) = (c P).hom) → d' = d) ∧
        (∀ (P : (resolving R).FullSubcategory) (B : Homotopy R) (f : P.obj ⟶ B)
          (hf : HomotopyCategory.quasiIso (Modules R) (.up ℤ) f),
          η.hom.app B ≫ d.hom.app ((Q R).obj B) =
            (invertedMapIso R H hU f hf).inv ≫ (c P).hom ≫ F.map ((Q R).map f)) ∧
        (∀ (G' : Derived R ⥤ Derived R) (s' : G'.CommShift ℤ)
          (η' : H ⋙ Q R ≅ Q R ⋙ G') (d' : G' ≅ F),
          ShiftCompatible R H G' s' η' →
          (∀ P : (resolving R).FullSubcategory,
            η'.hom.app P.obj ≫ d'.hom.app ((Q R).obj P.obj) = (c P).hom) →
          ∃! θ : G ≅ G',
            (∀ X : Homotopy R, η.hom.app X ≫ θ.hom.app ((Q R).obj X) = η'.hom.app X) ∧
            NatTrans.CommShift θ.hom ℤ ∧
            (∀ M : Derived R, θ.hom.app M ≫ d'.hom.app M = d.hom.app M))

/-- Exact localization of both fixed tensors, with signed shifts and comparisons normalized
on the published resolving class.

Source: Stacks Project, sites-cohomology.tex, Tag 06YU and preceding construction;
categories.tex, Tags 04VG and 04VK; derived.tex, definition-distinguished-triangle
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison).

Proof plan (the node's nine steps):
1. Localize U=QH using lem-weil-pbc-localization-universal-property, giving G and η.
2. Use lem-pur-additive-localization-descent, since Q and H are additive and every derived
   object is isomorphic to QB, to show G additive.
3. Conjugate Q(s_n), the canonical Q shift maps, and η to define shifts after restriction
   along Q. Extend these transformations and their inverses by the localization property.
4. Check zero and addition coherence after restriction: the adjacent η inverses cancel;
   faithfulness gives the laws and uniqueness of the coherent shift structure on G.
5. A distinguished derived triangle is a localized cone triangle up to isomorphism.
   Exactness of H and Q (lem-pur-homotopy-category-triangulated), and the shift square,
   identify its image under G with QH of the cone triangle, including its connecting arrow.
6. The resolving restriction is a localization by lem-weil-pbc-site-derived-tensor-descent.
   Extend c_(A,P) η_P^{-1} and its inverse uniquely to d_L.
7. Repeat in the other variable using the same published comparison's first-variable
   naturality, obtaining the uniquely normalized d_R.
8. Naturality at r:P→B gives e_B QH(r)=T(Qr)c_P; invert QH(r) to obtain the stated formula.
   lem-pc-kflat-resolution supplies unbounded flat-term K-flat resolutions. Each formula
   equals e_B, proving independence, while d's naturality covers every derived arrow.
9. The localization property gives the unique θ with η(θQ)=η'. Restrict the shift and d
   compatibility squares to Q and the resolving class respectively; faithfulness proves
   both globally. No boundedness or flatness of cohomology has been used.
-/
theorem fixed_tensor_localization_comparison
    (A : Complexes R) (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    (hAf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (A.X n))
    [((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)).CommShift ℤ]
    [((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)).CommShift ℤ]
    [((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)).Additive]
    [((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)).Additive]
    [((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)).IsTriangulated]
    [((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)).IsTriangulated]
    (hUL : (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).IsInvertedBy
      (((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)) ⋙ Q R))
    (hUR : (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).IsInvertedBy
      (((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)) ⋙ Q R))
    (hSL : ∀ (n : ℤ) (B : Complexes R),
      ((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)).map
          (((quotient R).commShiftIso n).hom.app B) ≫
        (((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)).commShiftIso n).hom.app
          ((quotient R).obj B) =
      (chainComparison R).hom.app (A, B⟦n⟧) ≫
        (quotient R).map (CochainComplex.mapBifunctorShift₂Iso A B
          (@curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)) n).hom ≫
        ((quotient R).commShiftIso n).hom.app (((totalTensor R).obj A).obj B) ≫
        (shiftFunctor (Homotopy R) n).map ((chainComparison R).inv.app (A, B)))
    (hSR : ∀ (n : ℤ) (B : Complexes R),
      ((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)).map
          (((quotient R).commShiftIso n).hom.app B) ≫
        (((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)).commShiftIso n).hom.app
          ((quotient R).obj B) =
      (chainComparison R).hom.app (B⟦n⟧, A) ≫
        (quotient R).map (CochainComplex.mapBifunctorShift₁Iso B A
          (@curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)) n).hom ≫
        ((quotient R).commShiftIso n).hom.app (((totalTensor R).obj B).obj A) ≫
        (shiftFunctor (Homotopy R) n).map ((chainComparison R).inv.app (B, A))) :
    NormalizedDescent R
      ((Functor.curry.obj (tensorK R)).obj ((quotient R).obj A)) hUL
      ((tensorD R).obj ((Q R).obj ((quotient R).obj A)))
      (fun P ↦ (resolvingComparison R).app (resolvingObject R A hA hAf, P)) ∧
    NormalizedDescent R
      ((Functor.curry.obj (tensorK R)).flip.obj ((quotient R).obj A)) hUR
      ((tensorD R).flip.obj ((Q R).obj ((quotient R).obj A)))
      (fun P ↦ (resolvingComparison R).app (P, resolvingObject R A hA hAf)) := by
  sorry

end SheafOfModules.FixedTensorLocalization
