/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Canonical localization filtration descent

Source: Varshavsky, *Lefschetz--Verdier trace formula*, Example 5.2.3 and
§5.1.2(a)--(b) (blueprint: lem-trf-localization-filtration-descent).

The statement records the exact open--closed localization sequence and the
canonical two-step filtration on bounded complexes. The filtered target is the localization
of bounded complexes with uniformly finite
filtrations at all graded quasi-isomorphisms (`FiniteFiltered.Derived true`). The
ordinary target is Mathlib's `DerivedCategory.Bounded`. All comparison functors and the
section are conclusions, normalized on bounded complexes and chain maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The coefficient category of modules over the commutative ring `Λ`.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
abbrev LocalizationCoefficients (Λ : Type (u + 1)) [Ring Λ] := ModuleCat.{u + 1} Λ

/-- The abelian category of `Λ`-module sheaves on the small étale site of `X`.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
abbrev LocalizationSheaves (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology (LocalizationCoefficients Λ)

/-- The open localization endofunctor `j_!j^{-1}` on module sheaves.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
noncomputable def localizationOpenStep (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    LocalizationSheaves Λ X ⥤ LocalizationSheaves Λ X :=
  Etale.openImmersionRestriction (LocalizationCoefficients Λ) j ⋙
    Etale.openImmersionLowerShriek (LocalizationCoefficients Λ) j

/-- The closed localization endofunctor `i_*i^{-1}` on module sheaves.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
noncomputable def localizationClosedStep (Λ : Type (u + 1)) [CommRing Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    LocalizationSheaves Λ X ⥤ LocalizationSheaves Λ X :=
  Etale.upperStar (LocalizationCoefficients Λ) i ⋙
    Etale.lowerStar (LocalizationCoefficients Λ) i

/-- Additivity is inherited from restriction and extension by zero.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
instance localizationOpenStep_additive (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (localizationOpenStep Λ j).Additive := by
  dsimp [localizationOpenStep]
  infer_instance

/-- Additivity is inherited from inverse and direct image.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
instance localizationClosedStep_additive (Λ : Type (u + 1)) [CommRing Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (localizationClosedStep Λ i).Additive := by
  dsimp [localizationClosedStep]
  infer_instance

/-- The two step `j_!j^{-1}` operation on cochain complexes.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
noncomputable def localizationOpenStepComplex (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    CochainComplex (LocalizationSheaves Λ X) ℤ ⥤ CochainComplex (LocalizationSheaves Λ X) ℤ :=
  (localizationOpenStep Λ j).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The two step `i_*i^{-1}` operation on cochain complexes.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
noncomputable def localizationClosedStepComplex (Λ : Type (u + 1)) [CommRing Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    CochainComplex (LocalizationSheaves Λ X) ℤ ⥤ CochainComplex (LocalizationSheaves Λ X) ℤ :=
  (localizationClosedStep Λ i).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Bounded complexes in the sheaf category, with both strict degree bounds.
This uses the existing boundedness predicate, with `true`, not its bounded-below variant.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
abbrev LocalizationBoundedComplexes (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (CochainComplex.FiniteFiltered.DegreeBound (LocalizationSheaves Λ X) true)

/-- The inclusion of bounded complexes into all complexes.
Source: Varshavsky, Example 5.2.3 (blueprint: lem-trf-localization-filtration-descent). -/
noncomputable def localizationBoundedInclusion (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    LocalizationBoundedComplexes Λ X ⥤ CochainComplex (LocalizationSheaves Λ X) ℤ :=
  ObjectProperty.ι _

/-- Ordinary quasi-isomorphisms between bounded complexes.
Source: Varshavsky, §5.1.2 (blueprint: lem-trf-localization-filtration-descent). -/
def localizationBoundedQuasiIso (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    MorphismProperty (LocalizationBoundedComplexes Λ X) :=
  fun {_ _} f ↦ QuasiIso f.hom

/-- The entire bounded descent assertion, including its normalization on complexes.
`T` is the canonical filtration functor before localization; `e` identifies its underlying
complex with the input, and the image equation pins its first step to the actual counit.
`q` lands in Mathlib's bounded derived category and is normalized to `DerivedCategory.Q`.
The filtered target is the concrete localization `FiniteFiltered.Derived true`.
Every forgetful and graded functor is normalized on chain maps by a natural isomorphism.
No presentation, target category, triangulation, or arbitrary comparison map is assumed.
Source: Varshavsky, Example 5.2.3 and §5.1.2(a)--(b)
(blueprint: lem-trf-localization-filtration-descent). -/
def LocalizationFiltrationDescentData
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [HasDerivedCategory.{u + 2} (LocalizationSheaves Λ X)] : Prop :=
  ∃ (T : LocalizationBoundedComplexes Λ X ⥤
      CochainComplex.FiniteFiltered.Complex (LocalizationSheaves Λ X) true)
    (e : T ⋙ CochainComplex.FiniteFiltered.forget true ≅ localizationBoundedInclusion Λ X),
    (∀ B : LocalizationBoundedComplexes Λ X,
      (T.obj B).obj.filtration.F 0 = ⊤ ∧ (T.obj B).obj.filtration.F 2 = ⊥ ∧
      ∀ n : ℤ,
        imageSubobject (((T.obj B).obj.filtration.F 1).arrow.f n ≫ (e.app B).hom.f n) =
          imageSubobject ((Etale.openImmersionLowerShriekAdjunction
            (LocalizationCoefficients Λ) j).counit.app (B.obj.X n))) ∧
    Nonempty (T ⋙ CochainComplex.FiniteFiltered.graded true 0 ≅
      localizationBoundedInclusion Λ X ⋙ localizationClosedStepComplex Λ i) ∧
    Nonempty (T ⋙ CochainComplex.FiniteFiltered.graded true 1 ≅
      localizationBoundedInclusion Λ X ⋙ localizationOpenStepComplex Λ j) ∧
    (∀ (p : ℤ) (B : LocalizationBoundedComplexes Λ X), p ≠ 0 → p ≠ 1 →
      IsZero ((CochainComplex.FiniteFiltered.graded true p).obj (T.obj B))) ∧
    (∀ {B B' : LocalizationBoundedComplexes Λ X} (f : B ⟶ B'),
      QuasiIso f.hom → CochainComplex.FiniteFiltered.quasiIso true (T.map f)) ∧
    ∃ (q : LocalizationBoundedComplexes Λ X ⥤
        _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X))
      (a : q ⋙ _root_.DerivedCategory.Bounded.ι ≅
        localizationBoundedInclusion Λ X ⋙ _root_.DerivedCategory.Q),
      q.IsLocalization (localizationBoundedQuasiIso Λ X) ∧
      ∃ (omega : CochainComplex.FiniteFiltered.Derived (A := LocalizationSheaves Λ X) true ⥤
          _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X))
        (gr : ℤ → CochainComplex.FiniteFiltered.Derived
          (A := LocalizationSheaves Λ X) true ⥤
            _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X))
        (b : CochainComplex.FiniteFiltered.Q true ⋙ omega ⋙
          _root_.DerivedCategory.Bounded.ι ≅
            CochainComplex.FiniteFiltered.forget true ⋙ _root_.DerivedCategory.Q),
        (∀ p : ℤ, Nonempty (CochainComplex.FiniteFiltered.Q true ⋙ gr p ⋙
          _root_.DerivedCategory.Bounded.ι ≅
            CochainComplex.FiniteFiltered.graded true p ⋙ _root_.DerivedCategory.Q)) ∧
        ∃ (S : _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X) ⥤
            CochainComplex.FiniteFiltered.Derived (A := LocalizationSheaves Λ X) true)
          (d : q ⋙ S ≅ T ⋙ CochainComplex.FiniteFiltered.Q true)
          (sectionIso : S ⋙ omega ≅ 𝟭 (_root_.DerivedCategory.Bounded
            (LocalizationSheaves Λ X)))
          (closedD openD : _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X) ⥤
            _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X)),
          (∀ B : LocalizationBoundedComplexes Λ X,
            _root_.DerivedCategory.Bounded.ι.map (sectionIso.app (q.obj B)).hom ≫
                (a.app B).hom =
              (omega ⋙ _root_.DerivedCategory.Bounded.ι).map (d.app B).hom ≫
                (b.app (T.obj B)).hom ≫ _root_.DerivedCategory.Q.map (e.app B).hom) ∧
          Nonempty (q ⋙ closedD ⋙ _root_.DerivedCategory.Bounded.ι ≅
            localizationBoundedInclusion Λ X ⋙ localizationClosedStepComplex Λ i ⋙
              _root_.DerivedCategory.Q) ∧
          Nonempty (q ⋙ openD ⋙ _root_.DerivedCategory.Bounded.ι ≅
            localizationBoundedInclusion Λ X ⋙ localizationOpenStepComplex Λ j ⋙
              _root_.DerivedCategory.Q) ∧
          Nonempty (S ⋙ gr 0 ≅ closedD) ∧ Nonempty (S ⋙ gr 1 ≅ openD) ∧
          (∀ (p : ℤ) (K : _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X)),
            p ≠ 0 → p ≠ 1 → IsZero
              (_root_.DerivedCategory.Bounded.ι.obj ((gr p).obj (S.obj K)))) ∧
          (∀ (K L : _root_.DerivedCategory.Bounded (LocalizationSheaves Λ X)) (f : K ≅ L),
            ∃ f' : S.obj K ≅ S.obj L, f'.hom = S.map f.hom ∧
              omega.map f'.hom ≫ (sectionIso.app L).hom =
                (sectionIso.app K).hom ≫ f.hom)

/-- The canonical localization filtration descends from bounded complexes to the
bounded filtered derived localization, giving a section over the bounded derived category.
The exactness assumptions concern the four ordinary sheaf functors. The degreewise
short exact sequence is required only for bounded complexes.

Source: Varshavsky, Example 5.2.3 and §5.1.2(a)--(b).

Proof, following the four steps of the node:
1. The counit `j_!j^{-1}B → B` is natural and degreewise monic by `hdegree`. Its images
   form a subcomplex. Set `F^p=B` for `p ≤ 0`, `F^1` equal to this image, and `F^p=0`
   for `2 ≤ p`. Both degree bounds of `B` remain valid for every step and quotient.
   The cokernel is naturally `i_*i^{-1}B` by the specified localization sequence.
2. Naturality of the counit gives the filtered functor `T`. For an exact additive
   functor `E`, preservation of kernels, images and cokernels gives
   `H^n(EB) ≅ E(H^n B)` naturally. Apply this to the composites `j_!j^{-1}` and
   `i_*i^{-1}` using the eight exactness hypotheses. The grade-0 and grade-1 maps
   are therefore quasi-isomorphisms whenever the underlying map is one; other
   grades vanish. This uses the recorded filtration and graded-subquotient APIs.
3. For an arbitrary graded quasi-isomorphism `w`, filter its cone componentwise.
   Each grade is the cone of `gr^p(w)`, acyclic by
   `lem-pur-quasi-iso-cone-acyclic`. From a common finite filtration bound, descend
   by induction using `lem-weil-pbc-complex-ses-homology-long-exact` to show that
   the entire cone is acyclic. Thus forgetting inverts every graded quasi-isomorphism.
   `lem-weil-pbc-localization-universal-property` gives `omega`, the graded functors
   and the descended `S`, on the concrete bounded localization. Bounded complexes
   localize to Mathlib's bounded derived category. The underlying identity on
   complexes descends to `sectionIso`, with the displayed normalization equation.
4. Apply `S.mapIso` to a specified derived isomorphism. Naturality of `sectionIso`
   gives the equation identifying its underlying map. The quotient and open-step
   natural isomorphisms of Step 1 descend by the same universal property, giving
   `S ⋙ gr 0 ≅ closedD`, `S ⋙ gr 1 ≅ openD`, and vanishing of all other grades.
   Their normalizations on bounded chain maps identify `closedD` and `openD` with
   the ordinary exact termwise endofunctors. Thus representative independence is
   relative to specified derived identifications, not uniqueness for unmarked objects.
(blueprint: lem-trf-localization-filtration-descent). -/
theorem localization_filtration_descent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hcomplement : Set.range (i : Z → X) = (Set.range (j : U → X))ᶜ)
    [HasDerivedCategory.{u + 2} (LocalizationSheaves Λ X)]
    (hJinvL : PreservesFiniteLimits
      (Etale.openImmersionRestriction (LocalizationCoefficients Λ) j))
    (hJinvC : PreservesFiniteColimits
      (Etale.openImmersionRestriction (LocalizationCoefficients Λ) j))
    (hIL : PreservesFiniteLimits
      (Etale.upperStar (LocalizationCoefficients Λ) i))
    (hIC : PreservesFiniteColimits
      (Etale.upperStar (LocalizationCoefficients Λ) i))
    (hJL : PreservesFiniteLimits (Etale.openImmersionLowerShriek
      (LocalizationCoefficients Λ) j))
    (hJC : PreservesFiniteColimits (Etale.openImmersionLowerShriek
      (LocalizationCoefficients Λ) j))
    (hIstarL : PreservesFiniteLimits
      (Etale.lowerStar (LocalizationCoefficients Λ) i))
    (hIstarC : PreservesFiniteColimits
      (Etale.lowerStar (LocalizationCoefficients Λ) i))
    (hdegree : ∀ (B : LocalizationBoundedComplexes Λ X) (n : ℤ),
      ∃ hzero :
          ((Etale.openImmersionLowerShriekAdjunction
            (LocalizationCoefficients Λ) j).counit.app (B.obj.X n)) ≫
            (Etale.upperStarLowerStarAdjunction
              (LocalizationCoefficients Λ) i).unit.app (B.obj.X n) = 0,
        (ShortComplex.mk
          ((Etale.openImmersionLowerShriekAdjunction
            (LocalizationCoefficients Λ) j).counit.app (B.obj.X n))
          ((Etale.upperStarLowerStarAdjunction
            (LocalizationCoefficients Λ) i).unit.app (B.obj.X n)) hzero).ShortExact)
    : LocalizationFiltrationDescentData Λ j i := by
  sorry

end AlgebraicGeometry.Etale
