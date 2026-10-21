/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleAffineLinePullbackFull
import Sheaf.AlgebraicGeometry.EtaleSheafHomFamilyGluing
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-! # Normalized descent of shifted lines on the ordinary etale affine line

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
opening paragraph and Gluing (blueprint: lem-trf-etale-shifted-line-normalized-descent).

All pullbacks are the existing ordinary constant-coefficient etale inverse images.
Their total left derived functors agree canonically with the termwise exact functors.
The helper isomorphisms below only compose their prescribed compositors. In particular,
no comparison map or base-change identification is supplied as extra input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.AffineLineNormalizedDescent

/-- The canonical comparison q* a* C ≅ a_T* b* C for the affine-line base-change square.
Source: sk-thm-dnc, Gluing, base change to an etale cover
(blueprint: lem-trf-etale-shifted-line-normalized-descent). -/
def lineBaseChange (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}}
    (b : T ⟶ S) (C : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) b
    (AffineSpace.map (ULift.{u} (Fin 1)) b ≫ AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.map_over b)).app C

/-- Normalization at the unit section, using the specified section compositor.
Source: sk-thm-dnc, Gluing, identity at t=1
(blueprint: lem-trf-etale-shifted-line-normalized-descent). -/
def Normalized (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S)}
    {C : DerivedCategoryModule A S}
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (κ : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) : Prop :=
  (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map κ.hom ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app C = θ.hom

/-- Local normalization: the local comparison evaluated at one is b* theta.
The existing sectionRestrictionIso includes both the section-square compositor and
cancellation of a_T* along its section, so equality to the identity expresses precisely
this normalization, without choosing identifications.
Source: sk-thm-dnc, Gluing (blueprint: lem-trf-etale-shifted-line-normalized-descent). -/
def LocallyNormalized (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}} (b : T ⟶ S)
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S)}
    {C : DerivedCategoryModule A S}
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (localIso : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C)) : Prop :=
  sectionRestrictionIso (ModuleCat.{u + 1} A) b
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace.oneSection_comp_map b)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T) θ localIso = Iso.refl _

/-- Restrict a local comparison to a further object, identifying both endpoints by
inverse-image compositors. This is used on the actual fibre-product overlaps.
Source: sk-thm-dnc, Gluing (blueprint: lem-trf-etale-shifted-line-normalized-descent). -/
def comparisonRestriction (A : Type (u + 1)) [CommRing A]
    {W U X : Scheme.{u}} (f : U ⟶ X) (g : W ⟶ U) (h : W ⟶ X) (hh : h = g ≫ f)
    {F G : DerivedCategoryModule A X}
    (e : (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj G) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj G :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f h hh).app F ≪≫
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.mapIso e ≪≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f h hh).app G).symm

/-- Section rigidity for the pullback of any locally constant free rank-one module sheaf.
Source: sk-thm-dnc, Gluing, rigidity of the ratio; Stacks 0A3H
(blueprint: lem-trf-etale-shifted-line-normalized-descent).
Proof: Step 1 applies etale_a1_pullback_full to lift u to a sheaf endomorphism b of L.
Apply inverse image along the unit section and conjugate by upperStarComp and upperStarId.
The section identity shows b=1, so u=a*(1)=1. No nonempty, reducedness, or nonzero-ring
hypothesis is used; in fact the proof does not need local constancy. -/
theorem sheaf_rigidity (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u})
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : Scheme.IsLisseRankOneSheaf L)
    (v : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj L ≅
      (upperStar (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj L)
    (hv : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).map v.hom = 𝟙 _) :
    v = Iso.refl _ := by
  sorry

/-- Normalized local comparisons of shifted ordinary-etale lines agree, as do their
inverses, and descend to a globally normalized isomorphism. Global uniqueness quantifies
over all normalized isomorphisms. The last clause gives independence on every etale
base change, hence independence of the entire cover and all normalized choices.
Source: sk-thm-dnc.proof.md, opening paragraph and Gluing
(blueprint: lem-trf-etale-shifted-line-normalized-descent).
Proof: Step 1 is sheaf_rigidity, by affine-line fullness (Stacks 0A3H). Step 2 fixes
F[-m]=P[0] and C[-m]=Q[0]. Exact inverse image commutes with shifts and single complexes
(015F); the fully faithful single functor (06XS) identifies maps, inverses and their
compositions with sheaf maps, compatibly with every compositor. Step 3 uses affine-space
base change to identify X_i and all overlaps with affine lines over the corresponding
bases. Etale covering-base-change makes the X_i cover X, including empty covers.
Step 4 takes the ratio of two local comparisons on an overlap; normalization makes
its value at one the identity, so Step 1 makes the ratio the identity. Inverses agree
as well. Step 5 applies existsUnique_etaleSheafHom_of_family to glue the maps and
separately their inverses; uniqueness identifies both composites with identities.
Return to derived objects by Step 2. Step 6 tests the normalization on the base cover.
The ratio of any two normalized global comparisons is the identity by Step 1, without
assuming prescribed restrictions. Apply that argument over every etale base to identify
any other normalized local comparison with the restriction of the global one. This
includes empty and nonreduced bases and the zero ring. -/
theorem normalized_descent (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u})
    (m : ℤ) (C : DerivedCategoryModule A S)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S))
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Scheme.IsLisseRankOneSheaf Q ∧
        Nonempty (C⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    (hF : ∃ P : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
        (ModuleCat.{u + 1} A), Scheme.IsLisseRankOneSheaf P ∧
        Nonempty (F⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj P))
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (cover : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (localIso : ∀ i : cover.I₀,
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) (cover.X i) ↘ cover.X i)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) (cover.f i)).leftDerivedFunctor.obj C))
    (hlocal : ∀ i : cover.I₀, LocallyNormalized A (cover.f i) θ (localIso i)) :
    (∀ i j : cover.I₀,
      comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
        (pullback.fst (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ rfl
        (localIso i ≪≫ (lineBaseChange A (cover.f i) C).symm) =
      comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))
        (pullback.snd (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ pullback.condition
        (localIso j ≪≫ (lineBaseChange A (cover.f j) C).symm)) ∧
    (∀ i j : cover.I₀,
      (comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
        (pullback.fst (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ rfl
        (localIso i ≪≫ (lineBaseChange A (cover.f i) C).symm)).inv =
      (comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))
        (pullback.snd (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ pullback.condition
        (localIso j ≪≫ (lineBaseChange A (cover.f j) C).symm)).inv) ∧
    ∃ κ : F ≅ (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C,
      Normalized A S θ κ ∧
      (∀ i : cover.I₀,
        (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))).leftDerivedFunctor.mapIso κ ≪≫
          lineBaseChange A (cover.f i) C = localIso i) ∧
      (∀ κ' : F ≅ (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C,
        Normalized A S θ κ' → κ' = κ) ∧
      (∀ (T : Scheme.{u}) (b : T ⟶ S), Etale b →
        ∀ μ : (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj F ≅
          (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
              ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C),
        LocallyNormalized A b θ μ →
          μ = (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.mapIso κ ≪≫
              lineBaseChange A b C) := by
  sorry

end AlgebraicGeometry.Etale.AffineLineNormalizedDescent
