/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.FilteredTruncationTriangle

/-!
# Graded comparisons for supplied filtered lifts

Source: Varshavsky, Lefschetz--Verdier trace formula, Sections 5.1.3(a),(b),(e)
and Lemma 5.1.4(i)--(iii), pp. 39--41
(blueprint: lem-trf-filtered-functor-graded-comparison).

The family formulation expresses coherence for arbitrary identities and composites,
including a third abelian category. All categories live in a common larger universe;
object, morphism, derived-localization and indexing universes remain independent.
-/

@[expose] public section

set_option autoImplicit false

universe z w v u v' u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.FiniteFilteredDerived

variable {I : Type z} (C : I → Type u) [∀ i : I, Category.{v} (C i)]
  [∀ i : I, Abelian (C i)] [∀ i : I, HasDerivedCategory.{w} (C i)]
  (D : I → Type u') [∀ i : I, Category.{v'} (D i)] [∀ i : I, HasShift (D i) ℤ]
  [∀ i : I, Preadditive (D i)] [∀ i : I, HasZeroObject (D i)]
  [∀ (i : I) (n : ℤ), (shiftFunctor (D i) n).Additive]
  [∀ i : I, Pretriangulated (D i)] [∀ i : I, IsTriangulated (D i)]
  (P : ∀ i : I, Presentation (C := C i) (D := D i))

/-- A supplied exact filtered lift includes its ordinary functor and the specified
forgetful comparison; preservation is required for every finite filtration interval.
Source: Varshavsky 5.1.3(a),(b), covariant unary case
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
structure Lift (i j : I) where
  ordinary : DerivedCategory.Plus (C i) ⥤ DerivedCategory.Plus (C j)
  filtered : D i ⥤ D j
  [ordinaryShift : ordinary.CommShift ℤ]
  [filteredShift : filtered.CommShift ℤ]
  ordinaryExact : ordinary.IsTriangulated
  filteredExact : filtered.IsTriangulated
  interval : ∀ (a b : ℤ) (M : D i),
    Supported (P i) a b M → Supported (P j) a b (filtered.obj M)
  phi : filtered ⋙ (P j).omega ≅ (P i).omega ⋙ ordinary

attribute [instance] Lift.ordinaryShift Lift.filteredShift Lift.ordinaryExact Lift.filteredExact

variable {C D P}

/-- A lift of a supplied transformation is specified by exactly its forgetful square.
No existence of such a lift is assumed or asserted for arbitrary transformations.
Source: Varshavsky 5.1.3(e)
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
def LiftsTransformation {i j : I} (F G : Lift C D P i j)
    (h : F.ordinary ⟶ G.ordinary) (a : F.filtered ⟶ G.filtered) : Prop :=
  ∀ M : D i, (P j).omega.map (a.app M) ≫ G.phi.hom.app M =
    F.phi.hom.app M ≫ h.app ((P i).omega.obj M)

/-- The given lift of the identity uses the identity forgetful comparison.
Source: Varshavsky 5.1.3(b)
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
noncomputable def identityLift (i : I) : Lift C D P i i where
  ordinary := 𝟭 _
  filtered := 𝟭 _
  ordinaryExact := inferInstance
  filteredExact := inferInstance
  interval := fun _ _ _ h ↦ h
  phi := Iso.refl _

/-- Composition uses the specified composite forgetful comparison.
Source: Varshavsky 5.1.3(b),(e)
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
noncomputable def composeLift {i j k : I} (F : Lift C D P i j) (G : Lift C D P j k) :
    Lift C D P i k where
  ordinary := F.ordinary ⋙ G.ordinary
  filtered := F.filtered ⋙ G.filtered
  ordinaryExact := inferInstance
  filteredExact := inferInstance
  interval := fun a b M h ↦ G.interval a b _ (F.interval a b M h)
  phi := (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft F.filtered G.phi ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight F.phi G.ordinary ≪≫
    Functor.associator _ _ _

/-- Graded comparisons, normalized on pure filtration objects, commute with supplied
transformations and both kinds of composition, and detect lifted isomorphisms.
Source: Varshavsky 5.1.3(a),(b),(e), Lemma 5.1.4(i)--(iii)
(blueprint: lem-trf-filtered-functor-graded-comparison).

Proof:
1. For every supplied lift F and integer r use the universal supported truncation
   triangle of lem-trf-filtered-truncation-triangle. Exactness and interval preservation
   identify F(t_ge r M) with t_ge r(F M) and F(t_lt r M) with t_lt r(F M).
   Postcomposition with the inclusion and precomposition with the quotient are the
   two universal Hom bijections, so these comparisons are unique and natural.
2. Put T_p = t_ge p t_lt (p+1). Compose the two comparisons to get
   kappa : F T_p ≅ T_p F. Apply omega to its inverse and then the supplied phi
   at T_p M. Since omega T_p = gr p, this defines theta. On pure degree p
   objects this is the supplied phi through the canonical pure comparisons.
3. Naturality of a supplied lifted transformation for the inclusion and quotient
   makes it commute with both truncation comparisons by the same Hom bijections.
   Therefore it commutes with kappa. Apply omega and the supplied forgetful square
   at T_p M to obtain the displayed theta square.
4. If the ordinary transformation is invertible, this square makes every graded
   component invertible. Each grade of a cone of its filtered component is zero by
   lem-kun-distinguished-cone-zero. A finite filtered complex representing that cone
   has all grades acyclic, so its map to zero is a graded quasi-isomorphism. The
   localization inverts it. The cone-zero criterion makes the filtered component,
   and hence the whole filtered natural transformation, invertible.
5. For identities and composition of transformations the theta square conjugates
   the ordinary transformation; intermediate inverse comparisons cancel. For a
   composite of filtered functors, uniqueness of the supported truncation maps
   identifies its kappa with kappa_G composed with G(kappa_F). The specified
   composite phi gives theta_GF = theta_G followed by G(theta_F). Identity
   filtered functors have identity truncation comparisons, hence identity theta.
-/
theorem filteredFunctorGradedComparison :
    ∃ theta : ∀ {i j : I} (F : Lift C D P i j) (p : ℤ),
      F.filtered ⋙ (P j).gr p ≅ (P i).gr p ⋙ F.ordinary,
    (∀ {i j : I} (F : Lift C D P i j) (p : ℤ) (M : D i)
      (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M))
      (hFM : ∀ q : ℤ, q ≠ p → IsZero (((P j).gr q).obj (F.filtered.obj M))),
      (theta F p).hom.app M =
        ((P j).pureComparison p (F.filtered.obj M) hFM).hom ≫ F.phi.hom.app M ≫
        F.ordinary.map ((P i).pureComparison p M hM).inv) ∧
    (∀ {i j : I} (F G : Lift C D P i j) (h : F.ordinary ⟶ G.ordinary)
      (a : F.filtered ⟶ G.filtered), LiftsTransformation F G h a →
      (∀ (p : ℤ) (M : D i),
        ((P j).gr p).map (a.app M) ≫ (theta G p).hom.app M =
          (theta F p).hom.app M ≫ h.app (((P i).gr p).obj M)) ∧
      (IsIso h → IsIso a)) ∧
    (∀ (i : I) (p : ℤ) (M : D i),
      (theta (identityLift (C := C) (D := D) (P := P) i) p).hom.app M = 𝟙 _) ∧
    (∀ {i j k : I} (F : Lift C D P i j) (G : Lift C D P j k) (p : ℤ) (M : D i),
      (theta (composeLift F G) p).hom.app M =
        (theta G p).hom.app (F.filtered.obj M) ≫
          G.ordinary.map ((theta F p).hom.app M)) ∧
    (∀ {i j : I} (F : Lift C D P i j) (p : ℤ) (M : D i),
      ((P j).gr p).map ((𝟙 F.filtered : F.filtered ⟶ F.filtered).app M) ≫ (theta F p).hom.app M =
        (theta F p).hom.app M ≫ (𝟙 F.ordinary : F.ordinary ⟶ F.ordinary).app (((P i).gr p).obj M)) ∧
    (∀ {i j : I} (F G H : Lift C D P i j)
      (h : F.ordinary ⟶ G.ordinary) (k : G.ordinary ⟶ H.ordinary)
      (a : F.filtered ⟶ G.filtered) (b : G.filtered ⟶ H.filtered),
      LiftsTransformation F G h a → LiftsTransformation G H k b →
      ∀ (p : ℤ) (M : D i),
        ((P j).gr p).map ((a ≫ b).app M) ≫ (theta H p).hom.app M =
          (theta F p).hom.app M ≫ (h ≫ k).app (((P i).gr p).obj M)) := by
  sorry

end CategoryTheory.FiniteFilteredDerived
