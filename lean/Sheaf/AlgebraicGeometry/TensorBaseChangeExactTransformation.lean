/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.Algebra.Homology.DerivedTensorShiftDescent

/-! # Exactness and shifts of tensor base change

Source: Stacks Project, Tag 0F1N, and blueprint main-20261015,
sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1n.proof.md, paragraph 1
(blueprint: lem-kun-tensor-base-change-exact-transformation).

The map is the existing `tensorBaseChangeMap`, with its first input pulled back along p.
The four functors below are its source and target with either input fixed. Their shifts
are the composite canonical shifts: exact termwise inverse image, derived direct image,
and signed total tensor. The notation L for inverse image is identified with exact
termwise inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`; its shift structure
is transported along exactly this isomorphism. No invertibility of the mate is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X X' S' T Y : Scheme.{u}}

/-- A(E,F) with F fixed, using the existing unbounded tensor.
Source: Stacks 0F1N, proof paragraph 1
(blueprint: lem-kun-tensor-base-change-exact-transformation). -/
abbrev tensorBaseChangeSourceLeft (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S')
    (F : DerivedCategoryModule Λ T) :
    DerivedCategoryModule Λ X ⥤ DerivedCategoryModule Λ X' :=
  L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) X').flip.obj
      (L((f')^*[ModuleCat.{u + 1} Λ]).obj (R((g)_*[ModuleCat.{u + 1} Λ]).obj F))

/-- A(E,F) with E fixed.
Source: Stacks 0F1N, proof paragraph 1
(blueprint: lem-kun-tensor-base-change-exact-transformation). -/
abbrev tensorBaseChangeSourceRight (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S')
    (E : DerivedCategoryModule Λ X) :
    DerivedCategoryModule Λ T ⥤ DerivedCategoryModule Λ X' :=
  R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ L((f')^*[ModuleCat.{u + 1} Λ]) ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) X').obj
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj E)

/-- B(E,F) with F fixed.
Source: Stacks 0F1N, proof paragraph 1
(blueprint: lem-kun-tensor-base-change-exact-transformation). -/
abbrev tensorBaseChangeTargetLeft (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (F : DerivedCategoryModule Λ T) :
    DerivedCategoryModule Λ X ⥤ DerivedCategoryModule Λ X' :=
  L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj
      (L((e)^*[ModuleCat.{u + 1} Λ]).obj F) ⋙ R((h)_*[ModuleCat.{u + 1} Λ])

/-- B(E,F) with E fixed.
Source: Stacks 0F1N, proof paragraph 1
(blueprint: lem-kun-tensor-base-change-exact-transformation). -/
abbrev tensorBaseChangeTargetRight (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (E : DerivedCategoryModule Λ X) :
    DerivedCategoryModule Λ T ⥤ DerivedCategoryModule Λ X' :=
  L((e)^*[ModuleCat.{u + 1} Λ]) ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
      (L((h)^*[ModuleCat.{u + 1} Λ]).obj (L((p)^*[ModuleCat.{u + 1} Λ]).obj E)) ⋙
        R((h)_*[ModuleCat.{u + 1} Λ])

/-- The specified tensor base-change counit mate is separately exact, natural in both
inputs, and compatible with the canonical integer shifts in either input.
Source: Stacks 0F1N, proof paragraph 1
(blueprint: lem-kun-tensor-base-change-exact-transformation).

Proof:
1. `prop-weil-pbc-inverse-image-modules-exact` and
   `lem-weil-pbc-exact-functor-derived-factorization` identify inverse image with the
   exact termwise derived functor. `lem-pc-right-derived-functor-triangulated` supplies
   exactness of the unbounded K-injective direct images; `lem-kun-derived-tensor-triangulated`
   supplies separate exactness of tensor. Compose these by
   `lem-weil-pbc-triangulated-functor-composite` for the four functors displayed above.
2. `lem-weil-pbc-pullback-tensor-canonical-shift-unit`, under the exact module pullback
   identification, gives both shift squares for the normalized inverse tensorator.
   Its normalization on flat-term K-flat representatives is the localization of the
   ordinary tensor comparison, hence agrees with `lem-kun-inverse-image-monoidal`.
3. The square comparison of `def-kun-unbounded-exchange` is descended termwise from
   inverse-image composition. On a shifted complex its degree r component is the
   ordinary component in degree r+m, so it commutes with the identity termwise shift
   maps for every integer m. Naturality and equality descend by clauses (2) and (3) of
   `lem-weil-pbc-localization-universal-property`, with the factorization comparisons.
4. `lem-sp-canonical-right-derived-adjunction-shift` gives shift compatibility of the
   units and counits for the prescribed termwise/K-injective derived adjunctions.
   `lem-weil-pbc-derived-tensor-shift-descent` gives naturality of the tensor shift in
   arbitrary derived morphisms of the other factor. Thus tensorator, square comparison
   and pulled-back counit compose to a natural beta : h inverse image A -> D with
   d beta_shift = beta[m] l L(a), for either varying input.
5. The actual mate is alpha = R(beta) eta. Naturality follows from that of beta and eta.
   Write r for the right-derived shift. The composite target shift is r R(d).
   Substituting step 4 and using naturality of eta and r reduces its shift square to
   r R(l) eta_shift = eta[m], the unit equation from the canonical derived-adjunction
   shift lemma. This gives both equations below, for every m, with the fixed shifts.
-/
theorem tensorBaseChange_exact_natural_shift
    (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (sq : IsPullback h e f' g) :
    (∀ F : DerivedCategoryModule Λ T,
      (tensorBaseChangeSourceLeft Λ p f' g F).IsTriangulated ∧
      (tensorBaseChangeTargetLeft Λ p h e F).IsTriangulated) ∧
    (∀ E : DerivedCategoryModule Λ X,
      (tensorBaseChangeSourceRight Λ p f' g E).IsTriangulated ∧
      (tensorBaseChangeTargetRight Λ p h e E).IsTriangulated) ∧
    (∀ (E E' : DerivedCategoryModule Λ X) (F F' : DerivedCategoryModule Λ T)
      (φ : E ⟶ E') (ψ : F ⟶ F'),
      (tensorBaseChangeSourceLeft Λ p f' g F).map φ ≫
          (tensorBaseChangeSourceRight Λ p f' g E').map ψ ≫
            tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq.w
              (L((p)^*[ModuleCat.{u + 1} Λ]).obj E') F' =
        tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq.w
            (L((p)^*[ModuleCat.{u + 1} Λ]).obj E) F ≫
          (tensorBaseChangeTargetLeft Λ p h e F).map φ ≫
            (tensorBaseChangeTargetRight Λ p h e E').map ψ) ∧
    (∀ (m : ℤ) (E : DerivedCategoryModule Λ X) (F : DerivedCategoryModule Λ T),
      tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq.w
          (L((p)^*[ModuleCat.{u + 1} Λ]).obj (E⟦m⟧)) F ≫
          ((tensorBaseChangeTargetLeft Λ p h e F).commShiftIso m).hom.app E =
        ((tensorBaseChangeSourceLeft Λ p f' g F).commShiftIso m).hom.app E ≫
          (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq.w
            (L((p)^*[ModuleCat.{u + 1} Λ]).obj E) F)⟦m⟧') ∧
    (∀ (m : ℤ) (E : DerivedCategoryModule Λ X) (F : DerivedCategoryModule Λ T),
      tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq.w
          (L((p)^*[ModuleCat.{u + 1} Λ]).obj E) (F⟦m⟧) ≫
          ((tensorBaseChangeTargetRight Λ p h e E).commShiftIso m).hom.app F =
        ((tensorBaseChangeSourceRight Λ p f' g E).commShiftIso m).hom.app F ≫
          (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq.w
            (L((p)^*[ModuleCat.{u + 1} Λ]).obj E) F)⟦m⟧') := by
  sorry

end AlgebraicGeometry.Etale
