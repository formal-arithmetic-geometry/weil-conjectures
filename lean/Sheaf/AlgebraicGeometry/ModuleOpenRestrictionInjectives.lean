/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Exact restriction of module sheaves and injective objects

Source: Stacks Project, Cohomology, Tags 01E1 and 02N5; Modules, Tags 01AJ and 01AK
(blueprint: lem-weil-pbc-module-open-restriction-injectives).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to an open `U` (`SheafOfModules.overFunctor`, modules over `𝒪_X.over U`)
is additive and exact, preserves injective objects, and sends an injective resolution
to its termwise restriction with restricted augmentation. Direct image along the
inclusion (`SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)`, sections
`𝒥(W ∩ U)`, Mathlib's right adjoint of restriction) also preserves injective objects.

Source: Stacks Project, Cohomology, Tags 01E1 and 02N5; Modules, Tags 01AJ and 01AK
(blueprint: lem-weil-pbc-module-open-restriction-injectives).

Proof: (1) Restriction is sectionwise additive by `def-weil-sheaf-of-modules-category`.
Its stalk at a point of the open is naturally the original stalk: restrict a representative
section to its intersection with the open; equality of germs is unchanged. Thus exactness
follows from `lem-weil-pbc-module-stalk-exact` and `def-weil-pbc-exact-sequence`.
(2) By `lem-weil-pbc-module-extension-by-zero-adjunction`, extension by zero is left adjoint
to restriction. Its stalks are the original stalks inside the open and zero outside, so it
is exact. Apply `lem-sp-right-adjoint-preserves-injectives`.
(3) By `lem-weil-pbc-module-restriction-open-immersion-colimits`, restriction is left adjoint
to direct image; apply the same injectivity lemma using (1).
Finally, (1) preserves exactness of the augmented resolution and (2) preserves injectivity
of every term. Restriction preserves zero terms, so this is an injective resolution as in
`def-sp-injective-resolutions`; enough injectives are supplied by
`lem-weil-pbc-scheme-modules-enough-injectives`. -/
theorem module_open_restriction_injectives (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).Additive ∧
    (∀ S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf), S.Exact →
      (S.map (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)).Exact) ∧
    (∀ I : SheafOfModules.{u} X.ringCatSheaf, Injective I → Injective (I.over U)) ∧
    (∀ J : SheafOfModules.{u} (X.ringCatSheaf.over U), Injective J →
      Injective ((SheafOfModules.pushforward.{u}
        (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U)).obj J)) ∧
    (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (I : InjectiveResolution F),
      ∃ (J : InjectiveResolution (F.over U))
        (h : J.cocomplex = ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex),
        J.ι.f 0 ≫ eqToHom (congrArg (fun K ↦ K.X 0) h) = (I.ι.f 0).over U) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
