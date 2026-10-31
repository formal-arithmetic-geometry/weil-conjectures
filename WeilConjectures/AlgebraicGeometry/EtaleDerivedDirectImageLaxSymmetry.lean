/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # The canonical symmetric tensor structure on ordinary derived direct image

Source: the current blueprint, `sec-smooth-purity/sk-lem-sp-tower/`
`lem-weil-delta-proper-pushforward.proof.md`, paragraphs 2 and 3; Stacks Tag 07A4.
(blueprint: lem-pur-etale-derived-direct-image-lax-symmetry).

The tensorator and unit are actual adjunction mates. The existence assertion below pins
both coherent structures to these maps and the existing pullback comparisons. The symmetry
is the signed symmetry descended from cochain complexes, not an arbitrary symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The binary mate of the canonical pullback comparison followed by the tensor of counits.
Source: the current blueprint, `lem-weil-delta-proper-pushforward.proof.md`, paragraph 2;
Mathlib `Adjunction.rightAdjointLaxMonoidal`, tensorator formula.
(blueprint: lem-pur-etale-derived-direct-image-lax-symmetry). -/
noncomputable def derivedDirectImageTensorator (M N : DerivedCategoryModule A X) :
    R((f)_*[ModuleCat A]).obj M ⊗ R((f)_*[ModuleCat A]).obj N ⟶
      R((f)_*[ModuleCat A]).obj (M ⊗ N) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat A) f
      (R((f)_*[ModuleCat A]).obj M) (R((f)_*[ModuleCat A]).obj N)).hom ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).counit.app M ⊗ₘ
          (derivedUpperStarLowerStarAdjunction (ModuleCat A) f).counit.app N))

/-- The unit mate of the degree-zero constant-coefficient pullback identification.
Source: Stacks Tag 07A4 and the current blueprint,
`lem-weil-delta-proper-pushforward.proof.md`, paragraph 2.
(blueprint: lem-pur-etale-derived-direct-image-lax-symmetry). -/
noncomputable def derivedDirectImageTensorUnit :
    𝟙_ (DerivedCategoryModule A Y) ⟶
      R((f)_*[ModuleCat A]).obj (𝟙_ (DerivedCategoryModule A X)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv _ _
    (leftDerivedUpperStarUnitIso (ModuleCat A) f).hom

/-- The specified inverse image is strong symmetric monoidal, and its counit mates make
ordinary unbounded derived direct image lax symmetric monoidal. Its projection morphism is
exactly the specified tensorator composed with the adjunction unit.
Source: the current blueprint, `lem-weil-delta-proper-pushforward.proof.md`, paragraphs 2--3;
Stacks Tag 07A4.
(blueprint: lem-pur-etale-derived-direct-image-lax-symmetry).

Proof:
1. `prop-weil-pbc-inverse-image-modules-exact` identifies constant-coefficient module pullback
   with exact inverse image. `lem-weil-pbc-exact-functor-derived-functor` identifies its
   termwise localization with the left derived functor. The K-flat construction in
   `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is the canonical comparison of
   `lem-kun-inverse-image-monoidal`, for all unbounded complexes.
2. On K-flat representatives the comparison preserves reassociation and the signed swap
   by `lem-pur-cochain-pullback-tensor-coherence`. The representative normalizations of
   `lem-sf-ringed-derived-closed-symmetric-monoidal` and the finite-variable descent of
   `lem-pur-derived-tensor-additive-constraints` give associativity and the symmetry square
   on all derived objects.
3. The unit comparison is the degree-zero pullback of the coefficient sheaf.
   `lem-weil-pbc-pullback-tensor-canonical-shift-unit` supplies both action-unitor equations.
   Together with invertibility of the comparisons, this gives the pinned monoidal structure.
4. Apply `lem-sfb-monoidal-adjunction-mates`. Its binary mate is the comparison followed by
   the tensor of the two counits, and its unit is the mate of the constant-unit comparison.
   Thus its lax structure maps are precisely the two definitions above; it supplies their
   naturality, associativity and both unit diagrams.
5. Transpose the two sides of the direct-image symmetry equation. Pullback compatibility
   with the signed symmetry and naturality of that symmetry identify their transposes.
   Injectivity of the adjunction bijection gives the asserted equality.
6. Transpose the final composite. Naturality of the pullback comparison moves the unit
   through its second input. The triangle identity cancels the second counit against the
   pulled-back unit. The resulting transpose is the comparison followed by the first
   counit tensored with the identity, exactly `def-kun-projection-formula-map`. -/
theorem etaleDerivedDirectImage_laxSymmetry :
    ∃ sF : (L((f)^*[ModuleCat A])).Monoidal,
      (∀ P Q : DerivedCategoryModule A Y,
        @Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ sF.toOplaxMonoidal P Q =
          (leftDerivedUpperStarTensorIso (ModuleCat A) f P Q).hom) ∧
      (@Functor.OplaxMonoidal.η _ _ _ _ _ _ _ sF.toOplaxMonoidal =
        (leftDerivedUpperStarUnitIso (ModuleCat A) f).hom) ∧
      (∀ P Q : DerivedCategoryModule A Y,
        L((f)^*[ModuleCat A]).map
            (((derivedTensorSymmetry (ModuleCat A) Y).hom.app P).app Q) ≫
          (leftDerivedUpperStarTensorIso (ModuleCat A) f Q P).hom =
        (leftDerivedUpperStarTensorIso (ModuleCat A) f P Q).hom ≫
          (((derivedTensorSymmetry (ModuleCat A) X).hom.app
            (L((f)^*[ModuleCat A]).obj P)).app (L((f)^*[ModuleCat A]).obj Q))) ∧
      ∃ sG : (R((f)_*[ModuleCat A])).LaxMonoidal,
        (∀ M N : DerivedCategoryModule A X,
          @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ sG M N =
            derivedDirectImageTensorator A f M N) ∧
        (@Functor.LaxMonoidal.ε _ _ _ _ _ _ _ sG = derivedDirectImageTensorUnit A f) ∧
        (∀ M N : DerivedCategoryModule A X,
          derivedDirectImageTensorator A f M N ≫ R((f)_*[ModuleCat A]).map
              (((derivedTensorSymmetry (ModuleCat A) X).hom.app M).app N) =
            (((derivedTensorSymmetry (ModuleCat A) Y).hom.app
              (R((f)_*[ModuleCat A]).obj M)).app (R((f)_*[ModuleCat A]).obj N)) ≫
              derivedDirectImageTensorator A f N M) ∧
        (∀ (M : DerivedCategoryModule A X) (T : DerivedCategoryModule A Y),
          R((f)_*[ModuleCat A]).obj M ◁
              (derivedUpperStarLowerStarAdjunction (ModuleCat A) f).unit.app T ≫
            derivedDirectImageTensorator A f M (L((f)^*[ModuleCat A]).obj T) =
              ((rightDerivedLowerStarProjectionMap (ModuleCat A) f).app M).app T) := by
  sorry

end AlgebraicGeometry.Etale
