/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.SmoothPurity.QbarFiniteDescent
import WeilConjectures.AlgebraicGeometry.LocalizingCompactificationCoherence
import WeilConjectures.Algebra.Homology.OrdinaryLineDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Smooth purity with native condensed algebraic-closure coefficients

Source: latest blueprint, sec-smooth-purity/sk-thm-sp-qbar/_section.md and
sk-thm-sp-qbar.proof.md (blueprint: sk-thm-sp-qbar).

The coefficients are the finite-subextension-valued condensed algebraic closure,
pulled back from the point. Both categories are full bounded constructible
subcategories of the ordinary unbounded derived categories of internal modules.
Membership proofs are conclusions, so no preservation assumption is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The exact coefficient inverse image, followed by the recorded condensed Tate
line in degree zero and the cohomological shift [2d]. Its object value is precisely
`spInternalComplexTwist` of the inverse image, shifted by twice the dimension.
Source: latest blueprint, sk-thm-sp-qbar, displayed right adjoint, using the signed
line of sk-def-sp-tate-twist (blueprint: sk-thm-sp-qbar). -/
def nativeQbarPurityRight (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X)) :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f).mapDerivedCategory ⋙
    tensorRight ((DerivedCategory.singleFunctor _ 0).obj
      (spInternalSignedTwist X (condensedRingObj (Profinite.padicAlgClRingObj ell) X)
        (spQbarTwist X ell) (d : ℤ))) ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- Smooth purity: for any compactification the compact-support composite is left
adjoint to exact inverse image followed by (d)[2d] on bounded constructible complexes.
The two existential witnesses assert that the specified ambient functors preserve
these full subcategories; `lift` only bundles those very same objects and arrows.
Source: latest blueprint, sk-thm-sp-qbar, order 3326 (blueprint: sk-thm-sp-qbar).

Proof: choose finite coefficient models for arbitrary source and target objects
using sk-thm-sfb-qlbar-two-colimit, enlarging to their compositum. The algebraically
closed base has ell-cohomological dimension zero by sk-lem-base-field-cd. Thus
clause (3) of det-sp-qbar-finite-descent compares compact support and pullback with
their algebraic-closure versions. Compact support preserves constructibility and
its compactification comparisons satisfy the cocycle by sk-prop-sf-comp-coherence.
The coefficient-independent compatible roots in sk-def-sp-tate-twist identify
scalar extensions of the Tate lines. Apply lem-pur-ordinary-line-derived-scalar-comparison
with power d and lem-pur-derived-tensor-additive-constraints with shift 2d to
identify the right functor under scalar extension. These comparisons give the two
preservation assertions. At every finite coefficient field use sk-prop-sp-rational.
Its Hom bijection and its inverse commute with field enlargement by the unit and
counit equations of sk-lem-sp-field-extension. The Hom-colimit formula of
sk-thm-sfb-qlbar-two-colimit therefore induces mutually inverse maps on the desired
Hom sets. Descend comparison isomorphisms, their inverses and inverse equations
by det-sp-qbar-finite-descent (2) to see that these maps are independent of models.
Descend arbitrary arrows in both variables to prove naturality at a finite field,
where rational adjunction naturality applies. Finally use
lem-weil-pbc-adjunction-of-natural-bijection to construct the displayed adjunction.
All constructions use the fixed compactification through its canonical comparisons.
-/
theorem nativeSmoothPurityQbar
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (c : Compactification.BoundaryCompactification f.left) :
    ∃ (hSupport : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) X.left,
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.padicAlgClRingObj ell) c.obj.obj).obj K.obj))
      (hRight : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) Y.left,
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left
          ((nativeQbarPurityRight ell f.left d).obj K.obj)),
      Nonempty
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left).lift
          ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left).ι ⋙
            CondensedRing.rightDerivedLowerShriekOfCompactification
              (Profinite.padicAlgClRingObj ell) c.obj.obj) hSupport ⊣
         (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left).lift
          ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left).ι ⋙
            nativeQbarPurityRight ell f.left d) hRight) := by
  sorry

end AlgebraicGeometry.ProEtale
