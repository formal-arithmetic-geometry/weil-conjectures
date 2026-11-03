/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
import WeilConjectures.AlgebraicGeometry.GeneralFieldSmoothPurityQbarSupport
import WeilConjectures.AlgebraicGeometry.GeneralFieldSmoothPurityQbarSource
import WeilConjectures.AlgebraicGeometry.GeneralFieldSmoothPurityQbarAdjunction

/-! # Smooth purity with condensed algebraic-closure coefficients

Source: latest blueprint,
`part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/`
`sec-coefficient-fields/sk-thm-sp-qbar/_section.md` and `sk-thm-sp-qbar.proof.md`
(blueprint: sk-thm-sp-qbar).

This statement uses the finite-subextension-valued condensed algebraic closure,
pulled back to the small pro-etale sites. The bounded constructible categories
are the full subcategories represented by `ConstantModelBoundedConstructible`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Smooth purity over a finite or algebraically closed field: compactly supported
pushforward is left adjoint to inverse image followed by the condensed Tate twist
and the cohomological shift. The two preservation witnesses express that the
specified ambient functors restrict to the bounded constructible categories.

Source: latest blueprint,
`part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/`
`sec-coefficient-fields/sk-thm-sp-qbar/_section.md`, order 479, and
`sk-thm-sp-qbar.proof.md` (blueprint: sk-thm-sp-qbar).

Proof: choose finite coefficient models and a common compositum using the two-colimit
formula. The base-field cohomological-dimension bound and scalar six-functor
comparisons identify compact support and pullback after extension of scalars; the
coefficient-independent Tate-line comparisons identify the twisted pullback. At each
finite coefficient field, the rational smooth-purity adjunction and its normalized
field-extension compatibilities give compatible Hom bijections. The two-colimit
formula descends these bijections, proves independence of models and naturality,
and the natural-bijection constructor produces the displayed adjunction. The optional
unique-adjoint comparison is applied only after this adjunction has been constructed.
-/
theorem smoothPurityQbar
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] (_hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    let right :=
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f.left).mapDerivedCategory ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj
          (spInternalSignedTwist X.left
            (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
            (spQbarTwist X.left ell) (d : ℤ))) ⋙ shiftFunctor _ (2 * (d : ℤ))
    ∃ (hSupport : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) X.left,
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.padicAlgClRingObj ell)
            (CondensedRing.compactificationOverField f)).obj K.obj))
      (hRight : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) Y.left,
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left
          (right.obj K.obj)),
    Nonempty
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left).lift
          ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left).ι ⋙
            CondensedRing.rightDerivedLowerShriekOfCompactification
              (Profinite.padicAlgClRingObj ell)
              (CondensedRing.compactificationOverField f)) hSupport ⊣
         (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left).lift
          ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left).ι ⋙
            right) hRight) := by
  dsimp
  let hSupport := generalFieldQbarSupportClosed ell _hk f
  let hRight := generalFieldQbarSourceClosed ell _hk f d
  exact ⟨hSupport, hRight,
    generalFieldQbarAdjunction ell _hk f d hSupport hRight⟩

end AlgebraicGeometry.ProEtale
