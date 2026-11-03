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
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-- The Hom-colimit construction supplies the Q-bar adjunction once its two
preservation witnesses are available. This is the model-independence, naturality,
and `Adjunction.mkOfHomEquiv` part of `sk-thm-sp-qbar`, and is strictly weaker
than the theorem including the preservation conclusions.
Source: the Hom-colimit and adjunction-construction clauses of the proof of
`sk-thm-sp-qbar`.
Proof plan: choose common finite models for a source and target object and enlarge
their coefficient fields to a compositum. Use the normalized finite rational
adjunction and the field-extension unit and counit equations to define mutually
inverse maps on finite-stage Hom representatives. The Q-bar Hom descent theorem
proves independence of models and eventual equality at a common stage. Descend
arbitrary arrows in both variables to obtain naturality, then apply
`Adjunction.mkOfHomEquiv`; the two supplied witnesses only bundle the resulting
ambient functors into the bounded-constructible full subcategories.
-/
theorem generalFieldQbarAdjunction
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] (_hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hSupport : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) X.left,
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.padicAlgClRingObj ell)
            (CondensedRing.compactificationOverField f)).obj K.obj))
    (hRight : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) Y.left,
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left
          (((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f.left).mapDerivedCategory ⋙
            tensorRight ((DerivedCategory.singleFunctor _ 0).obj
              (spInternalSignedTwist X.left
                (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
                (spQbarTwist X.left ell) (d : ℤ))) ⋙ shiftFunctor _ (2 * (d : ℤ))).obj K.obj)) :
    Nonempty
      ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left).lift
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.padicAlgClRingObj ell)
            (CondensedRing.compactificationOverField f)) hSupport ⊣
       (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left).lift
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left).ι ⋙
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f.left).mapDerivedCategory ⋙
            tensorRight ((DerivedCategory.singleFunctor _ 0).obj
              (spInternalSignedTwist X.left
                (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
                (spQbarTwist X.left ell) (d : ℤ))) ⋙ shiftFunctor _ (2 * (d : ℤ)))) hRight) := by
  sorry
end AlgebraicGeometry.ProEtale
