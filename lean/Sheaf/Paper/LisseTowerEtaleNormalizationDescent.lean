/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence

/-! # Descending and realizing normalization arrows after descent of the levels

Source: Stacks Tags 06YY, 099Z, 09B1 and 03DA.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- Normalization arrows descend once the etale levels and their comparison are given.
The statement neither constructs etale levels nor asks for finite locally constant
cohomology, algebraic local markings, or inhabited Isom stalks.

Source: Stacks Project, Tags 099Z and 09B1 (bounded-below full faithfulness),
06YY (scalar extension), 03DA and 0H7J (restriction and inverse image).
(blueprint: lem-weil-pbc-lisse-tower-etale-normalization-descent).

Proof: the fixed realization is an equivalence: restriction along the completion
quotient is an equivalence, and the constant scalar map is locally bijective. Transport
the actual consecutive semilinear transition of M along the two given comparisons and
the canonical coefficient-restriction interchange. The resulting arrow between the
comparison images of D_(n+1) and Res D_n has a unique etale preimage by bounded-below
full faithfulness; call it delta_n. This is a statement about actual arrows, not a
choice of a new tensor functor. The inverse-image scalar mate is invertible by the
sectionwise tensor computation. Thus the image of the scalar adjunct of delta_n is
the pullback of M.normalization; it is invertible. Exact conservative comparison
reflects this invertibility. The adjunction therefore makes delta_n universal.
The same tensor mate for restriction to an etale object proves local universality.
Exact constants and the constant scalar-extension comparison prove the analogous
claim for every universal algebraic arrow. Coefficient-mate pasting and the canonical
inverse-image compositors show that both localized arrows have restriction coherence.
Applying inverse image to a supplied square and using those coherences proves the
coefficient coherence fields.

For V over U.left, realize fixed sheaves over V.left by restricting their algebraic
scalars and sheafifying along constant scalar sections, then pull to W.left along
f.left. The inverse-image coefficient comparison identifies the target coefficient
ring with the prescribed pullback from X. Apply this construction termwise and localize
to define realization. Pullback of the given level comparisons gives actual. Constant
sheafification and its inverse-image comparison give model naturally for every E.
Two successive scalar restrictions give scalar. Its equation on delta_n is the
pullback of the defining descent equation, hence the actual restricted step of M.
On a constant arrow k the sectionwise restriction calculation is the identity on every
constant section. Localization and the specified mapDerivedCategoryCompIso and
restrictScalarsComp' compositors identify it with lisseTowerAlgebraArrow d n k.
Pasting with constantAdicQuotientRightIso gives exactly model_normalized for all k.
The argument uses the comparisons at U only, then their canonical pullbacks; it makes
no new or incompatible choices of comparisons on V or W. It applies unchanged to
empty bases and zero objects, with no finite Tor-amplitude assumption. -/
theorem lisse_tower_etale_normalization_descent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt)
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (D n)))
    (e : ∀ n : ℕ, (lisseTowerFixedRealization (U.hom ≫ g) d n).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj (D n)) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :
    Nonempty (LisseTowerEtaleNormalization X Y g d M U D) := by sorry

end AlgebraicGeometry.Scheme
