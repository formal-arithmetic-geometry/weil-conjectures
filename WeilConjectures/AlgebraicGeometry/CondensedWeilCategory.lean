/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # The condensed Weil category and its coefficient functors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/_section.md, strict pairs and complement;
finite derived reduction as in thm-pur-finite-reduction-of-purity, Step 2.
(blueprint: def-wf-weil-category).

The category itself is the existing `StrictWeil.modelComplex`: fixed pairs on the ordinary
uncompleted condensed Dctf, directly also for the finite-subextension-valued algebraic
closure. Its objects, morphisms, composition and forgetful functor are unchanged. For field
coefficients the recorded `integral_ctf_equals_bc` identifies Dctf with Dbc.
This file supplies the coefficient functor, including nonflat finite reduction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (g : X.left ≅ X.left)

/-- Restrict the inverse of the normalized scalar-adjunction pullback comparison.
Its components are P' T_b K to T_b P K. The chosen pullback-data witness has its hom
fixed by thetaNormalization to scalarSixPullHom; thus this does not choose an arbitrary
natural isomorphism. Fully faithful inclusion retains that specified comparison.
Source: latest blueprint, coefficient functor on strict pairs, and scalar-six pullback
normalization (blueprint: def-wf-weil-category). -/
def scalarFrobeniusComparison :
    scalarExceptionalChange ell k a ha X ⋙ smallAction Λ'.X g ≅
      smallAction Λ.X g ⋙ scalarExceptionalChange ell k a ha X :=
  Functor.fullyFaithfulCancelRight
    (constantModelBoundedConstructible Λ'.X X.left ⊓
      DerivedCategory.finiteTorAmplitude _).ι
    (Functor.isoWhiskerLeft
      (constantModelBoundedConstructible Λ.X X.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι
      ((Classical.choice scalarSixPullbackData_exists).theta a g.hom).symm)

/-- Derived coefficient extension of strict Weil pairs: the underlying functor is exactly
T_b, the structure is lambda followed by T_b(phi), and maps are sent by T_b.
The fixed-pair transport supplies the commuting square, identities and composition.
No flatness of b or k-linearity of g is assumed.
Source: latest blueprint, strict pairs; finite reduction Step 2
(blueprint: def-wf-weil-category). -/
def scalarExtension : Complex Λ.X g ⥤ Complex Λ'.X g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (scalarFrobeniusComparison ell k a ha X g)


end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil
