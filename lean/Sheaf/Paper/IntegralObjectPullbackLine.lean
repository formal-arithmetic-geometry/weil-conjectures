/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Completed inverse image on a trivialized integral line

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9;
Stacks Project, Tags 04J0, 06YY and 08TC.
(blueprint: lem-pur-integral-object-pullback-line).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- A slice basis computes the actual completed inverse image of a line.

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9;
Stacks Project, Tags 04J0, 06YY and 08TC.
(blueprint: lem-pur-integral-object-pullback-line).

Proof: place L in degree zero. Local freeness makes this a K-flat complex with
flat terms, so it is an allowed representative of integralDerivedPullback. At
quotient exponent n+1, ordinary scalar extension commutes with restriction to
W. Extend the supplied slice basis to the finite quotient. Inverse image along
the object W is slice restriction followed by the pro-etale slice equivalence;
the unit-normalized constant-ring comparison then identifies the pulled-back
finite line with the regular finite coefficient module on W.left. The basis
is the reduction of one fixed integral basis, so these identifications commute
with every quotient transition and with the augmentation. Consequently the
whole strict pullback tower is isomorphic to the coefficient quotient tower
placed in degree zero. Products and the mapping-cocone construction carry this
tower isomorphism to a Roos-complex isomorphism. The regular completed module
is derived complete: its ordinary quotient tower has the completed coefficient
ring as its limit and locally surjective transitions. Its augmented Roos map
is therefore an isomorphism after Q. Compose the defining representative
comparison of integralDerivedPullback, the Roos isomorphism, and the inverse
regular augmentation. This proves exactly the displayed object isomorphism,
including the empty scheme and the zero module category. -/
theorem integralObjectPullbackLine (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (W : X.ProEt)
    (L : integralTowerModules l E X) (hL : L.IsFiniteLocallyFreeOfRank 1)
    (e : L.over W ≅
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X)).over W) :
    Nonempty ((integralDerivedPullback l E W.hom).obj
      ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W.left))) := by
  sorry

end WeilConjectures
