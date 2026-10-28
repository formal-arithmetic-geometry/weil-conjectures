/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Paper.FiniteScalarMonoidalModel
public import Sheaf.Paper.FiniteScalarTensorData

/-! # The representative equation for constructed scalar monoidal transport

Source: finite reduction of purity, proof Step 2; Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The explicitly transported native tensorator satisfies the full cochain counit square.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-monoidal-representative).

Proof: the native left-derived tensor comparison is characterized by its counit
square on the homotopy category. Pass from homotopy objects to cochain objects
using quotientCompQhIso and the quotient functor's monoidal structure. The exact
restriction comparison mapDerivedCategoryFactors identifies the transpose of the
localized ordinary scalar unit with that same derived counit. Uniqueness of left
adjoints identifies this transpose for the chosen fixed scalar adjunction with
the native counit preceded by the inverse leftAdjointUniq comparison. Substitute
this identity in each of the three counit components. The formula for monoidal
transport cancels the two tensor factors of leftAdjointUniq and its tensor-source
component. What remains is exactly the native tensor comparison's counit square.
This argument is natural for every pair of complexes; it does not require the
coefficient morphism to be flat or the complexes to be bounded or K-flat. It also
applies to the identity coefficient morphism, zero rings and the empty scheme. -/
theorem finiteScalarMonoidalModel_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (finiteScalarTensorData φ T).source C D =
      ((finiteScalarMonoidalModel φ T).μIso
        (_root_.DerivedCategory.Q.obj C) (_root_.DerivedCategory.Q.obj D)).inv ≫
          (finiteScalarTensorData φ T).tail C D := by
  sorry

end WeilConjectures.PurityFiniteSetting
