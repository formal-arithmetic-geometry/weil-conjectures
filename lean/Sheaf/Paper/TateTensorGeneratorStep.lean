/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorGeneratorCompatibility

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-step)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- Tensor two already normalized maps to append one root factor.

Source: smooth-purity transport, Step 2, tensoring the root projections in order.
(blueprint: lem-pur-tate-tensor-generator-step)

Proof: for positive degree, the finite etale twist of degree d+2 is by definition
the tensor of its degree d+1 twist with the first root line. The comparison
pullback is strong monoidal, with pure-section formula given by the comparison
adjunction. Realization along `scalars` preserves this tensor: constant sections
are locally all sections of the constant coefficient sheaf, so the fixed-scalar
and sheaf-scalar balancing relations agree after sheafification. Apply f tensor g
after these comparisons. Scalar extension along the completed coefficient
projection is strong monoidal. In its target, contract the unit factor in
`integralLine 1` by the left unitor before appending the final root factor to
`integralLine (d+1)`. This defines the required morphism without choosing any
roots. For the generator equation, split each Fin(d+2) tuple into castSucc and
last. Place a in the first factor and 1 in the last factor; the defining finite
power generator is exactly that pure tensor. The hypotheses for f and g apply
to these subtuples. The normalized tensor constraints carry their two values to
scalars(a) tensor the integral generator of degree d+2. This is its defining
recursion. The argument is balanced in arbitrary scalars and is natural under
restriction; neither invertibility of ell nor a choice of root basis is needed.
The positive-degree restriction avoids identifying the separate finite degree-one
root-line definition with a tensor product containing a degree-zero factor. -/
theorem tateTensorQuotient_generator_step
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime] (n d : ℕ)
    (f : (realization T ell n).obj (finiteSheaf T ell n (d + 1)) ⟶
      quotientLine T ell n (d + 1))
    (g : (realization T ell n).obj (finiteSheaf T ell n 1) ⟶ quotientLine T ell n 1)
    (hf : GeneratorCompatible T ell n (d + 1) f)
    (hg : GeneratorCompatible T ell n 1 g) :
    ∃ h : (realization T ell n).obj (finiteSheaf T ell n (d + 2)) ⟶
      quotientLine T ell n (d + 2),
      GeneratorCompatible T ell n (d + 2) h := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
