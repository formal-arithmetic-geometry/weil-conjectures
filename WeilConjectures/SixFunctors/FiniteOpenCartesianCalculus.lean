/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenBaseChangeSquareData

/-! # Canonical open projection and base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionBaseChange
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
variable (E : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]

/-- The unit-normalized finite open projection and exchange maps satisfy the
Cartesian tensor identity on arbitrary ambient derived inputs.

Source: Stacks 03DI, 0E8I, 0GL1 and 07A4; blueprint
sec-six-functors/sk-prop-sf-pf-coherence, base-change paragraph, steps 5--6.
(blueprint: lem-sf-finite-open-cartesian-calculus).

Proof: use the localized open adjunction and the K-flat total tensor models.
The inverse projection is the transpose of the open unit tensored with identity
followed by inverse tensor pullback. The slice-site projection formula makes it
invertible. The reverse exchange is the specified open mate; open Cartesian
base change makes it invertible. These constructions are natural in both inputs
and give FiniteMaps, with exactly its two transpose equations and mate equation.
Transpose the inverse Cartesian tensor square under the base-changed open
adjunction. Substitute these defining transposes. Naturality moves the square
comparison past the inverse projection; monoidality of the canonical pullback
square moves it past the tensor comparison. Naturality of the tensor comparison
moves the open unit to the first tensor factor. The base-changed inverse
projection transpose and the exchange transpose identify the remaining factors.
Injectivity of the adjunction equivalence identifies the inverse routes.
Cancel the invertible projection and exchange maps to obtain the displayed
forward identity. This calculation uses the complete signed total complexes,
so applies to unbounded inputs, including zero objects and empty opens. -/
theorem finite_open_cartesian_calculus (n : ℕ) (Q : SixFunctorCompactifiedSquare D) :
    ∃ d : FiniteMaps D c E n Q,
      ∀ (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
        (P : proEtaleDerivedCategory Q.Z.obj.left (finiteCoefficientRing c.l E (n + 1))),
  OpenIdentityAt
    (finiteIntrinsicDerivedTensor c.l E Q.X.obj.left n)
    (finiteIntrinsicDerivedTensor c.l E Q.Z.obj.left n)
    (finiteIntrinsicDerivedTensor c.l E Q.X'.obj.left n)
    (finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n)
    (finiteDerivedPullback c.l E n Q.h.hom.left)
    (finiteDerivedPullback c.l E n Q.g'.hom.left)
    (finiteDerivedPullback c.l E n Q.i.hom.left)
    (finiteDerivedPullback c.l E n Q.i'.hom.left)
    (finiteOpen D c E n Q) (finiteOpen' D c E n Q)
    (fun N T ↦ d.gamma.hom.app (N, T)) (fun N T ↦ d.gamma'.hom.app (N, T))
    d.beta.hom.app K P
    ((finiteMu D c E Q.g' n K
      ((finiteDerivedPullback c.l E n Q.i.hom.left).obj
        P)).hom)
    ((finiteMu D c E Q.h n ((finiteOpen D c E n Q).obj K)
      P).hom)
    ((sfIntrinsicDerivedSquarePullback (finiteCoefficientRing c.l E (n + 1))
      Q.g'.hom.left Q.i'.hom.left Q.i.hom.left Q.h.hom.left Q.openSquare.w).hom.app
        P)
 := by sorry

end WeilConjectures.OpenProjectionBaseChange
