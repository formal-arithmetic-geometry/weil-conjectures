/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackScalarFamilies

/-! # Primitive twist and composition scalar squares

Source: purity transport, scalar/pullback/tensor square and compositor cancellation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  (sq : u ≫ f = f' ≫ v) (d : ℕ)

attribute [local irreducible] D rationalDerivedPullback

/-- The two primitive scalar squares and naturality of the specified components.
Source: purity-transport coefficient-change calculation, Steps 2--4 and 7--8 of
lem-pur-twisted-pullback-square-scalars; Stacks 07A4 and 099N.
(blueprint: lem-pur-twisted-pullback-scalar-primitives).

Proof: On a common flat K-flat representative, use scalarExtensionTowerCoherence
with its second input the degree-zero Tate line. The roots-induced line maps
commute with scalar extension: both routes take (zeta tensor e) tensor l to the
pullback of zeta tensor el. Tensor powers preserve the calculation, while the
zeroth power uses the coefficient unit. Normalize the whole quotient tower and
realize it; tensor balancing identifies the scalar and pullback maps with the
specified completed comparisons. Apply the common even shift and localize to
obtain Z. For C apply the composition law for scalar/pullback comparison twice,
once to u,f and once to f',v. The comparison at the composite morphism is the
same by sq; cancel the first compositor and insert the second. This gives exactly
the displayed t-square. Every constituent is natural on integral representatives;
localization extends the naturality equations to every raw rational arrow.
Whiskering and composing these natural maps proves all clauses of Naturality.
No exceptional exchange or detection by separate finite reductions is used. -/
theorem twistedPullbackScalarPrimitives :
  (∀ M : sfRationalConstructibleCategory l E X,
    (p l E L i u ((D l E X d).obj M)).hom ≫
      (rationalDerivedPullback l L u).map (q l E L i X d M).hom ≫
      (z l L u d ((T l E L i X).obj M)).hom =
    (T l E L i X').map (z l E u d M).hom ≫
      (q l E L i X' d ((rationalDerivedPullback l E u).obj M)).hom ≫
      (D l L X' d).map (p l E L i u M).hom) ∧
  (∀ K : sfRationalConstructibleCategory l E Y,
    (T l E L i X').map ((t l E u f f' v sq).hom.app K) ≫
      (PV l E L i f' v K).hom =
    (PU l E L i u f K).hom ≫
      (t l L u f f' v sq).hom.app ((T l E L i Y).obj K)) ∧
    Naturality l E L i u f f' v sq d := by sorry

end WeilConjectures.TwistedPullbackScalars
