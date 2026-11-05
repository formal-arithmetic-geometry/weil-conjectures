/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientStrictSquare
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnit
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnique
import WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso
import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso
import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso

/-! # Transposes of the ordinary quotient arrows

The transpose of the ordinary quotient arrow under extension of scalars along the consecutive
quotient map `q : A_(n+1) → A_n` is invertible. The arrow factors as the image under the chart
coordinates of the ring-level quotient transition `R_(n+1) ⊗ N ⟶ R_n ⊗ N`, followed by the
strict square identifying the two scalar restrictions. The transpose is accordingly the mate of
this square followed by the chart image of the ring-level transpose; the latter is the
comparison of the left adjoints of the restriction along `R → R_n`, and the mate is invertible
since its iterated mate along the chart adjunctions is.

Source: Stacks Project, Tags 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
