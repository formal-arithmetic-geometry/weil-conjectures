/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.SmoothPurity.WeilSheafComplex

/-!
# Mixedness of real constructible Weil sheaves by curves

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, node statement and
proof paragraphs 1--9 (blueprint: thm-zl-real-mixed-by-curves).

The theorem states the condensed-coefficient formulation: a constructible actual
Weil module over a separated finite-type scheme over a finite field, whose local
Frobenius factors are coefficientwise real under `iota`, admits a finite
filtration with punctually pure quotients. The proof follows the blueprint's
curve-testing route: reduce to a lisse smooth affine stratum, test each
geometrically irreducible constituent on curves and read its common weight from
an anchor eigenvalue, transport the filtration through a finite constant
extension and descend it by the trace splitting, then glue the strata by the
open--closed exact sequence. The empty and zero-dimensional cases are included
(the zero object has the empty filtration, and point fibres use Jordan flags).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

open NativeCondensedModule

/-- Every constructible `iota`-real actual `Qbar_l`-Weil sheaf on a separated
finite-type scheme over a finite field is `iota`-mixed.

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, node statement and
proof paragraphs 1--9 (blueprint: thm-zl-real-mixed-by-curves). The hypotheses
are the finite-field datum, a prime `l` different from the characteristic, a
separated finite-type model `X₀`, constructibility of the carrier in
`Cons(X, Qbar_l)` (`IsConstantModelConstructible`, the predicate of the coefficient
heart and of the filtration in `NativeL2.Mixed`), and
coefficientwise reality of all local factors. The conclusion is the existence
of a real bound `w` for which `NativeL2.Mixed` supplies the finite filtration
and punctually pure successive quotients. The proof route is: curve testing of
geometrically irreducible lisse constituents; the anchor eigenvalue computes a
curve-independent weight; cyclic sheet transport handles a finite constant
extension; trace splitting descends mixedness; and open--closed gluing plus
Noetherian induction handles arbitrary constructible sheaves. -/
theorem real_isMixed_by_curves
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hℓ : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {M : WeilModule D l X₀}
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (iota : PadicAlgCl l →+* ℂ)
    (hreal : NativeCondensedWeil.Real D l X₀ M iota) :
    ∃ w : ℝ, Mixed D l X₀ M iota w := by
  sorry

end WeilConjectures.NativeL2
