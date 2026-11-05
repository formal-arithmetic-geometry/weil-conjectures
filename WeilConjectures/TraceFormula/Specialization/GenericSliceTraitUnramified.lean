/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance

/-!

# The change of trait of a generic slice trait is unramified

For a generic slice trait `D` of `𝔸¹_S`, `S = Spec k'⟦t⟧`
(`AlgebraicGeometry.GenericSliceTrait`), the composite `k'⟦t⟧ ⟶ R ⟶ K⟦t⟧` of the structure map
and of the change of trait is the coefficientwise map
(`AlgebraicGeometry.GenericSliceTrait.ι_comp_φ`), so `t` is a uniformizer of both `R` and `K⟦t⟧`
(`AlgebraicGeometry.GenericSliceTrait.maximalIdeal_eq_map_ι`): the change of trait
`Spec K⟦t⟧ ⟶ S'` is unramified, as needed by the invariance of nearby cycles under change of
trait (SGA 4½, [Th. finitude], 3.7).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

end AlgebraicGeometry.GenericSliceTrait
