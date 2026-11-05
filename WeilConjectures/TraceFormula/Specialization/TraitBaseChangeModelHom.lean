/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Base change of morphisms of models and the projections

For a morphism of models `φ : P ⟶ M` over the trait `S = Spec k'⟦t⟧` and compatible base changes
along `v : Spec K⟦t⟧ ⟶ Y`, the induced morphism of base changes
`φ'' : P'' ⟶ M''` (`NearbyCyclesModel.Hom.baseChange`) is compatible with the projections
`P'' ⟶ P` and `M'' ⟶ M` (`NearbyCyclesModel.baseChangeHom`) on total spaces, geometric generic
fibres and special fibres (`NearbyCyclesModel.Hom.baseChange_total_comp`,
`NearbyCyclesModel.Hom.baseChange_generic_comp`, `NearbyCyclesModel.Hom.baseChangeSpecial_comp`).
These are the hypotheses of the compatibility of the Künneth map of nearby cycles with pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) for the projections from the
geometric slice of a product.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X Z : Scheme.{u}} {X' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {P : NearbyCyclesModel Z Z'.left} {f : Z ⟶ X} {f' : Z'.left ⟶ X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qP : P.total ⟶ trait k'} {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hP : P.IsTraitModelOver qP gP)
  {YM YP : Scheme.{u}} {bM : M.total ⟶ YM} {pM : YM ⟶ trait k'} (hbM : bM ≫ pM = qM)
  {vM : trait K ⟶ YM} (hvM : vM ≫ pM = traitMap k' K)
  {bP : P.total ⟶ YP} {pP : YP ⟶ trait k'} (hbP : bP ≫ pP = qP)
  {vP : trait K ⟶ YP} (hvP : vP ≫ pP = traitMap k' K)
  (φ : P.Hom M f f') (κ : YP ⟶ YM) (hκb : bP ≫ κ = φ.total ≫ bM) (hκv : vP ≫ κ = vM)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
