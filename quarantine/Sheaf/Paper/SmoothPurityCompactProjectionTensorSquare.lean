/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Paper.SmoothPurityCompactProjectionData
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.RingedSquareTensorCompatibility
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Tensor compatibility of the section-normalized pullback square

Source: Stacks 03EL, 07A4, 0D6D and 0E48.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

/-- Tensor compatibility of the section-normalized pullback square.
This is an equality of inverse-image comparisons alone, before taking mates or
introducing an open extension or a compact-support projection map.
Source: Stacks 03EL, 07A4, 0D6D and 0E48
(blueprint: lem-sp-compact-projection-tensor-square).

Proof: conjugate the specified sectionwise direct-image square through the ordinary
module adjunctions. The resulting ordinary square sends each scalar-extension
insertion to the insertion along the same fibre-product comparison. The ordinary
pure-tensor normalizations therefore make the two routes equal: on a generalized
pure tensor both apply this comparison to its two factors. The tensor universal
property extends the equation to module sheaves. Apply it in each bidegree of two
flat-term K-flat complexes and sum along the total-complex diagonals. Both routes
preserve bidegrees and the sign on the second differential, so give equal chain maps.
The defining representative equations of `TensorComparison` and the termwise
localization formula for `Presentation.square` identify these maps with the displayed
routes. Two-variable K-flat descent proves the equality for all derived inputs.
This proof takes place on the vertical diagram site as a single ringed site for
systems, retaining transitions; it does not infer equality from level evaluations. -/
theorem Presentation.tensor_square {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) (M N : Der (c.ring Y)) :
    (o.square s).hom.app ((o.tensor Y).functor.obj (M, N)) ≫
        (o.operation a).left.map ((o.tensorComparison f).comparison.hom.app (M, N)) ≫
        (o.tensorComparison a).comparison.hom.app
          ((o.operation f).left.obj M, (o.operation f).left.obj N) =
      (o.operation b).left.map ((o.tensorComparison g).comparison.hom.app (M, N)) ≫
        (o.tensorComparison b).comparison.hom.app
          ((o.operation g).left.obj M, (o.operation g).left.obj N) ≫
        (o.tensor X').functor.map
          (CategoryTheory.Prod.mkHom ((o.square s).hom.app M) ((o.square s).hom.app N)) := by
  sorry

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
