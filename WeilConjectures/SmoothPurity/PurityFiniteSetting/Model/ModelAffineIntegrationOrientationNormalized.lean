/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization

/-! # The canonical normalized affine family

The finite-coordinate family is the inverse diagonal orientation. Its ordered
normalization is proved through the prescribed reversed-coordinate isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwist diagonalOrdinaryDualizing
  iteratedAffineLine iteratedAffineLineProj Etale.affineLinearBaseCoefficient

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting
end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

/-- The inverse diagonal orientation on each fixed finite-coordinate affine projection.
Source: composition proof, affine model normalization.
(blueprint: lem-pur-model-affine-integration-orientation-normalized). -/
def modelAffineCanonicalGamma (P : PurityFiniteSetting.{u}) : P.ModelAffineGamma :=
  fun B _ aB _ _ r ↦ by
    letI := DiagonalPasting.affineDimension r B
    exact (P.diagonalDualizingObject r (DiagonalPasting.pr r B) aB).symm

end WeilConjectures.PurityFiniteSetting
