/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionSingleMatePresentation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.FiniteCompositionSourceOrientationSquare
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.FiniteCompositionTensorRealization

/-! # Composition coherence for the specified smooth purity maps

Source: main-20261015, sec-smooth-purity/sk-prop-sp-composition,
thm-pur-composition-coherence (blueprint: thm-pur-composition-coherence).

The source identification is assembled from the ordered shifted Tate tensor powers,
monoidal comparison, pullback composition and the shift reassociation used by gamma.
The exceptional comparison is the recorded standing counit mate, transported through
the canonical constant-scalar equivalences. All objects are on the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

end Geometry
end WeilConjectures.PurityFiniteSetting
