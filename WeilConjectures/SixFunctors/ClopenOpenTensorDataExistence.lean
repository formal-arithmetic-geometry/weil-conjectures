/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
import WeilConjectures.SixFunctors.ClopenReverseModuleAdjunction
import WeilConjectures.SixFunctors.OpenOperationModels
import WeilConjectures.SixFunctors.OpenTensorSupportAux

/-! Auxiliary existence of the two open tensor records needed by the clopen data.

This isolates the independent restriction-tensor constructions for the pullback open
and the canonical clopen lift. Source: the open tensor normalization and clopen
reverse-adjunction steps of `lem-sf-clopen-comparison-tensor-data-existence`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

/-- The open tensor and reverse-adjunction records below the main clopen datum.
This is strictly below `data_nonempty`: it contains no pullback tensor records and
no composite delta map.
Source: Stacks 0GL1 and 04TS.
(blueprint: lem-sf-clopen-comparison-tensor-data-existence) -/
structure OpenTensorData {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) {A : Scheme.{u}} (s : A ⟶ d.U') [IsOpenImmersion s] where
  tensorB : OpenTensor m d.j' d.S o.opens.extension' o.tensorX' o.tensorU'
  extensionS : OpenExtension m s (restrictRing m d.j' d.S)
  tensorA : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel
    (restrictRing m s (restrictRing m d.j' d.S))
  tensorS : OpenTensor m s (restrictRing m d.j' d.S) extensionS o.tensorU' tensorA
  rightAdjunction : restrict m s (restrictRing m d.j' d.S) ⊣ extensionS.ordinary
  counit_normalization : ∀ M,
    extensionS.adjunction.unit.app M ≫ rightAdjunction.counit.app M = 𝟙 M

/-- The normalized open tensor and clopen reverse-adjunction records exist.
The proof first instantiates the open operation model on `d.j'`, then transports its
pure-tensor and K-flat comparison maps through restriction to `s` using the support
lemmas. The open normalization theorem supplies the exact comparison equations. The
clopen reverse-module-adjunction theorem identifies restriction with the first factor
of the clopen gluing equivalence and extension with insertion of zero; its counit
normalization is exactly the final field. These records are then packaged as
`OpenTensorData o s`. Source: Stacks 0GL1, 04TS and the open tensor normalization
proof. (blueprint: lem-sf-clopen-comparison-tensor-data-existence) -/
theorem open_tensor_data_nonempty {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) {A : Scheme.{u}}
    (s : A ⟶ d.U') [IsOpenImmersion s] [IsClosedImmersion s] :
    Nonempty (OpenTensorData o s) := by
  sorry

end SheafOfModules.ClopenComparisonTensorSquare
