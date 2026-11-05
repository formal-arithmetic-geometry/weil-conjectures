/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackNormalization
public import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackExistence
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarPullbackNaturality
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer

/-! # Pullback of the signed line scalar square

Source: blueprint main-20261015, prop-weil-twist-preserves.proof.md, first and final
sentences; Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0.
(blueprint: lem-pur-signed-line-scalar-pullback-square)

The structural ring maps are written as adjuncts R → u_* R' and S → u_* S'.
The pullbacks are Mathlib's actual module left adjoints, with existence supplied by
`module_pushforward_isRightAdjoint_of_universes`, hence the sheafified relative tensors.
The square is tested on the adjunction-unit images of scalar tensors. These generate
by the two adjunctions, so this is the morphism equality under canonical reassociation,
not an equality restricted to bases or to global sections. The evaluation clause likewise
specifies the transpose of pulled evaluation, precomposed by the inverse positive map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

end SheafOfModules
