/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperationsSupplement

/-! # Scalar compatibility of the ordinary small-site direct-image comparison

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D7.
(blueprint: lem-sf-integral-compactification-ordinary-scalar-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The inverse of the Hom-normalized underlying comparison respects local scalars.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D7; the section normalization
of def-sf-integral-compactification-ordinary-site-transport.
(blueprint: lem-sf-integral-compactification-ordinary-scalar-action).

Proof: write C for sfCbcModelModules. Its scalar action is restriction along the
constant-section-normalized sfCbcModelRingMap. On C(f_* M), r acts through the
adjunct constant coefficient map and then the action of M. On the representing
module right adjoint, transpose multiplication through the module Hom bijection.
The defining Hom equation of constantDirectUnderlying identifies this transpose
with the geometric transpose after pullInsertion. The generalized-section scalar
identity for the algebraic inverse image identifies its scalar with the image of r
under the same adjunct coefficient map. These coefficient maps agree: precompose
with the unit of constant sheafification, where both send a constant to that same
constant; the sheafification adjunction gives equality. Thus the hom comparison
intertwines multiplication by r on every section. Apply its inverse to that
identity, and use the hom-inverse identities, to obtain the displayed formula.
The argument uses no finiteness or nonemptiness of the scheme or of the section
module, so it includes empty sites and zero modules. -/
theorem ordinaryDirectUnderlying_smul {V T : Scheme.{u}} (f : V ⟶ T)
    (M : ProEtale.StrictTower.Modules (ULift.{u + 1} (constantRing l E)) V)
    (W : (proEtaleSiteModel T)ᵒᵖ)
    (r : (sfCbcModelRing T (constantRing l E)).obj.obj W)
    (x : ((sfCbcModelModules T (constantRing l E)).obj
      ((ProEtale.StrictTower.moduleDirectImage
        (ULift.{u + 1} (constantRing l E)) f).obj M)).val.obj W) :
    ((constantDirectUnderlying l E f).inv.app
      ((sfCbcModelModules V (constantRing l E)).obj M)).hom.app W (r • x) =
      r • (show (((sfCbcMorphism f).modulePush
          (ULift.{u + 1} (constantRing l E))).obj
            ((sfCbcModelModules V (constantRing l E)).obj M)).val.obj W from
        ((constantDirectUnderlying l E f).inv.app
          ((sfCbcModelModules V (constantRing l E)).obj M)).hom.app W x) := by sorry

end WeilConjectures.IntegralCompactificationBridge
