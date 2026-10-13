/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorComplex
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Relative flatness of local tensor terms

Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: lem-pc-strict-perfect-relative-tensor-terms-flat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

/-- Each term of the explicitly scalar-restricted local total tensor is flat over
f inverse-image O_S on the open site. Source: Stacks Project, Tags 0DJQ and 08CI,
local relative Tor calculation; Tag 05NE, flatness detected on stalks.

Proof: at x in U choose an affine neighbourhood of f(x). Affine neighbourhoods of x
inside its preimage form a filtered basis. The hypothesis IsFlatOver makes every
G-term section module flat over this base section ring. Their filtered colimit is
the stalk and remains flat. Localizing the base ring gives flatness over O_S,f(x),
which is the stalk of the inverse-image ring. The stalks of L terms are retracts
of finite free O_X,x-modules, so tensoring with them gives retracts of finite sums
of these flat base modules. The degreewise total is a direct sum of these tensors;
stalks commute with the tensor sheafification and this sum. Sums and retracts of
flat modules are flat. Exactness of tensor is detected on stalks, giving flatness
of the scalar-restricted term as a sheaf on the localized site. The empty open,
zero summands and a zero complex satisfy the same stalkwise argument.
(blueprint: lem-pc-strict-perfect-relative-tensor-terms-flat). -/
theorem strictPerfect_relativeTensor_terms_flat
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    ∀ n : ℤ, SheafOfModules.IsFlat
      ((strictPerfectRelativeTensorComplex f U L G).X n) := by sorry

end AlgebraicGeometry.Scheme
