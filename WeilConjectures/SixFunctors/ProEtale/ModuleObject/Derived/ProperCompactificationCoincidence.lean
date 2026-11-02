/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison
public import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
import WeilConjectures.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
import WeilConjectures.Compactification.DenseCategory

/-! # Proper coincidence and its canonical exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-comp-proper/_section.md and sk-prop-sf-comp-proper.proof.md
(blueprint: sk-prop-sf-comp-proper).

The normalization uses the actual refinement from the identity compactification.
Compatibility is an equation of the ordinary ambient condensed-module exchanges.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactificationReindexing

/-- The identity compactification, as an object of the dense boundary-refinement category.
Its open immersion is the identity, hence quasi-compact and scheme-theoretically dense.
Source: proper-coincidence proof, first sentence (blueprint: sk-prop-sf-comp-proper). -/
def properDenseIdentityCompactification {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Compactification.DenseBoundaryCompactification f :=
  ⟨⟨⟨Compactification.ofIsProper f, inferInstanceAs (QuasiCompact (𝟙 X))⟩⟩,
    inferInstanceAs (IsSchemeTheoreticallyDominant (𝟙 X))⟩

/-- The canonical refinement from the identity compactification to any compactification
of a proper map. Its ambient arrow is the supplied open immersion; properness follows
from properness of f and separatedness of the compactification's proper factor.
Source: proper-coincidence proof, identity model and comparison paragraph
(blueprint: sk-prop-sf-comp-proper). -/
def properIdentityRefinement {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    (c : Compactification f) : (Compactification.ofIsProper f).Refinement c where
  hom := c.i
  i_hom := Category.id_comp _
  hom_g := c.comm.symm

end AlgebraicGeometry.ProEtale.CondensedRing
