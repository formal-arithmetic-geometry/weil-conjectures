/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.DerivedAdjoint

/-! # Bijectivity of the fixed section comparison

Source: Stacks Project, Tag 0B91, clause (2), and Tag 079W.
(blueprint: lem-sc-picard-direct-image-section-map-bijective)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The fixed degree-zero comparison is bijective after arbitrary base change.
Source: Stacks Project, Tag 0B91, clause (2), and Tag 079W.
(blueprint: lem-sc-picard-direct-image-section-map-bijective)

Proof: Put p = pr_W and M = pr_X^*L. Invertibility makes L finitely presented
and intrinsically flat; flatness of f makes M flat over W. Properness and finite
presentation persist under base change. Identify the square used in
picardDirectImageSectionMap with the chosen pullback square by its universal
property. Apply perfect_derivedDirectImage_baseChange to M. Its canonical
comparison is the base-change mate followed by the single pullback comparison;
transporting its target by the fixed coefficient isomorphism preserves invertibility.
The source structure-sheaf comparison is invertible. Under canonical derived
adjunction, morphisms from the degree-zero structure sheaf into Rp_*N[0] are
morphisms from the pulled-back structure sheaf into N[0]. Pullback preserves the
structure sheaf and the single functor is fully faithful. Thus these morphisms
are precisely ordinary module morphisms O to N. Their identification with H^0 of
Rp_*N[0] is the canonicalDirectImageH0Iso computation of the right-derived unit,
so evaluating the displayed map at 1 is exactly the section equivalence.
Evaluation at 1 and restriction of the pushforward from inverse-top to top are
bijective. The same argument applies to zero modules on empty schemes. -/
theorem picardDirectImageSectionMap_bijective
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) {T : Scheme.{v}} (t : T ⟶ W) :
    Function.Bijective (picardDirectImageSectionMap f L W k t) := by sorry

end AlgebraicGeometry.Scheme
