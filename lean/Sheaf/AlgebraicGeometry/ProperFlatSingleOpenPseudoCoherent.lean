/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex

/-! # Pseudo-coherence of open restrictions of a proper relatively flat direct image

Source: Stacks Project, Tag 0A1H, Noetherian approximation paragraph; Tag 08E7.
(blueprint: lem-pc-proper-flat-single-open-pseudo-coherent).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The open restriction of the direct image is pseudo-coherent, without a Tor bound.
Source: Stacks Project, Tag 0A1H, approximation paragraph, with E=O_X and G=F[0];
Tags 02O5, 08E7, 08E5.
(blueprint: lem-pc-proper-flat-single-open-pseudo-coherent).

Proof: The assertion is local on U. Choose an affine neighbourhood of a point in U.
Express its ring as the filtered colimit of finitely generated Z-subalgebras.
Finite presentation descends the restricted morphism and module to a Noetherian
stage. Enlarge the stage to descend properness and relative flatness. Proper
coherence and the finite affine-cover cohomological bound give bounded coherent
cohomology for the direct image at this stage. Over a Noetherian scheme this is
pseudo-coherent, so on an affine refinement it has a bounded-above finite-free
representative. Relative flatness gives the derived base-change identification
with the original single-module direct image. Derived pullback of the finite-free
representative is computed termwise: its terms remain finite free, and its upper
bound remains unchanged. Open base change identifies the result with the specified
exact restriction to U. On a further open of U, transport this representative to
the localized site by the module equivalence. Uniqueness of localization transports
its derived isomorphism into the supplied independent localizations: compute each
version of direct image with the same K-injective resolution and compare Q.
These bounded-above finite-free witnesses prove pseudo-coherence. No lower bound
or finite Tor dimension is used. Empty opens are vacuous; F=0 uses zero complexes.
-/
theorem properFlat_single_open_isPseudoCoherent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    U.toScheme.IsPseudoCoherent ((schemeOpenRestriction S U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) := by sorry

end AlgebraicGeometry
