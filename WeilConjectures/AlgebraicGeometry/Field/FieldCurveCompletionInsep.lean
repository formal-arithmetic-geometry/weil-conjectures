/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.Proper.ProperGeometricallyReducedGlobalSectionsSeparable
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CurveProjectiveDenseCompletion
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSeparableBaseRefinement
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.GeonormalDimOneSmooth
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NormalizationGeonormalInsep
import WeilConjectures.AlgebraicGeometry.Finite.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Smooth projective completions after an inseparable field extension

Source: Stacks Project, Varieties, Tag 0GK5,
`lemma-dim-1-projective-completion-after-insep`, assertions (1)-(5)
(blueprint: lem-weil-pbc-field-curve-completion-insep).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
