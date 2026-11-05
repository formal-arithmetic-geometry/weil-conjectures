/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.RingTheory.ProperBaseChange.MinimalPrimeFiniteTypeFiniteAway
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Finiteness over an open containing all component generic points

Source: Stacks Project, Morphisms of Schemes, Tag 02NW, lemma-generically-finite,
equivalence (1) and (4), applied to every component generic point.
(blueprint: lem-weil-pbc-generic-finite-morphism-open-neighborhood)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
