/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Topology.Stratification

/-!
# Stratifications of a scheme

A *stratification* of a scheme `X` (`AlgebraicGeometry.Scheme.Stratification`) is a
stratification of its underlying topological space — a finite partition into locally closed
subsets, `Topology.Stratification`, following [Stacks 09XZ] — together with, for each
stratum, a scheme immersed in `X` whose set-theoretic image is that stratum.

This is the site-independent input to constructibility: a sheaf on the small étale site
(`WeilConjectures.ConstructibleSheaf.Etale`) or on the small pro-étale site
(`WeilConjectures.ConstructibleSheaf.ProEtale`) of `X` is constructible if its pullbacks to
the strata of some stratification are finite locally constant. The scheme structure on a
stratum is a choice recorded by the immersion `S.immersion i : S.domain i ⟶ X`; by
topological invariance of these sites the resulting conditions do not depend on it.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A *stratification* of a scheme `X`: a stratification of the underlying topological
space of `X` (`Topology.Stratification`: a finite partition into locally closed subsets
following [Stacks 09XZ]) together with, for each stratum, a scheme immersed in `X` with
set-theoretic image the stratum. A sheaf on the small étale or pro-étale site of `X` is
constructible if its pullbacks to the strata of some stratification are finite locally
constant, see `AlgebraicGeometry.Etale.IsConstructibleSheaf` and
`AlgebraicGeometry.ProEtale.IsConstructibleSheaf`. -/
structure Stratification (X : Scheme.{u}) extends Topology.Stratification X where
  /-- The schemes underlying the strata. -/
  domain : Fin n → Scheme.{u}
  /-- The immersions of the strata into `X`. -/
  immersion : ∀ i, domain i ⟶ X
  isImmersion : ∀ i, IsImmersion (immersion i) := by infer_instance
  range_immersion : ∀ i, Set.range (immersion i) = stratum i

attribute [instance] Stratification.isImmersion

end AlgebraicGeometry.Scheme
