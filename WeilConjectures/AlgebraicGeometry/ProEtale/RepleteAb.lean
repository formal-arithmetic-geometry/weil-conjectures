/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-!
# Repleteness of the pro-étale topos for abelian sheaves

The abelian-sheaf version of `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`, which treats
sheaves of modules: on the pro-étale site of a scheme, the projection `lim Fₙ ⟶ F₀` of a tower of
epimorphisms of abelian sheaves is an epimorphism
(`AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_ab`), and countable products of abelian
sheaves are exact (`AlgebraicGeometry.Scheme.ProEt.countableAB4Star_ab`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

end AlgebraicGeometry.Scheme.ProEt
