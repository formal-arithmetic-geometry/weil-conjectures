/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.DerivedExchangeBoundedComparison
import WeilConjectures.AlgebraicGeometry.DerivedExchangeUnboundedTransport

/-!
# Termwise construction of the derived exchange morphism

Source: Stacks Project, `sites-cohomology.tex`, Lemma 0736 and Remark 07A7;
`derived.tex`, Lemmas 070I, 070K and 0DVC. The comparison between these constructions
is the blueprint's explicit argument (blueprint: lem-weil-pbc-derived-exchange-termwise).

## Main statements

* `AlgebraicGeometry.derivedExchangeTermwise`: computation on arbitrary K-injective
  resolutions, including resolutions that are not bounded below as complexes.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

end AlgebraicGeometry
