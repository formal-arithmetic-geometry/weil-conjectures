/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.SixFunctors.Etale.Gabber
import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-! # Short-exact devissage with constructible outer terms

Source: Stacks Project, Lemma 0A5C. The proof specializes the existing proof in
Curve.Reductions; this standalone module avoids its import of ConstructiblePrimeDevissage.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry
