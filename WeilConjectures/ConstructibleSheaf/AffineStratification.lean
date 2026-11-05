/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Immersed strata over affine schemes

A locally closed subset of an affine scheme `Spec R` is the image of an immersion
(`AlgebraicGeometry.Scheme.exists_isImmersion_range_eq_of_isLocallyClosed`), so a stratification
of the underlying space of `Spec R` is the underlying stratification of a scheme stratification
(`AlgebraicGeometry.Scheme.Stratification.ofAffine`). With the descent of stratifications to a
finitely generated subring, every stratification of `Spec A` comes from a scheme stratification
of a Noetherian affine scheme (`AlgebraicGeometry.exists_finset_schemeStratification`), which is
the stratification part of Step 2 of `lem-weil-pbc-constructible-finite-pushforward-approximation`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
