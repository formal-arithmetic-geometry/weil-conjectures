/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Effective fppf descent for separated locally quasi-finite schemes

Source: Stacks Project, More on Morphisms, Tag 02W8,
`lemma-separated-locally-quasi-finite-morphisms-fppf-descend`
(blueprint: lem-trf-separated-lqf-fppf-effective-descent).

The covering-family scheme descent datum and its geometric effectivity are the existing
`AlgebraicGeometry.SchemeCoverDescentDatum` and
`AlgebraicGeometry.SchemeCoverDescentDatum.IsEffective` interfaces. The theorem below
states that an fppf covering datum whose local structure morphisms are separated and
locally quasi-finite is effective. No quasi-compactness or local finite-presentation
hypothesis on the local structure morphisms is included.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Effective fppf descent for separated locally quasi-finite schemes.

Source: Stacks Project, More on Morphisms, Tag 02W8,
`lemma-separated-locally-quasi-finite-morphisms-fppf-descend`
(blueprint: lem-trf-separated-lqf-fppf-effective-descent).
The proof follows Tag 02W8. First, separatedness and local quasi-finiteness are invariant
under base change and are stable for the finite coproducts used in the fppf-family
reduction, including the empty coproduct. The fppf-family effectivity reduction then
reduces to a single flat surjective finite-presentation morphism of affine schemes.
For each affine open in the local scheme, its saturated image is open and quasi-compact;
the cocycle makes these opens invariant. Restriction preserves separatedness and local
quasi-finiteness, and the quasi-compact separated locally quasi-finite morphisms are
quasi-affine. Effective descent for quasi-affine data on the fpqc singleton, followed
by gluing over the invariant open cover, gives effectivity of the original datum.
-/
theorem separated_lqf_fppf_effective_descent
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (D : SchemeCoverDescentDatum f)
    (hsep : ∀ i, IsSeparated (D.localScheme i).hom)
    (hlqf : ∀ i, Scheme.Hom.IsLocallyQuasiFinite (D.localScheme i).hom) :
    D.IsEffective := by
  sorry

end AlgebraicGeometry
