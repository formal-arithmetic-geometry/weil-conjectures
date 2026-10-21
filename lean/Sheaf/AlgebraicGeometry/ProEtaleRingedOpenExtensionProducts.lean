/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation

/-!
# Products of ringed pro-etale open extensions

Source: Stacks Project, Pro-etale Cohomology, Tag 09BP (lemma-j-shriek-limits),
with arbitrary ring-sheaf coefficients via ringed recollement
(blueprint: lem-cbc-ringed-open-extension-products).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- For a quasi-compact open immersion, the canonical product comparison for extension
by zero of module sheaves is invertible and natural in maps of families.

The open site is presented as the slice at `U`, as in `ProEt.weaklyEtale_localization`.
The coefficient sheaf is `(proEtaleModuleCoefficients R).over U`; the functor
`proEtaleRingedExtensionByZero U R` is the recorded extension presheaf followed by
module sheafification. `piComparison` has components the images of the projections.
Products are Mathlib's sectionwise module-sheaf limits. The index type may be empty.
No quasi-compactness or quasi-separatedness condition is imposed on `X`.

Source: Stacks Project, Tag 09BP, using Tags 09AA, 09AG, 09AH and 09BN
(blueprint: lem-cbc-ringed-open-extension-products).

Proof plan:
1. Use `reduced_induced_closed_subscheme` for the closed complement of `U.hom`.
   Apply `proEtale_ringed_open_closed` to obtain the open restriction isomorphism,
   closed restriction vanishing, exactness and the localization short exact sequence.
2. Form the specified comparison `c` using the sectionwise products of
   `SheafOfModules.hasLimitsOfSize`. Open inverse image preserves products by
   `proEtale_immersion_inverseImage_preservesLimits`. Naturality of the open restriction
   isomorphism identifies the open restriction of `c` with an isomorphism: after
   projecting to each factor its composite is the restriction isomorphism on the product.
3. Closed inverse image also preserves products by the same immersion theorem. Both
   restrictions of the source and target to the closed complement are zero, since
   closed restriction annihilates extension by zero. Thus the closed restriction of
   `c` is invertible. This includes the empty product, which is the zero module sheaf.
4. Both inverse images are exact. The kernel and cokernel of `c` therefore have zero
   open and closed restrictions. The localization sequence makes each zero, using
   exactness of extension by zero and closed direct image. Hence `c` is invertible.
5. For a family map `a`, project the naturality square to factor `s`. Both paths are
   extension by zero applied to the projection followed by `a s`, by functoriality.
   Product uniqueness gives the displayed equality. For an empty family both products
   are terminal zero objects and extension by zero preserves zero by exactness.
   The same formulas cover an empty open or scheme, the identity open, and zero rings. -/
theorem proEtaleRingedExtensionByZero_products {X : Scheme.{u}} (U : X.ProEt)
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (S : Type (u + 1))
    (F : S → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) :
    IsIso (piComparison (proEtaleRingedExtensionByZero U R) F) ∧
      ∀ (G : S → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U))
        (a : ∀ s : S, F s ⟶ G s),
        (proEtaleRingedExtensionByZero U R).map (Limits.Pi.map a) ≫
            piComparison (proEtaleRingedExtensionByZero U R) G =
          piComparison (proEtaleRingedExtensionByZero U R) F ≫
            Limits.Pi.map (fun s ↦ (proEtaleRingedExtensionByZero U R).map (a s)) := by
  sorry

end AlgebraicGeometry.Scheme
