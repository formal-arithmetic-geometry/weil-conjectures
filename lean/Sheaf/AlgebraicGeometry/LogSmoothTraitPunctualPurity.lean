/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.PunctualPurity

public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart
import Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity
import Sheaf.AlgebraicGeometry.PunctualPurityEtaleLocality

/-!
# Punctual purity for regular log smooth schemes over a trait

Source: ILO, Exposé XVI, Theorem 3.6.2, printed p.252, and its final reduction on p.253
(blueprint: lem-per-log-smooth-trait-punctual-purity).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A regular Noetherian fs log scheme log smooth over a trait with its canonical
log structure is punctually pure for the prime coefficient field.
Source: ILO XVI Theorem 3.6.2, pp.252--253
(blueprint: lem-per-log-smooth-trait-punctual-purity).

Proof plan:
1. Refine the log-smooth charts using ILO XVI 3.6.3 to compatible uniformizer
   charts with injective group map. At each point apply
   lem-per-regular-log-smooth-monomial-chart (ILO XVI 3.6.5).
   It gives an etale neighbourhood U of the point and an etale trait morphism from U
   to the monomial model with a nonzero exponent tuple. The trait is unchanged.
2. By lem-per-monomial-trait-punctual-purity (ILO XVI 3.5.12) that model is regular
   Noetherian and punctually pure, with the given prime invertible. Apply
   lem-per-punctual-purity-etale-locality to the second etale arrow to deduce purity of U.
   No exponent is required to be prime to the coefficient characteristic.
3. Apply lem-per-punctual-purity-etale-locality to U → V and the chosen point over v.
   This identifies the actual normalized Kummer classes at their local spectra.
   Since v was arbitrary, V is punctually pure; for empty V the condition is vacuous.
-/
theorem log_smooth_trait_punctual_purity (ℓ : ℕ) (hℓ : ℓ.Prime)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsUnit (ℓ : R)) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (M : EtaleLogStructure (Spec (.of R))) (hfs : M.IsFineSaturated)
    (hcanonical : ∃ e : M.monoidSheaf.obj ≅ divisorialLogPresheaf
        ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π)).ι,
      e.hom ≫ divisorialStructuralMap
        ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π)).ι = M.alpha)
    (V : FineSaturatedLogScheme.{u}) [IsNoetherian V.scheme]
    (hV : IsRegularScheme V.scheme)
    (f : EtaleLogHom V ⟨Spec (.of R), inferInstance, M, hfs⟩)
    (hf : f.IsLogSmooth) : IsPunctuallyPure ℓ hℓ V.scheme := by
  sorry

end AlgebraicGeometry.Etale
