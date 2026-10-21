/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# An integral lattice on a nonempty reduced open

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
first paragraph, and Stacks Tag 03S0.
(blueprint: lem-weil-pbc-lisse-lattice-reduced-open)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- A lisse rational coefficient module has a lisse integral lattice on a nonempty
quasi-compact open of a nonempty reduced noetherian finite-dimensional scheme.
The coefficient type `WithAbs` equips the field with its canonical extended p-adic
absolute value; `latticeCoefficientIntegers` is its ring of integers. The ringed
pullback along the open immersion is `j⁻¹ L`, with its coefficient action identified
by the canonical continuous-function comparison. No constant or positive rank is required.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph; Stacks Tags 03S0 and 0356.
(blueprint: lem-weil-pbc-lisse-lattice-reduced-open)

Proof plan:
1. Pro-etale localization identifies restriction to an open with slice restriction.
   Continuous coefficients restrict to the same continuous functions, finite free
   presentations restrict, and the ringed-topos tensor comparison restricts lattice pairs.
2. Etale-local lattice existence gives a covering with integral lattices. Since X is
   nonempty, choose a nonempty member and then a nonempty affine open B in that member.
3. The image W of B in X is nonempty and open, since etale maps are open. The map B to W
   is etale and surjective. Noetherian-open permanence makes W noetherian and qcqs;
   the affine B is qcqs as well.
4. Apply Stacks 03S0 to obtain a finite locally closed partition of W on which B is finite
   etale. Choose a minimal subfamily of closures covering W. The complement of all but
   one closure is nonempty open inside the remaining closure; intersect its open dense
   stratum to obtain a nonempty open U contained in that stratum.
5. U is reduced. Factor the stratum immersion as closed followed by open; the
   reduced-source factorization theorem gives an actual map U to the stratum.
6. Base change to U gives a finite etale surjection B_U to U. The projection to B is open,
   so the lattice on B restricts to B_U. The object inverse-image restriction theorem and
   inverse-image composition comparison identify its rationalization with the pullback of L.
7. U is noetherian, hence topologically noetherian by a finite noetherian affine cover.
   Finite-etale lattice descent gives M on U with the required rationalization. Every
   inverse image of an affine open of X is a noetherian open, hence quasi-compact, so
   the open immersion is quasi-compact. This argument includes varying ranks and rank zero. -/
theorem exists_lisse_lattice_reduced_open
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X] [IsReduced X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (L : ringedSiteModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (_hL : L.IsFiniteLocallyFree) :
    ∃ U : X.Opens, Nonempty U ∧ QuasiCompact U.ι ∧
      ∃ M : ringedSiteModules.{u + 1}
          (latticeModuleRing U.toScheme (latticeCoefficientIntegers l E)),
        M.IsFiniteLocallyFree ∧
        Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (integralLatticeCoefficientMap U.toScheme l E) M ≅
          continuousModulePullback U.ι
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L) := by
  sorry

end AlgebraicGeometry.ProEtale
