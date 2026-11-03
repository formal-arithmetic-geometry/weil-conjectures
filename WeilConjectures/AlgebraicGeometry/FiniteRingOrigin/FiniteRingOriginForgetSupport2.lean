/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1CompactificationFibre.P1CompactificationFibre
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Polynomial.Laurent
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Origin-normalized compact support for arbitrary finite coefficient rings

Source: blueprint sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2; released repair note of 2026-11-01
(blueprint: lem-pur-finite-origin-forget-support).

The definitions use the published Kummer splice, compactification and comparison
maps. The coefficient ring is an arbitrary finite commutative ring; no
PurityFiniteSetting is used in these statements.
The origin-normalized proof route retains its recorded BLUEPRINT QUESTION.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale AlgebraicGeometry.Etale.P1CompactificationFibre

namespace AlgebraicGeometry.Etale.FiniteRingOrigin


/-- Restriction along the etale subsite identifies the two supported-section
kernels, uniquely compatibly with their inclusions into global sections.
Source: Stacks 099R and 09XP, blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support).
Proof: comparison direct image is restriction to the etale subsite. The terminal
object and the open complement are unchanged. The global-sections comparison
intertwines their restriction maps. Kernel functoriality gives an isomorphism;
the monic kernel inclusion determines it uniquely and proves naturality. -/
theorem supportKernelComparison_existsUnique (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ∃! e : ProEtale.comparisonLowerStar (C A) T ⋙ globalSectionsWithSupport (C A) i ≅
        ProEtale.globalSectionsWithSupport (C A) i,
      ∀ G : Sheaf (Scheme.ProEt.topology T) (C A),
        e.hom.app G ≫ (Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
          (op (Scheme.ProEt.mk i.openComplement.ι))).app G =
        (Sheaf.ΓSupportι T.smallEtaleTopology (C A)
          (op (Scheme.Etale.mk i.openComplement.ι))).app
            ((ProEtale.comparisonLowerStar (C A) T).obj G) ≫
          (ProEtale.comparisonLowerStarCompGlobalSectionsIso (C A) T).hom.app G := by
  sorry

end AlgebraicGeometry.Etale.FiniteRingOrigin
