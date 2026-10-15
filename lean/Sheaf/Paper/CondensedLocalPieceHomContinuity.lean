/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.CondensedConstructiblePiece
public import Sheaf.CategoryTheory.HomColimitExtension
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Algebra.Homology.LocallyFreeDerivedHom
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Filtered Hom continuity for one locally closed piece -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Extension by zero of a locally finitely presented condensed field module has
filtered derived Hom continuity on uniformly bounded below complexes.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), locally free and costalk steps.
(blueprint: lem-weil-pbc-condensed-local-piece-hom-continuity)

Proof: write the piece as i_*j_!P[0], where i is closed and j is a quasi-compact open.
The noetherian closed subscheme and its open are qcqs. Local finite presentation over
these condensed finite field coefficients gives pro-etale local finite freeness.
The derived Hom formula identifies Hom(P[0],L[n]) with the nth cohomology of derived
sections of P∨ tensor L. Tensor with a finite locally free dual is exact, commutes
with filtered colimits, and preserves the common lower bound. Apply qcqs global
sections continuity to this diagram. Transport the ringed-site module formulation of
this formula to internal module objects with the same coefficient ring and evaluation
pairing. The good-truncation cocone used by continuity maps termwise quasi-isomorphically
to the original cocone; exact filtered colimits preserve this comparison.
For the ambient diagram, adjunction identifies
Hom(i_*j_!P[0],N[n]) with Hom(P[0],j^*Ri^!N[n]). Recollement expresses i_*Ri^!N as
Cone(N → Rk_*k^*N)[-1] for the complementary quasi-compact open k. Qcqs pushforward
continuity and exact filtered colimits show that this cone commutes with the filtered
colimit. The same recollement gives the common lower bound for Ri^!N; exact j^*
also preserves it. Functorial bounded injective resolutions and good truncations give
strict uniformly bounded below diagrams representing these derived images and their
colimits. Include the bounded below derived categories in the ordinary derived categories
when applying adjunction. Apply the locally free calculation to j^*Ri^!N. Naturality of the
adjunction and of evaluation identifies every leg with the original cocone leg.
An isomorphism of the first argument transports the resulting isomorphism. -/
theorem condensed_local_piece_hom_continuity
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)) :
    condensedConstructiblePiece T ℓ E ≤
      homColimitProperty (N ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone (colimit.cocone N)) := by
  sorry

end AlgebraicGeometry.ProEtale
