/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSupportStratumHom
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Continuity of derived Hom out of a stratum extension

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-constructible-ext-continuity-stratum.md and its proof
(blueprint: det-lem-constructible-ext-continuity-stratum).

The colimit is taken in complexes of coefficient modules, hence degreewise. Derived Hom
is taken in the ordinary unbounded derived category, using the same extension i_* u_! L
as the recorded stratum Hom lemma. The comparison is induced by the colimit cocone.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical map from the filtered colimit of Hom(a!L,K_t[q]) to Hom(a!L,K[q])
is invertible, equivalently bijective, for every integer q and every diagram with one
common strict lower bound. Here a!L is i_*u_!L placed in degree zero.

Source: blueprint stratum continuity lemma and its proof
(blueprint: det-lem-constructible-ext-continuity-stratum).
Proof for stage 3, following the nine steps of the node:
1. Closed i and the quasi-compact open uS make Z and S qcqs by
   lem-weil-pbc-qcqs-morphism-permanence. The complementary open j is qcqs as well.
2. Put Phi = L-dual tensor uS* i*. By sk-prop-sfb-cartesian-coefficients and
   sk-def-sfb-module-pushforward-pullback, inverse images are exact left adjoints,
   hence preserve colimits. On a cover L and its dual are finite free, so dual tensor
   is a finite direct sum, exact and colimit-preserving. These properties descend.
   Phi preserves the strict lower bound and distinguished triangles by
   lem-sf-exact-functor-derived-triangulated.
3. Put B(M)=Phi(M), C(M)=Phi(Rj_*j*M), and A(M)=L-dual tensor uS* R-Gamma_Z(M).
   det-lem-formal-closed-support-adjunction and det-sf-open-closed-sequence-ring-sheaf
   give the natural triangle A -> B -> C -> A[1]. Finite locally free is finite
   locally projective, so det-lem-formal-closed-support-stratum-hom identifies
   Hom(a!L,M[q]) naturally with H^q(S,A(M)). Derived global sections give a long
   exact sequence by lem-pc-right-derived-functor-triangulated and
   lem-sf-derived-homology-long-exact. The module categories are Grothendieck by
   lem-pur-ringed-site-grothendieck-abelian, with K-injective resolutions by
   lem-weil-pbc-kinjective-functorial-existence.
4. Apply det-pe-bounded-continuity-sections on the final qcqs object S to B(K_t).
   The degreewise colimit is B(K) and all complexes have strict lower bound b.
5. Apply thm-sp-truncation-e2 to j_*: its quadrant shows Rj_*j*K_t and Rj_*j*K
   have cohomology zero below b. Apply it again to global sections on S after Phi.
   This yields natural spectral sequences E2^{p,r}=H^p(S,Phi H^r(Rj_*j*K_t)).
   Naturality follows from lem-weil-pbc-truncation-triangle, then the natural
   kernel, image and quotient operations on truncation exact couples.
6. det-lem-bounded-continuity-direct-image for qcqs j identifies the filtered
   colimits of H^r(Rj_*j*K_t). Apply Phi and det-pe-bounded-continuity-sections
   on S to the degree-zero sheaves: comparison is invertible on the E2 pages.
7. Filtered colimits of abelian groups are exact by
   lem-weil-pbc-filtered-colimits-commute-finite-limits and preservation of cokernels.
   Thus comparison is invertible on every finite page. The common quadrant p>=0,
   r>=b forces stabilization at the single page max(2,r-b+2,p+1) at (p,r),
   independently of t, giving comparison on E-infinity.
8. For total degree n>=b, thm-sp-truncation-e2 gives a natural finite filtration,
   with F^0=H^n and F^{n-b+1}=0. Descending induction through its short exact
   sequences, using exact filtered colimits and the graded comparisons, gives
   comparison for H^n(S,C). For n<b both groups vanish.
9. Take the filtered colimit of the natural long exact sequences from step 3.
   In H^{q-1}(B) -> H^{q-1}(C) -> H^q(A) -> H^q(B) -> H^q(C), the four outer
   comparisons are invertible by steps 4 and 8. The five-lemma chase proves the
   middle comparison bijective. The natural Hom identification in step 3 identifies
   it with colimit.post: on each cocone leg it is postcomposition by K_t -> K,
   localized and shifted by q. This proves exactly the stated canonical comparison. -/
theorem constructibleExtContinuityStratum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {S Z V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion uS] [QuasiCompact uS]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hΛ : IsAdmissibleCoefficient Λ)
    (L : supportModules Λ S) (hL : ProEtale.IsLisseCoefficientModule Λ L)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (supportModules Λ X) ℤ)
    (b : ℤ) (hK : ∀ (t : I) (n : ℤ), n < b → IsZero ((K.obj t).X n)) (q : ℤ) :
    IsIso (colimit.post K
      (DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (supportModules Λ X)) q ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj
            ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L)))))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
