/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.Paper.KunBcMapOnCohomology
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Sheaf.AlgebraicGeometry.EtaleInverseImageColimits
import Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.StalkFaithfulDerived
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure

/-!
# Base change towards spectra of fields

Source: Stacks Project, Tag 0F1I (blueprint: lem-kun-0f1i).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Base change for torsion étale sheaves along a finite-type scheme over a field.
Source: Stacks Project, Tag 0F1I (blueprint: lem-kun-0f1i).

Proof, following the eight steps of the node:

1. By lem-kun-unbounded-exchange-agrees and lem-kun-bc-map-on-cohomology, the exchange
at F[0] induces the usual degree-q exchange on abelian sheaves. Negative degrees vanish.
By lem-weil-pbc-unbounded-derived-iso-cohomology it suffices to prove these maps are
isomorphisms for all nonnegative q.
2. By lem-kun-invertible-orders-colimit, F is the filtered colimit of its n-torsion
subsheaves over positive n invertible in K, ordered by divisibility. The index is
nonempty (it contains 1), and nm is a common upper bound of n and m. Inverse image
preserves annihilation by n by prop-weil-pbc-inverse-image-exact. The base change h
of g is qcqs by lem-weil-pbc-qcqs-morphism-permanence. Apply
lemma-weil-pbc-direct-image-filtered-colimit to g and h and
lem-weil-pbc-inverse-image-preserves-colimits to the inverse images. Naturality identifies
the original exchange with the colimit of the n-torsion exchanges. It therefore suffices
to prove the assertion when nF = 0 for a fixed positive n invertible in K.
3. Choose an algebraic closure of K (def-weil-algebraic-closure). By lem-kun-0f1c,
both direct images commute with this base change. The two comparisons identify the
pulled-back exchange with the new exchange: paste the inverse-image squares using
lem-weil-pbc-derived-square-iso-pasting, and take mates using lem-weil-pbc-mate-pasting.
Finite type is preserved by lem-weil-pbc-lft-base-change and
lem-weil-pbc-qcqs-morphism-permanence.
4. Every geometric point lifts to this base change, since its algebraically closed
field admits an extension of the ground-field map from the algebraic closure, by
lem-weil-pbc-algebraic-extension-embeds-algebraically-closed. Use
lem-weil-pbc-derived-inverse-image-composition and lem-kun-stalk-faithful-derived to
deduce conservativity. We may thus assume K algebraically closed.
5. Replace X by its reduction using lem-weil-pbc-reduction-universal-homeomorphism,
lem-weil-pbc-universal-homeomorphism-base-change and
thm-weil-pbc-universal-homeomorphism-invariance. The resulting equivalences preserve the
inverse-image square, its adjunction counit and hence its exchange mate
(def-kun-unbounded-exchange). Finite type survives reduction because quotients of
finitely generated K-algebras are finitely generated. We may assume X reduced.
6. An algebraically closed field is perfect. By lem-kun-geometric-reduced-perfect,
the reduced finite-type X is flat and finitely presented with geometrically reduced
fibres. Apply lem-weil-pbc-flat-morphism-base-change and
lem-weil-pbc-qcqs-morphism-permanence after every base change. Then lem-kun-0eys gives
degree-zero base change universally, hence BC(f,n,0) of def-kun-bc-property.
7. Induct on q. If BC(f,n,q-1) holds but BC(f,n,q) fails, lem-kun-0f1d supplies an
affine integral normal K-scheme with algebraically closed function field L and d dividing
n for which the degree-q direct image of the constant Z/dZ sheaf along the generic-fibre
projection is nonzero. Lemma lem-kun-0f1i-normal gives its vanishing, a contradiction.
Thus BC(f,n,q) holds for every q, for all base changes and all n-annihilated abelian sheaves.
8. Undo reduction and the algebraic-closure extension, then take the filtered colimit
from step 2. All nonnegative cohomology exchanges are isomorphisms; negative degrees
vanish. Step 1 and lem-weil-pbc-unbounded-derived-iso-cohomology conclude. -/
theorem baseChange_towardsSpecField
    {K : Type u} [Field K]
    {X S' T : Scheme.{u}}
    (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [S'.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    (g : T ⟶ S') [g.IsOver (Spec (.of K))]
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F) :
    IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
        (g := g)).symm)).app
      ((DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := sorry

end AlgebraicGeometry.Etale
