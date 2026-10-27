module

public import Sheaf.RingTheory.Bialgebra.DistributionAlgebra
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Lie.UniversalEnveloping

import Sheaf.RingTheory.HopfAlgebra.AugmentationMonomialPairing
import Sheaf.Algebra.Lie.FieldFilteredPBW

/-! # The characteristic-zero distribution and enveloping algebra comparison

Source: Milne, Algebraic Groups (2017), Section 10l, printed p.208,
using Lemma 11.27, printed p.218, and Theorem 10.36, printed pp.200--204.
(blueprint: lem-sfb-characteristic-zero-distribution-enveloping)

All coordinate algebras are the actual global sections with their canonical
Hopf structure. Tangent vectors are counit derivations with the convolution
commutator, identified with invariant derivations by the imported calculus.
The maps in the naturality square are characterized on every functional or
on every enveloping generator; these characterizations determine them uniquely.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Bialgebra
open AlgebraicGeometry.RationalHighestWeight

namespace AlgebraicGeometry

/-- The unital algebra isomorphism extending the identity on tangent functionals,
and its naturality for all homomorphisms of smooth affine finite-type groups.
No connectedness or semisimplicity hypothesis is imposed.

Source: Milne, Algebraic Groups (2017), Section 10l, printed p.208,
using Lemma 11.27, printed p.218, and Theorem 10.36, printed pp.200--204.
(blueprint: lem-sfb-characteristic-zero-distribution-enveloping)

Proof:
1. The coordinate Hopf algebra has the multiplication comap as comultiplication
   and identity evaluation as counit. Apply
   lem-sfb-bialgebra-distribution-tangent-calculus: its distribution algebra is
   the union of the duals of C/I^(n+1), and its tangent bracket is the commutator
   of invariant derivations, also the convolution commutator.
2. Map a tensor word to the convolution product of its tangent letters, and the
   empty word to the counit. The Lie relations vanish by step 1, so the tensor
   quotient gives the unital algebra map. Values on generators determine it.
3. Choose a cotangent basis and its dual tangent basis. Apply
   lem-sfb-hopf-augmentation-monomial-pairing and lem-sfb-field-filtered-pbw.
   The ordered PBW words and the coordinate monomials give the two degree bases.
   Characteristic zero makes every degree factorial nonzero.
4. Restriction F_n to (I^n/I^(n+1)) dual is surjective with kernel F_(n-1), by
   extending a linear functional on a subspace. The order estimate makes the map
   filtered, and the factorial pairing gives diagonal nonzero degree matrices.
   At degree zero the map is the identification k with k times the counit.
5. Induct on n in the two short exact filtration sequences. Quotient bijectivity
   and the preceding-degree bijectivity prove both injectivity and surjectivity
   at degree n. Take the exhaustive unions. Dimension zero is included: its
   positive-degree quotient bases are empty.
6. For f:G to H, q=f* commutes with counit and comultiplication. Thus q takes
   the augmentation ideal of H into that of G and precomposition preserves
   orders and convolution. On tangent vectors it is df(v)=v q and preserves
   brackets. The tensor quotient therefore induces U(df). Both composites send
   each generator to v q, so agree on all tensor words and hence the quotient.
   These arguments use neither connectedness nor semisimplicity. -/
theorem characteristicZero_distribution_enveloping
    (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    ∃ ΘG : UniversalEnvelopingAlgebra k (tangentLieAlgebra k (coordinateAlgebra G)) ≃ₐ[k]
        distributionAlgebra k (coordinateAlgebra G),
      (∀ (v : tangentLieAlgebra k (coordinateAlgebra G)) (c : coordinateAlgebra G),
        (ΘG (UniversalEnvelopingAlgebra.ι k v)).val c = v.val c) ∧
      ∀ (H : Grp (Over (Spec (.of k)))) [IsAffine H.X.left]
        [Smooth H.X.hom] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom],
        ∃ ΘH : UniversalEnvelopingAlgebra k (tangentLieAlgebra k (coordinateAlgebra H)) ≃ₐ[k]
            distributionAlgebra k (coordinateAlgebra H),
          (∀ (v : tangentLieAlgebra k (coordinateAlgebra H)) (c : coordinateAlgebra H),
            (ΘH (UniversalEnvelopingAlgebra.ι k v)).val c = v.val c) ∧
          ∀ f : G ⟶ H,
            ∃ (push : distributionAlgebra k (coordinateAlgebra G) →ₐ[k]
                distributionAlgebra k (coordinateAlgebra H))
              (df : tangentLieAlgebra k (coordinateAlgebra G) →ₗ⁅k⁆
                tangentLieAlgebra k (coordinateAlgebra H))
              (Udf : UniversalEnvelopingAlgebra k (tangentLieAlgebra k (coordinateAlgebra G))
                →ₐ[k] UniversalEnvelopingAlgebra k (tangentLieAlgebra k (coordinateAlgebra H))),
              (∀ (a : distributionAlgebra k (coordinateAlgebra G)) (c : coordinateAlgebra H),
                (push a).val c = a.val (coordinateMap f c)) ∧
              (∀ (v : tangentLieAlgebra k (coordinateAlgebra G)) (c : coordinateAlgebra H),
                (df v).val c = v.val (coordinateMap f c)) ∧
              (∀ v : tangentLieAlgebra k (coordinateAlgebra G),
                Udf (UniversalEnvelopingAlgebra.ι k v) =
                  UniversalEnvelopingAlgebra.ι k (df v)) ∧
              push.comp ΘG.toAlgHom = ΘH.toAlgHom.comp Udf := by
  sorry

end AlgebraicGeometry
