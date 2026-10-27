module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.FibrePrimesResidueFields
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg

/-!
# Residue transcendence degrees under scheme base change

Source: Stacks Project, Morphisms of Schemes, Tag 02FY, parts (2) and (3).
(blueprint: lem-sfb-scheme-base-change-residue-transcendence-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Residue transcendence degree decreases under arbitrary base change of a locally
finite type scheme morphism, and every compatible pair of points has a lift attaining
equality. The algebra structures in both clauses are induced by the indicated morphisms.

Source: Stacks Project, Morphisms of Schemes, Tag 02FY (2), (3), reducing to
Algebra, Tag 0CWE.
(blueprint: lem-sfb-scheme-base-change-residue-transcendence-lifts).

Proof:
1. Around compatible points u and b', choose affine charts Spec S over Spec R and
   Spec R' over Spec R. Locally finite type gives S finite type over R
   (`def-weil-finite-type-morphism`). Cartesian pasting and the affine spectrum tensor
   theorem (`lem-weil-pbc-cartesian-square-pasting`,
   `lem-weil-pbc-fibre-product-affine-spectra`, `def-pc-fibre-product`) identify their
   product chart with Spec C for C = S tensor_R R'. Open neighbourhoods preserve
   stalks and hence the residue fields of `def-weil-residue-field`.
2. Put k = kappa(f(u)), K = kappa(b'), A = S tensor_R k and T = A tensor_k K.
   Tensor associativity identifies T with C tensor_R' K. Apply
   `lem-weil-pbc-fibre-ring-primes-residue-fields` to both fibre rings. Points above
   b' become primes P of T, the point u becomes a prime p of A, and projection to
   u is precisely contraction P cap A = p. The residue-field identifications respect
   k and K: the tensor evaluation kernels commute with the projection maps.
3. Finite algebra generators of S give finite generators of A over k and T over K
   (`def-weil-pbc-finite-type-algebra`). Thus A and T are Noetherian
   (`lem-wf-affine-noetherian-components`). The map A to T is faithfully flat by
   `lem-weil-pbc-field-extension-base-change-faithfully-flat`, and is therefore flat
   by `def-weil-pbc-faithfully-flat-ring-map`. No finiteness on R or R' is needed.
4. Write h = dim A_p, h' = dim T_P, r = trdeg_k kappa(p), r' = trdeg_K kappa(P).
   `lem-weil-pbc-dimension-at-point-field-extension` and
   `lem-weil-pbc-dimension-at-point-local-ring-trdeg` give finite-integer equality
   h + r = h' + r'. The flat height formula `lem-weil-pbc-flat-height-formula`
   gives h' = h + e, where e is the nonnegative height of P/pT in T/pT.
   Finiteness of h' makes e finite.
5. Cancel the finite integers to obtain r = e + r', hence r' <= r. For any given
   point of the pullback the identifications in step 2 give the first clause.
6. For equality, `lem-weil-pbc-faithfully-flat-surjective-spectrum` supplies P0 above p.
   Choose P minimal over pT and contained in P0 using
   `lem-weil-pbc-prime-contains-minimal-prime`. Its contraction both contains p
   (since pT is contained in P) and is contained in p (since P is contained in P0).
   Its image in T/pT is minimal prime, hence has height zero by the prime-chain
   interpretation in `lem-weil-pbc-flat-height-formula`. Thus e = 0 and r' = r.
7. The fibre-prime correspondence in step 2 turns P into the required point of the
   product chart, with both prescribed projections and the stated residue degree.
   With no compatible pair there is no existence instance; with empty pullback
   the universal inequality is vacuous. A compatible pair always yields step 6's lift.
-/
theorem residue_trdeg_base_change_le_and_exists_eq
    {U B B' : Scheme.{u}} (f : U ⟶ B) [LocallyOfFiniteType f] (g : B' ⟶ B) :
    (∀ u' : (pullback f g : Scheme.{u}),
      @Algebra.trdeg (B'.residueField ((pullback.snd f g) u'))
          ((pullback f g).residueField u') _ _
          (((pullback.snd f g).residueFieldMap u').hom.toAlgebra) ≤
        @Algebra.trdeg (B.residueField (f ((pullback.fst f g) u')))
          (U.residueField ((pullback.fst f g) u')) _ _
          ((f.residueFieldMap ((pullback.fst f g) u')).hom.toAlgebra)) ∧
    (∀ (u : U) (b' : B'), g b' = f u →
      ∃ u' : (pullback f g : Scheme.{u}), (pullback.fst f g) u' = u ∧
        (pullback.snd f g) u' = b' ∧
        @Algebra.trdeg (B'.residueField ((pullback.snd f g) u'))
            ((pullback f g).residueField u') _ _
            (((pullback.snd f g).residueFieldMap u').hom.toAlgebra) =
          @Algebra.trdeg (B.residueField (f u)) (U.residueField u) _ _
            ((f.residueFieldMap u).hom.toAlgebra)) := by
  sorry

end AlgebraicGeometry
