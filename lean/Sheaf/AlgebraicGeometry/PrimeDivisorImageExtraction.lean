module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.FieldTheory.AbhyankarInequality
import Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint

/-!
# Extracting the image of a prime divisor

Source: Milne, *Algebraic Groups* (2017), Proposition 8.25, p. 154, referring to
Milne, *A Proof of the Barsotti-Chevalley Theorem on Algebraic Groups* (2013),
Lemma 4.4, pp. 8--9; the node's normal and supported modification refinement
(blueprint: lem-sfb-prime-divisor-image-extraction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper birational modification, unchanged away from a prescribed closed subset,
makes the image of a prime divisor a divisor. Normality is the explicit stalk condition
in the source node. The partial isomorphism is required to be induced by `b`, and `F`
represents its rational lift on the maximal domain. The integral closed immersion `j`
with the specified image is precisely the reduced induced closed subscheme of that image.

Source: Milne, *Algebraic Groups* (2017), Proposition 8.25, p. 154, and Milne (2013),
Lemma 4.4, pp. 8--9, with the supported-model refinement in the node
(blueprint: lem-sfb-prime-divisor-image-extraction).

Proof:
1. Set m = dim V, n = dim P, L = k(V), K = k(P). Dominance embeds K in L.
   By lem-sc-integral-function-field-affine-fraction, affine charts have these fraction
   fields; finite type makes them finitely generated. The source is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Normality and codimension one make
   A = O_{V,eta_T} a DVR by lem-sc-normal-dim1-dvr and def-sc-discrete-valuation-ring.
   Its residue field is k(T). By lem-kun-dimension-formula and
   lem-weil-pbc-dense-open-dimension-comparison the transcendence degrees over k of
   L, K, k(T) are m, n, m-1 respectively.
2. The point p = f(eta_T) is nongeneric because it lies in the proper closed set Z.
   An affine domain chart B at p embeds locally in A. A nonzero element of its nonzero
   prime at p has positive valuation. Thus the restricted valuation w on K is nontrivial.
   Its ring R = A intersect K is centred at p. Its nonzero value group is eZ; taking
   least values of nonzero ideals shows R is a local PID and not a field, hence a DVR
   (def-sc-discrete-valuation-ring). Its residue field embeds in k(T).
3. By lem-trf-abhyankar-inequality, trdeg_{k(R)} k(T) is at most trdeg_K L.
   Apply lem-sbc-transcendence-degree-tower twice to get trdeg_k k(R) at least n-1.
   The nongeneric point p implies n is at least one. Lift n-1 algebraically independent
   residue elements to elements h_i of R, allowing an empty family when n = 1.
4. Apply lem-sfb-supported-valuation-finite-elements-model to P, Z, R and the h_i.
   It gives a proper birational Q over P, unchanged outside Z, and a centre q where the
   h_i are regular. By lem-weil-pbc-proper-composition Q is proper over k. Its function
   field K and lem-kun-dimension-formula with
   lem-weil-pbc-dense-open-dimension-comparison give dim Q = n.
5. Normalize Q in K using lem-weil-pbc-normalization-in-residue-field-extension at its
   generic point with the identity residue extension. By lem-sc-normalization-properties
   this gives a normal integral P', finite birational over Q, proper, of dimension n,
   and unchanged over the normal open P minus Z. Composition gives b, by
   lem-weil-pbc-proper-composition. The inverse of b there gives the rational lift of f.
   By lem-sfb-rational-map-extension-valuation-point it extends across eta_T, whose
   local ring is the DVR A. Take its maximal representative F and denote its value by x'.
6. The maps Spec A to Q from F and from Spec A to Spec R to Q agree generically.
   By lemma-nagata-separated-valuation-lift-unique they agree, so x' maps to q.
   Thus the h_i remain algebraically independent in the residue field at x', giving
   transcendence degree at least n-1. Since b(x') = p lies in Z, x' is nongeneric,
   and its local dimension is at least one. The dimension formula and
   lem-weil-pbc-dense-open-dimension-comparison force its residue transcendence degree
   to be exactly n-1.
7. Every point of T in the domain specializes from eta_T, which belongs to the domain.
   Continuity identifies the image closure with the closure of x'. By
   lem-weil-pbc-reduced-induced-closed-subscheme it has a reduced integral closed
   subscheme structure D with generic residue field k(x'). The generic dimension formula
   and lem-weil-pbc-dense-open-dimension-comparison give dim D = n-1. Since the inverse
   image of Z is closed and contains x', it contains D. -/
theorem exists_prime_divisor_image_extraction
    {k : Type u} [Field k] [IsAlgClosed k]
    (V P T : Scheme.{u}) [IsIntegral V] [IsIntegral P] [IsIntegral T]
    (aV : V ⟶ Spec (.of k)) [IsSeparated aV]
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (aP : P ⟶ Spec (.of k)) [IsProper aP]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (hP : ∀ x : P, IsDomain (P.presheaf.stalk x) ∧
      IsIntegrallyClosed (P.presheaf.stalk x))
    (f : V ⟶ P) [IsDominant f] (hf : f ≫ aP = aV)
    (i : T ⟶ V) [IsClosedImmersion i]
    (hcodim : ringKrullDim (V.presheaf.stalk (i (genericPoint T))) = 1)
    (Z : TopologicalSpace.Closeds P) (hZ : Z ≠ ⊤)
    (himage : Set.range (i ≫ f) ⊆ (Z : Set P)) :
    ∃ (P' : Scheme.{u}) (b : P' ⟶ P),
      IsIntegral P' ∧
      (∀ x : P', IsDomain (P'.presheaf.stalk x) ∧
        IsIntegrallyClosed (P'.presheaf.stalk x)) ∧
      IsProper (b ≫ aP) ∧ IsProper b ∧ IsIso (b ∣_ Z.compl) ∧
      (∃ e : P'.PartialIso P, e.iso.hom ≫ e.target.ι = e.source.ι ≫ b) ∧
      ∃ F : V.PartialMap P',
        F.domain = F.toRationalMap.domain ∧
        F.hom ≫ b = F.domain.ι ≫ f ∧ i (genericPoint T) ∈ F.domain ∧
        ∃ (D : Scheme.{u}) (j : D ⟶ P'),
          IsClosedImmersion j ∧ IsIntegral D ∧
          Set.range j = closure (F.hom '' {x | F.domain.ι x ∈ Set.range i}) ∧
          Set.range j ⊆ b ⁻¹' (Z : Set P) ∧
          topologicalKrullDim D + 1 = topologicalKrullDim P := by
  sorry

end AlgebraicGeometry
