/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Reduced graph closure of a projective generic map

Source: Stacks Project, Tags 01J3, 01TE and 02NW; the agent expansion of de Jong (1996),
Section 4.17, pp. 71--72, used in de Jong (1997), Lemma 3.7, p. 608
(blueprint: lem-sfb-projective-generic-map-graph-alteration).

The reduced induced closed subscheme is specified by its defining properties: a reduced
closed immersion with image the closure of the indicated point. Tag 01J3, recorded as
`Scheme.IdealSheafData.reduced_induced_closed_subscheme`, identifies this with the canonical
vanishing-ideal construction, uniquely over the ambient product. Generic stalk isomorphisms
specify the function-field identifications without choosing a different generic point.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The reduced closure of the graph of a projective generic map gives a proper surjective
model with the prescribed generic fibre and function field.

Source: Stacks Project, Tags 01J3, 01TE, 01RV, 01RW and 02NW; de Jong (1996), Section 4.17,
pp. 71--72, and de Jong (1997), Lemma 3.7, p. 608.
(blueprint: lem-sfb-projective-generic-map-graph-alteration)

Proof (the seven steps of the node):
1. The closure of the graph point is nonempty irreducible. The reduced-induced-subscheme
   theorem (lem-weil-pbc-reduced-induced-closed-subscheme) makes its reduced closed model
   integral (def-pc-integral-scheme). On an affine chart Spec R the graph map has kernel p;
   its factorization through R/p glues on overlaps, giving jT and jT followed by i = (a,j).
2. Over a nonempty affine Spec A in N and a chart Spec B of T, generic evaluation gives
   A ⊆ B ⊆ L = Frac A. Thus Frac B = L. The affine function-field lemma
   (lem-sc-integral-function-field-affine-fraction) identifies the generic stalk of T with L.
   Its compatibility with j and q identifies the induced extension with L/K.
3. For each such chart, multiplication B ⊗[A] L → L is an isomorphism, with inverse
   λ ↦ 1 ⊗ λ: writing c = a/s gives c ⊗ λ = 1 ⊗ (aλ/s). The affine fibre-product formula
   (lem-weil-pbc-fibre-product-affine-spectra) glues these inverses. This proves that the
   square with jT, the identity of Spec L, b and j is Cartesian, equivalently the specified
   induced map Spec L → T ×[N] Spec L is an isomorphism over L.
4. The two projection equations give b composed with jT = j and m composed with jT = a
   (def-pc-fibre-product).
5. Projectivity implies properness (lem-kun-projective-implies-proper), which survives
   base change and restriction to a closed subscheme (lem-weil-pbc-proper-base-change,
   lem-weil-pbc-closed-immersion-proper). Thus b is proper. Its closed image contains
   the generic point of N, and hence all of N, proving surjectivity.
6. A finite map is proper (lem-weil-pbc-finite-proper); composition of proper maps is proper
   (lem-weil-pbc-proper-composition). Hence r = b followed by q is proper and surjective.
   Properness gives finite type and a quasi-compact diagonal, hence quasi-separatedness.
7. Associativity of fibre products and the given generic-fibre square for q identify the
   generic fibre of r with Spec L. Its point set is a singleton (def-pc-scheme-fibre).
   The field spectrum is Noetherian, so S is Noetherian by finite type
   (lem-weil-pbc-finite-type-over-noetherian). Apply the generic finite neighbourhood lemma
   (lem-weil-pbc-generic-finite-morphism-open-neighborhood) to get the dense open V.
-/
theorem projective_generic_map_graph_alteration
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (S N M : Scheme.{u}) [IsIntegral S]
    (s : S ⟶ Spec (CommRingCat.of k)) [IsSeparated s]
    [LocallyOfFiniteType s] [QuasiCompact s]
    (η : S) (_hη : IsGenericPoint η Set.univ)
    (eK : S.presheaf.stalk η ≅ CommRingCat.of K)
    (q : N ⟶ S) [IsFinite q] [Surjective q]
    (_hN : IsNormalScheme N)
    [LocallyOfFiniteType (q ≫ s)] [QuasiCompact (q ≫ s)]
    (ηN : N) (_hηN : IsGenericPoint ηN Set.univ)
    (eN : N.presheaf.stalk ηN ≅ CommRingCat.of L)
    (j : Spec (CommRingCat.of L) ⟶ N)
    (_hj : j = Spec.map eN.hom ≫ N.fromSpecStalk ηN)
    (_hgeneric : IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap K L))) q
      (Spec.map eK.hom ≫ S.fromSpecStalk η))
    (p : M ⟶ Spec (CommRingCat.of k)) [IsHProjective p]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (a : Spec (CommRingCat.of L) ⟶ M) (ha : a ≫ p = j ≫ (q ≫ s))
    (T : Scheme.{u}) (i : T ⟶ pullback p (q ≫ s))
    [IsClosedImmersion i] [IsReduced T]
    (_hi : Set.range i = closure
      {pullback.lift a j ha (IsLocalRing.closedPoint L)}) :
    IsIntegral T ∧
    ∃ jT : Spec (CommRingCat.of L) ⟶ T,
      jT ≫ i = pullback.lift a j ha ∧
      (∃ ηT : T, IsGenericPoint ηT Set.univ ∧
        ∃ eT : T.presheaf.stalk ηT ≅ CommRingCat.of L,
          jT = Spec.map eT.hom ≫ T.fromSpecStalk ηT) ∧
      IsProper (i ≫ pullback.snd p (q ≫ s)) ∧
      Surjective (i ≫ pullback.snd p (q ≫ s)) ∧
      IsPullback jT (𝟙 (Spec (CommRingCat.of L)))
        (i ≫ pullback.snd p (q ≫ s)) j ∧
      IsProper (i ≫ pullback.snd p (q ≫ s) ≫ q) ∧
      Surjective (i ≫ pullback.snd p (q ≫ s) ≫ q) ∧
      LocallyOfFiniteType (i ≫ pullback.snd p (q ≫ s) ≫ q) ∧
      QuasiCompact (i ≫ pullback.snd p (q ≫ s) ≫ q) ∧
      (∃ V : S.Opens, Dense (V : Set S) ∧
        IsFinite ((i ≫ pullback.snd p (q ≫ s) ≫ q) ∣_ V)) ∧
      jT ≫ (i ≫ pullback.fst p (q ≫ s)) = a := by
  sorry

end AlgebraicGeometry
