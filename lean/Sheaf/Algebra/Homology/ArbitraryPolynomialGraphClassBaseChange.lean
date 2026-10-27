/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalData
public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalSystem
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Polynomial graph classes over arbitrary commutative rings

Source: Stacks Project, dualizing.tex, Tags 0E2E, 0E2F, 0A70, 0A71 and 0BZI;
the ordered graph/counit refinement in the DAG proof.
(blueprint: lem-sfb-arbitrary-polynomial-graph-class-base-change).

The four statements give existence and invertibility of multiplication, preservation
of the specified class under arbitrary scalar extension, and identity and composition
normalizations. A chart with bijective coordinates is an ordinary polynomial chart.
The two pushout squares express P' = P tensor_R R' and B' = B tensor_R R', without
choosing carriers for these canonical tensor algebras. All derived categories are the
ordinary unbounded module categories used by the recorded Koszul definitions.

## Main statements

- `arbitraryPolynomialGraphClass_exists`: normalized graph isomorphism and multiplication.
- `arbitraryPolynomialGraphClass_baseChange`: the exact class square for scalar extension.
- `arbitraryPolynomialGraphClass_identity`: identity normalization.
- `arbitraryPolynomialGraphClass_composition`: successive-extension normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The normalized graph diagonal isomorphism exists over arbitrary rings, and
multiplication by its adjunct class is invertible. The coordinate bijection says that
P is the polynomial algebra itself, rather than a proper localization of it.
Source: Stacks 0E2E and 0BZI, with the arbitrary-ring graph refinement
(blueprint: lem-sfb-arbitrary-polynomial-graph-class-base-change).

Proof (DAG steps 1--4):
1. The differentials have basis dt_i; lem-weil-pbc-exterior-power-free-basis gives the
ordered top volume, also for the empty tuple. Polynomial monomials and
lem-weil-pbc-flat-tensor-exact show that P, T, Q and B are R-flat.
2. By lem-sfb-arbitrary-polynomial-dual-properties, B is perfect over P. Apply
lem-sfb-perfect-coinduction-tor-independent-exchange to the flat map P -> P tensor_R B.
The exchange is characterized by extension of the evaluation counit and ordered volume.
3. lem-trf-polynomial-graph-coinduction and lem-sfb-koszul-evaluation-pasting give the
ordered graph trace. Paste with coinduction transitivity, using
lem-trf-derived-coinduction-adjunction and lem-cat-right-adjoint-composition. This is
exactly IsKoszulDiagonalNormalization, with no permutation of Koszul blocks.
4. The class is the coinduction adjunct of kappa inverse. Precomposition by b sends
x to xi(bx), so multiplication by the class is that same inverse adjunct and is
invertible. No perfection over Q is used. -/
theorem arbitraryPolynomialGraphClass_exists {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C : PolynomialKoszulChart R B) (hpoly : Function.Bijective C.coordinates) :
    ∃ κ : C.diagonalHom ≅ koszulDiagonalUnit B,
      IsKoszulDiagonalNormalization C κ ∧
      IsIso (relativeDualizingModuleClassMap R B C.firstPullback (C.diagonalClass κ)) := by
  sorry

/-- Every arbitrary scalar extension preserves the normalized class itself. Pushouts
are the carrier-independent specification of the two scalar-extended algebras; no
flatness of the base map or perfection of the diagonal module is assumed.
The comparison c is fixed by the evaluation counit; PreservesClass expands to the
actual commuting square using the canonical first-pullback and diagonal maps.
Source: Stacks 0E2F and 0A71, with exact ordered-class refinement
(blueprint: lem-sfb-arbitrary-polynomial-graph-class-base-change).

Proof (DAG steps 5--8):
5. lem-weil-pbc-flat-module-base-change and the finite presentation give the primed
hypotheses. lem-sfb-flat-algebra-derived-module-tensor-exchange, with the R-flat
algebras P, T, Q and modules B, Q, checks all Tor-independent squares without requiring
R' flat. lem-sfb-perfect-coinduction-tor-independent-exchange supplies c.
6. Paste the evaluation-counit mates by lem-weil-pbc-mate-pasting and
lem-cat-right-adjoint-composition. The two tensor paths agree on pure tensors and
ordered volumes, so the composite comparison intertwines the two graph exchanges.
Only existence of diagonal coinduction exchange is needed, not its invertibility.
7. The finite-free graph resolution remains the ordered graph resolution after scalar
extension. lem-sfb-koszul-evaluation-pasting preserves its top functional exactly;
hence the graph traces and the two kappa maps commute with the pasted exchange.
8. Take adjuncts by lem-trf-derived-coinduction-adjunction. The defining counit equation
turns this into d composed with the scalar extension of xi = xi' composed with the
canonical diagonal comparison. This is equality of arrows, including the sign. -/
theorem arbitraryPolynomialGraphClass_baseChange {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart S D)
    (hC : Function.Bijective C.coordinates) (hE : Function.Bijective E.coordinates)
    (F : KoszulDiagonalChartChange C E)
    (hbase : IsPushout (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom F.base)
      (CommRingCat.ofHom F.ring) (CommRingCat.ofHom (algebraMap S D)))
    (hquotient : IsPushout (CommRingCat.ofHom C.quotient.toRingHom)
      (CommRingCat.ofHom F.ambient) (CommRingCat.ofHom F.ring)
      (CommRingCat.ofHom E.quotient.toRingHom)) :
    ∃ c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model,
      F.IsComparison c ∧
      ∀ (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
        (κE : E.diagonalHom ≅ koszulDiagonalUnit D),
        IsKoszulDiagonalNormalization C κ → IsKoszulDiagonalNormalization E κE →
        F.PreservesClass κ κE c := by
  sorry

/-- The normalized identity exchange is the canonical identity scalar identification.
Together with the preceding class square this gives the identity law on xi itself.
Source: Stacks 0A71, 0E2F; the DAG's identity refinement
(blueprint: lem-sfb-arbitrary-polynomial-graph-class-base-change).

Proof (DAG step 9): apply the identity clause of
lem-sfb-perfect-coinduction-tor-independent-exchange. The coefficient map fixes the
ordered volume, hence is the identity on the free rank-one top line. Uniqueness of
the evaluation-counit mate gives the displayed identity. The graph trace fixes its
top functional by lem-sfb-koszul-evaluation-pasting, so its adjunct class is fixed too.
For n=0 this is the empty graph trace, and zero rings cause no exception. -/
theorem arbitraryPolynomialGraphClass_identity {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C : PolynomialKoszulChart R B) (hpoly : Function.Bijective C.coordinates)
    (F : KoszulDiagonalChartChange C C)
    (hf : F.ring = RingHom.id B) (hg : F.ambient = RingHom.id C.P)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ C.model)
    (hc : F.IsComparison c) :
    c.hom = (koszulDiagonalExtensionId F.ring hf).hom.app C.model := by
  sorry

/-- Successive normalized scalar exchanges equal the exchange for their composite,
under the canonical tensor associator. Together with the class squares this is the
successive-extension law for the specified xi, rather than an unspecified generator.
Source: Stacks 0A71, 0E2F; the DAG's successive-extension refinement
(blueprint: lem-sfb-arbitrary-polynomial-graph-class-base-change).

Proof (DAG step 9): the successive-extension clause of
lem-sfb-perfect-coinduction-tor-independent-exchange identifies the direct and pasted
evaluation-counit exchanges under the scalar associator. The coefficient maps both
send every dt_i to dt_i and the ordered top volume to the ordered top volume.
lem-sfb-koszul-evaluation-pasting identifies the graph traces; mate pasting from
lem-weil-pbc-mate-pasting preserves the resulting equality of adjunct classes.
This argument also covers empty tuples and zero rings and never uses perfection of
B over its self-product or a proper-adjoint comparison. -/
theorem arbitraryPolynomialGraphClass_composition {R B S D T H : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    [CommRing T] [CommRing H] [Algebra T H]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart S D)
    (J : PolynomialKoszulChart T H)
    (hC : Function.Bijective C.coordinates) (hE : Function.Bijective E.coordinates)
    (hJ : Function.Bijective J.coordinates)
    (F : KoszulDiagonalChartChange C E) (G : KoszulDiagonalChartChange E J)
    (FG : KoszulDiagonalChartChange C J)
    (hb : FG.base = G.base.comp F.base) (hd : FG.ring = G.ring.comp F.ring)
    (hp : FG.ambient = G.ambient.comp F.ambient)
    (hFbase : IsPushout (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom F.base)
      (CommRingCat.ofHom F.ring) (CommRingCat.ofHom (algebraMap S D)))
    (hFquotient : IsPushout (CommRingCat.ofHom C.quotient.toRingHom)
      (CommRingCat.ofHom F.ambient) (CommRingCat.ofHom F.ring)
      (CommRingCat.ofHom E.quotient.toRingHom))
    (hGbase : IsPushout (CommRingCat.ofHom (algebraMap S D)) (CommRingCat.ofHom G.base)
      (CommRingCat.ofHom G.ring) (CommRingCat.ofHom (algebraMap T H)))
    (hGquotient : IsPushout (CommRingCat.ofHom E.quotient.toRingHom)
      (CommRingCat.ofHom G.ambient) (CommRingCat.ofHom G.ring)
      (CommRingCat.ofHom J.quotient.toRingHom))
    (cF : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model)
    (cG : (relativeDualizingDerivedExtension G.ring).obj E.model ≅ J.model)
    (cFG : (relativeDualizingDerivedExtension FG.ring).obj C.model ≅ J.model)
    (hcF : F.IsComparison cF) (hcG : G.IsComparison cG) (hcFG : FG.IsComparison cFG) :
    (relativeDualizingDerivedExtension G.ring).map cF.hom ≫ cG.hom =
      (koszulDiagonalExtensionComp F.ring G.ring FG.ring hd).hom.app C.model ≫ cFG.hom := by
  sorry

end AlgebraicGeometry
