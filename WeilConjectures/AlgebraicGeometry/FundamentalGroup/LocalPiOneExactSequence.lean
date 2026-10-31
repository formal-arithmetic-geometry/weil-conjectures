/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Group.Basic
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # The local fundamental-group sequence of a normal local domain

Source: Stacks Project, pione.tex, Tag 0BSM (lemma-local-exact-sequence-normal),
with exactness interpreted by Tag 0BS9 (lemma-functoriality-galois-ses), part (1)
(blueprint: lem-dl-a1-local-pi1-exact-sequence).

`F` and `E` are arbitrary models of the fraction fields, specified by `IsFractionRing`.
The equation `hi` uniquely specifies their induced map. The fundamental groups are profinite
models of the recorded geometric fibre functors. Equations `hb` and `hc` specify the induced
maps using the existing `fundamentalGroupMap`, with compatible base points obtained from `s`.
The equivalent finite-cover formulation uses actual isomorphisms over the base schemes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- For a normal local domain and its strict henselization, the generic fundamental-group
sequence is exact in the sense of closed normal generation. Finite etale covers of the local
scheme split over the strict-local fraction field, and every generic cover split there extends.

Source: Stacks Project, Tag 0BSM and Tag 0BS9, part (1)
(blueprint: lem-dl-a1-local-pi1-exact-sequence).

The fraction-field instances identify `F = Frac(A)` and `E = Frac(C)`; they specify the
objects in the statement, rather than an additional condition on their extensions. `hi`
specifies the unique induced inclusion. `P` is the recorded universal pointed-etale colimit
presentation. The geometric point on `Spec F` is `s` composed with `Spec i`, and that on
`Spec A` is its further composite with the generic inclusion. The two fibre-action equations
`hb` and `hc` fix the maps, so neither groups nor maps are unrelated abstract variables.
For algebraically closed geometric points, the existing `exists_fiber_flc_equivalence`
identifies these models with automorphisms of `flcFiber`, including its evaluation topology.
The separably closed geometric-point convention also permits imperfect fields.

Proof (the seven steps of the DAG node):
1. Localizations of A are normal domains by lem-weil-pbc-localization-normal-domain.
   The pointed-etale diagram is essentially small and filtered by
   lem-sc-pointed-etale-small-filtered, and its colimit is local by
   lem-sc-ring-strict-henselization-local-maximal-ideal. Hence
   lem-weil-pbc-etale-colimit-normal-local-domain makes C a normal domain with A embedded.
   Use lem-sc-strict-henselization-triples-presentation to compare the same colimit to
   residue triples, lem-weil-pbc-strict-henselization-triples for strict henselianity and
   the chosen separably closed residue field, and
   lem-sc-strict-henselization-faithfully-flat for faithful flatness. Extend A to C to
   the fraction-field map i; its restriction to A is precisely hi.
2. By lem-sbc-normal-integral-generic-hom-full, generic restriction of finite etale
   A-schemes is fully faithful. The stalks are the normal prime localizations of A.
   Functoriality identifies b,c with restriction on fibres. All base schemes are connected;
   use thm-galois-fundamental for their finite continuous action equivalences.
3. A finite etale cover over C is determined by its closed fibre, by
   lemma-weil-pbc-finite-etale-henselian-lifting applied to the proper identity of Spec C.
   By lem-sc-finite-etale-algebra-criterion and def-pc-separably-closed, this fibre is
   a finite union of copies of the separably closed residue field. Lift its isomorphism,
   then pull back to E. The empty cover has n=0.
4. Write a finite etale F-cover split over E as Spec L, with L a finite product of
   finite separable extensions of F. Form B, the integral closure of A in L.
   By lem-weil-pbc-integral-closure-commutes-localization, its localization away from
   zero in A is L: every element of L is integral over F. Thus Spec B has the given
   generic fibre, without yet assuming finiteness of B over A.
5. By lem-dl-a1-strict-local-inertia-identification, E/F is algebraic. Therefore
   localizing C away from the nonzero elements of A gives a field, hence E. Indeed,
   a least-degree algebraic equation of a nonzero element has nonzero constant term
   and expresses its inverse as an F-polynomial. Consequently C tensor_A L equals
   E tensor_F L, which the specified splitting identifies with E^n as a C-algebra.
6. Apply lem-dl-a1-integral-closure-strict-etale-base-change. It identifies C tensor_A B
   with the integral closure of diagonal C in E^n, which is C^n: project monic
   equations coordinatewise, and conversely use the product of (T-c_i). This includes
   n=0. Faithful flatness, lem-weil-pbc-faithfully-flat-surjective-spectrum and the
   fpqc-covering definition give an affine fpqc cover Spec C -> Spec A.
   Apply lem-weil-pbc-fpqc-descend-finite and lem-galois-fpqc-descend-etale separately.
   This makes Spec B the required finite etale extension of the given generic cover.
7. Steps 2,3,6 give full faithfulness and identify the essential image with covers
   split by E. Under thm-galois-fundamental and lem-galois-pi1-functoriality this is
   triviality of the restricted G_E action. Apply
   lem-dl-a1-galois-category-exactness-criterion to obtain surjectivity of c, triviality
   of c composed with b, and closed normal generation of its kernel. The canonical
   maps are continuous by lem-galois-pi1-functoriality. No Noetherian or perfect
   residue-field hypothesis is used, and disconnected and empty covers are retained.
-/
theorem localPiOneExactSequence
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A K C)
    (F E : Type u) [Field F] [Field E]
    [Algebra A F] [IsFractionRing A F] [Algebra C E] [IsFractionRing C E]
    (i : F →+* E)
    (hi : i.comp (algebraMap A F) = (algebraMap C E).comp (algebraMap A C))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of E))
    (G_E G_F G_A : ProfiniteGrp.{u})
    [∀ Q, MulAction G_E ((fiber s).obj Q)]
    [∀ Q, MulAction G_F ((fiber (s ≫ Spec.map (CommRingCat.ofHom i))).obj Q)]
    [∀ Q, MulAction G_A ((fiber ((s ≫ Spec.map (CommRingCat.ofHom i)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A F)))).obj Q)]
    [IsFundamentalGroup (fiber s) G_E]
    [IsFundamentalGroup (fiber (s ≫ Spec.map (CommRingCat.ofHom i))) G_F]
    [IsFundamentalGroup (fiber ((s ≫ Spec.map (CommRingCat.ofHom i)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A F)))) G_A]
    (b : G_E →* G_F) (c : G_F →* G_A)
    (hb : b = fundamentalGroupMap
      (pullbackFiberIso (Spec.map (CommRingCat.ofHom i)) s) G_E G_F)
    (hc : c = fundamentalGroupMap
      (pullbackFiberIso (Spec.map (CommRingCat.ofHom (algebraMap A F)))
        (s ≫ Spec.map (CommRingCat.ofHom i))) G_F G_A) :
    Continuous c ∧ Function.Surjective c ∧
      c.comp b = 1 ∧
      c.ker = (Subgroup.normalClosure (Set.range b)).topologicalClosure ∧
      (∀ Y : (Spec (.of A)).FiniteEtale, ∃ n : ℕ,
        Nonempty (Over.mk (Limits.pullback.snd Y.obj.hom
            (Spec.map (CommRingCat.ofHom i) ≫
              Spec.map (CommRingCat.ofHom (algebraMap A F)))) ≅
          Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of E)))))) ∧
      (∀ V : (Spec (.of F)).FiniteEtale,
        (∃ n : ℕ, Nonempty (Over.mk (Limits.pullback.snd V.obj.hom
            (Spec.map (CommRingCat.ofHom i))) ≅
          Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of E)))))) →
        ∃ Y : (Spec (.of A)).FiniteEtale,
          Nonempty ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).obj Y ≅ V)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
