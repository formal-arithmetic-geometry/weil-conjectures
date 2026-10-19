/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import Sheaf.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import Sheaf.Compactification.NagataSketchClosure
import Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-! # A finite surjection splits finitely many separated etale maps into opens

Source: Orgogozo author draft, Lemma 9.1.3 and proof, printed p. 20
(blueprint: lem-trf-finite-base-splits-etale).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite surjective base change splits a finite family of separated etale maps
into quasi-compact open subschemes.

Source: Orgogozo author draft, Lemma 9.1.3 and proof, printed p. 20
(blueprint: lem-trf-finite-base-splits-etale).

Proof, following the node's nine steps:
1. Prove the single-map assertion simultaneously over every Noetherian base by induction
   on a geometric fibre-cardinality bound. The source is Noetherian, hence quasi-compact,
   by `lem-weil-pbc-finite-type-over-noetherian`. On affine charts,
   `lem-weil-pbc-etale-ring-map-quasi-finite` gives local quasi-finiteness, and
   `lem-weil-pbc-lqf-qc-source-bounded-fibres` supplies a degree bound. Use
   `lem-weil-pbc-fibre-degree-base-change`, `lem-weil-pbc-etale-scheme-base-change` and
   `lem-weil-pbc-etale-algebra-over-field-product` to identify geometric degree with
   cardinality. Bound zero means the source is empty: use the identity base change and
   empty coproduct. For positive bound d assume the assertion for d - 1 over every base.
2. The base is qcqs by `lem-weil-pbc-locally-noetherian-quasi-separated`.
   Apply `thm-pqf-zmt-factorization` to compactify U as an open in a finite S-scheme Y.
   Replace Y by the schematic closure Ubar using `sk-lem-nagata-sketch-closure`.
   Its finite map p to S follows from `lem-weil-pbc-closed-immersion-finite` and
   `lem-weil-pbc-finite-composition`; it remains Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`. Injectivity of sections into the direct
   image from U shows that U is dense in Ubar. The map p is separated by
   `lem-weil-pbc-finite-closed-map-finite-fibres`.
3. In P = U ×_S Ubar, the graph of U → Ubar is closed by pullback of the closed
   diagonal of p (`def-pc-fibre-product`, `def-weil-proper-morphism`, and
   `lem-weil-pbc-closed-immersion-base-change`). It is open because the diagonal of U/S
   is open inside U ×_S U (`def-weil-etale-morphism`, `def-weil-unramified-morphism`,
   and `lem-weil-pbc-open-immersion-base-change`). Thus P = U ⨿ W over Ubar.
   The complement w : W → Ubar is etale by `lem-weil-pbc-etale-scheme-base-change` and
   `lem-weil-pbc-etale-composition-cancellation`, separated by
   `lem-weil-pbc-separated-base-change`, and finitely presented by
   `lem-weil-pbc-qcqs-morphism-permanence`, `lem-weil-pbc-finite-type-over-noetherian`
   and `lem-weil-pbc-noetherian-open-subscheme-noetherian`. It is quasi-finite as in step 1.
4. Over dense U, the graph removes one point from each geometric fibre, so w has bound
   d - 1 there. Apply `lem-weil-pbc-flat-fp-qf-stratification` to w. Testing its universal
   property on residue fields identifies the closed degree-at-most-r loci; use
   `lem-weil-pbc-fibre-degree-base-change`, `lem-weil-pbc-etale-scheme-base-change` and
   `lem-weil-pbc-etale-algebra-over-field-product` for geometric cardinalities.
   The closed degree-at-most-(d - 1) locus contains dense U and is all of Ubar.
   Apply the smaller-bound induction to w, without a surjectivity assumption, obtaining
   a finite surjection q : T' → Ubar splitting W into finitely many quasi-compact opens.
5. The image of U in S is open by `lem-weil-pbc-etale-morphism-open-map`. Form its
   reduced closed complement C by `lem-weil-pbc-reduced-induced-closed-subscheme`.
   The map T' ⨿ C → S is finite by `lem-weil-pbc-finite-composition`,
   `lem-weil-pbc-closed-immersion-finite` and the affine product-algebra description
   (`def-weil-finite-integral-morphism`), and is surjective by its two components.
   Pulling back P = U ⨿ W along q gives U ×_S T' as q⁻¹(U) together with the split
   complement; U ×_S C is empty (`def-pc-fibre-product`). The first open is quasi-compact
   by `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`; all are opens in T' ⨿ C by
   `lem-weil-pbc-open-immersion-base-change`. This completes the single-map induction.
6. For each member of the finite family take its single-map finite surjection T_i → S
   and splitting. Empty members are allowed; for the empty family take T = S.
7. Take the iterated fibre product of the T_i over S. Its map to S and projections
   are finite by `lem-weil-pbc-finite-morphism-permanence` and
   `lem-weil-pbc-finite-composition`; it is surjective by
   `lem-weil-pbc-surjective-base-change` and composition of surjections.
8. Pull each splitting back to T. Associativity and distribution over disjoint open
   unions follow from `def-pc-fibre-product`. Each pulled-back summand is an open by
   `lem-weil-pbc-open-immersion-base-change`. The isomorphism respects the maps to T.
9. A finite affine cover of each old summand pulls back along the finite projection to
   a finite affine cover (`lem-weil-pbc-finite-morphism-permanence`). The new summands
   are quasi-compact. They need not cover T or be disjoint inside T. Since T is Noetherian,
   quasi-compactness of each open scheme is equivalent to quasi-compactness of its
   open immersion into T. Empty sources and empty summand families remain included.
-/
theorem finite_base_splits_etale
    {S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    {I : Type u} [Finite I]
    (U : I → Scheme.{u}) (u : ∀ i, U i ⟶ S)
    [∀ i, IsSeparated (u i)] [∀ i, Etale (u i)]
    [∀ i, LocallyOfFinitePresentation (u i)]
    [∀ i, QuasiCompact (u i)] [∀ i, QuasiSeparated (u i)] :
    ∃ (T : Scheme.{u}) (r : T ⟶ S), IsFinite r ∧ Surjective r ∧
      ∀ i, ∃ (J : Type u) (_ : Finite J) (W : J → Scheme.{u})
        (w : ∀ j, W j ⟶ T),
        (∀ j, IsOpenImmersion (w j) ∧ QuasiCompact (w j)) ∧
        ∃ e : pullback (u i) r ≅ ∐ W,
          e.hom ≫ Sigma.desc w = pullback.snd (u i) r := by
  sorry

end AlgebraicGeometry
