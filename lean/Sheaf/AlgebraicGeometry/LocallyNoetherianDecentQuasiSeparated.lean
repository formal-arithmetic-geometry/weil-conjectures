/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.SpaceMonicDiagonalTests
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FlatFpLqfBoundedStratification
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-! # Locally Noetherian decent algebraic spaces are quasi-separated

Source: Stacks Project, Decent Spaces, Tag 0BB6,
lemma-locally-Noetherian-decent-quasi-separated
(blueprint: lem-sfb-locally-noetherian-decent-quasiseparated).

Decency is expressed by quasi-compact scheme pullbacks of every field-valued map.
The conclusion includes the equivalent affine étale-pair formulation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally Noetherian decent algebraic space is absolutely quasi-separated.
Source: Stacks Project, Decent Spaces, Tag 0BB6,
lemma-locally-Noetherian-decent-quasi-separated
(blueprint: lem-sfb-locally-noetherian-decent-quasiseparated).

Proof:
1. For affine étale charts `U,V`, their scheme pullback `W` is étale over `U`
[def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers]. It is flat,
locally finitely presented and locally quasi-finite [def-weil-etale-morphism,
lem-weil-pbc-unramified-quasi-finite-at-points]. The monomorphism into `V × U`
and separatedness of the affine source give separatedness of `W → U`
[lem-weil-pbc-affine-source-morphism-separated, lem-a1-space-monic-diagonal-tests].
2. Decency makes every residue-field fibre quasi-compact. An étale field fibre is a
union of open spectra of finite separable field extensions; compactness makes this
union finite [lem-weil-pbc-etale-fibre-discrete-separable-points,
lem-weil-pbc-finite-affine-coproduct-spectrum]. Its degree is finite, including zero
for the empty fibre.
3. The affine locally Noetherian `U` is Noetherian and has finitely many irreducible
components with generic points [lem-weil-pbc-affine-scheme-qcqs,
lem-weil-pbc-noetherian-finitely-many-components, lem-weil-pbc-scheme-sober]. Let `n`
be their maximum fibre degree, or zero for empty `U`. The degree superlevel set
for `n+1` is open [lem-sfb-flat-lfp-lqf-degree-superlevel-open]. If nonempty it
contains a component's generic point, contradicting the maximum
[lem-sc-irreducible-components-cover]. Thus all fibre degrees are bounded by `n`.
4. Bounded stratification gives finitely many locally closed strata `S_r` with
`W ×_U S_r → S_r` finite locally free [lem-weil-pbc-flat-fp-lqf-bounded-stratification,
lem-weil-pbc-reduced-induced-closed-subscheme].
5. Every subspace of the Noetherian space `U` is quasi-compact: the maximal finite
union of members of an open cover already covers the subspace, by the minimal
condition on closed subsets [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal].
This applies to each stratum.
6. The finite locally free maps are finite, hence affine
[def-pc-finite-locally-free, def-weil-finite-integral-morphism]. A finite affine open
cover of each stratum pulls back to a finite cover by quasi-compact affine schemes
[lem-weil-pbc-affine-opens-basis, lem-weil-pbc-affine-morphism-permanence,
lem-weil-pbc-affine-scheme-qcqs]. Each `W ×_U S_r` is therefore quasi-compact.
7. The images of these finitely many schemes cover `W`: a point over a stratum
lifts to the fibre product since the tensor product of its two residue-field
extensions is nonzero [lem-weil-pbc-fibre-product-points]. Pull an open cover back
to each, take finite subcovers, and combine them. This proves compactness of `W`.
The affine étale-pair criterion gives quasi-compactness of the absolute diagonal
[lem-sfb-etale-affine-pairs-test-quasiseparated]. -/
theorem isAbsolutelyQuasiSeparated_of_locallyNoetherian_of_decent
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hdecent : ∀ (K : Type u) [Field K]
      (b : Spec (CommRingCat.of K) ⟶ Spec (.of (ULift.{u} ℤ)))
      (c : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
      (U : Over (Spec (.of (ULift.{u} ℤ)))), IsAffine U.left →
      ∀ a : yoneda.obj U ⟶ X.obj.obj,
        ∃ (W : Over (Spec (.of (ULift.{u} ℤ)))) (p : W ⟶ U)
          (q : yoneda.obj W ⟶ yoneda.obj (Over.mk b)),
          IsPullback q (yoneda.map p) c a ∧ CompactSpace W.left) :
    IsAbsolutelyQuasiSeparated X ∧
      ∀ (U V : Over (Spec (.of (ULift.{u} ℤ))))
        (a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ X.obj.obj),
        IsAffine U.left → IsAffine V.left → IsEtale a → IsEtale b →
          ∃ (W : Over (Spec (.of (ULift.{u} ℤ)))) (p : W ⟶ U) (q : W ⟶ V),
            IsPullback (yoneda.map p) (yoneda.map q) a b ∧ CompactSpace W.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
