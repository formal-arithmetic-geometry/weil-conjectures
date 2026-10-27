/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.FiniteType

import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # A finite type stage for an fpqc scheme model over a Dedekind base

Source: Stacks Project, limits.tex, Tag 01ZM, lemma-descend-finite-presentation,
and more-algebra.tex, Tag 0AUW, lemma-dedekind-torsion-free-flat; the explicit
fpqc-sheaf comparison uses sites.tex, Tags 04TR and 04TQ
(blueprint: lem-sfb-dedekind-fpqc-model-finite-type-stage).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finitely presented scheme model of an fpqc sheaf over a flat surjective affine
cover of a Dedekind base descends to a finite type flat surjective subalgebra.
Source: Stacks Project, Tag 01ZM (objects, arrows and equalities), Tag 0AUW
(torsion-free modules), and Tags 04TR/04TQ (effective descent of set sheaves)
(blueprint: lem-sfb-dedekind-fpqc-model-finite-type-stage).

Here `Over.map` restricts the original functor by composing a test scheme's structure
map with the indicated map of spectra. `RepresentableBy` is a natural bijection with
relative morphisms into the specified scheme, even for an independent set universe `v`.

Proof plan, following the node's nine steps:
1. The finitely generated R-subalgebras of B form a nonempty directed union equal to B.
   The affine-limit theorem lem-weil-pbc-limit-affine-transition identifies Spec B
   with their inverse limit, with affine transitions by
   lem-weil-pbc-morphism-affine-schemes-affine (size: def-weil-size-convention).
2. Flatness of B gives torsion-freeness of each subalgebra C. Apply
   lem-sfb-dedekind-torsionfree-module-flat and
   lem-weil-pbc-flat-ring-map-iff-flat-affine. Contract primes of B to get surjectivity.
   Lem-weil-pbc-finite-type-noetherian-finite-presentation gives finite presentation;
   lem-weil-pbc-qcqs-morphism-permanence gives the qcqs clauses. Hence Spec C and Spec B
   are singleton fpqc covers by def-weil-pbc-fpqc-covering and the affine-map lemma.
3. The tensor universal property lem-weil-pbc-algebra-tensor-pushout-universal-property
   shows that the tensor squares and cubes of B are the colimits of those of C,
   also on every tail. No injectivity of tensor-power transition maps is needed.
   Lem-weil-pbc-fibre-product-affine-spectra identifies their spectra and projections;
   the affine-map and affine-limit lemmas apply to both systems.
4. The given representation defines the canonical overlap isomorphism of P by
   lem-galois-yoneda-fully-faithful. Cancellation gives the triple cocycle. All
   pullbacks remain finitely presented by lem-weil-pbc-qcqs-morphism-permanence.
5. Apply thm-pd-spreading-out (1) to obtain a finitely presented model Q at a stage
   with a specified pullback isomorphism to P; transport the canonical overlap to it.
6. Apply thm-pd-spreading-out (2) on the square system to descend the overlap map
   and its inverse to a common larger stage. No flatness of C to B is used.
7. Apply thm-pd-spreading-out (3) on squares to descend the inverse identities,
   then on cubes to descend the cocycle. Pullback preserves the inverse identities.
8. By lem-weil-pbc-fpqc-representable-descent the relative functor of Q is a sheaf.
   Apply lem-pe-set-sheaf-cover-descent on the cover Spec C to Spec R to glue it,
   with the descended overlap isomorphism, to an fpqc sheaf H on Spec R.
9. Over Spec B the specified comparisons give H isomorphic to F. Their two pullbacks
   agree because the descended overlap pulls back to the canonical overlap of P.
   Glue this comparison and its inverse along Spec B to Spec R using the morphism
   and uniqueness clauses of lem-pe-set-sheaf-cover-descent. Thus H is isomorphic
   to the original F, and restricting to Spec C gives the required representation.
   Step 2 supplies flatness, surjectivity and finite presentation of the base stage. -/
theorem dedekindFpqcModelFiniteTypeStage
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hRdim : ringKrullDim R ≤ 1)
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (F : Sheaf (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) (Type v))
    (P : Over (Spec (CommRingCat.of B)))
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [QuasiSeparated P.hom]
    (hP : Nonempty
      (Functor.RepresentableBy
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R B)))).op ⋙ F.obj) P)) :
    ∃ C : Subalgebra R B,
      (algebraMap R C).FiniteType ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      ∃ Q : Over (Spec (CommRingCat.of C)),
        LocallyOfFinitePresentation Q.hom ∧ QuasiCompact Q.hom ∧ QuasiSeparated Q.hom ∧
        Nonempty
          (Functor.RepresentableBy
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R C)))).op ⋙ F.obj) Q) := by
  sorry

end AlgebraicGeometry
