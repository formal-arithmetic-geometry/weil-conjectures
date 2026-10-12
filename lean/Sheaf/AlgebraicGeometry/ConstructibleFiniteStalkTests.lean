/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

import Sheaf.AlgebraicGeometry.IrreducibleLisseStrata
import Sheaf.AlgebraicGeometry.LisseGenericKernel
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Finitely many stalk tests for a constructible source

Source: the finite irreducible lisse partition argument in blueprint node
`lem-weil-pbc-constructible-noetherian-finite-selection`, steps 1, 3 and 4;
Stacks Project, Tag 09Z6, partition alternative
(blueprint: lem-weil-pbc-constructible-finite-stalk-tests).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finitely many finite geometric stalks test monomorphisms out of a constructible sheaf.
The chosen points depend only on the source sheaf, not on the target or the morphism.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, finite-selection node steps 1, 3
and 4; Stacks Project, Tag 09Z6, partition alternative
(blueprint: lem-weil-pbc-constructible-finite-stalk-tests).

Proof: Choose the finite nonempty irreducible lisse stratification provided by
`lem-weil-pbc-irreducible-lisse-strata`. In each stratum choose its generic point, and
let P be the finite set of its images in X. Use the algebraic closure of the residue
field at each image as its geometric point. Its base change to the stratum is a
geometric generic point: immersions induce isomorphisms on residue fields at
points in their images, so the point lifts through the residue-field point of the
stratum. The natural isomorphism `lemma-openclosed-stalk-upperstar` identifies
the abelian restriction's stalk with the original stalk. The inverse-image/forget
comparison of `lem-weil-pbc-etale-inverse-image-algebraic-structures` identifies its
underlying set sheaf with the set restriction given by stratification. Forgetting
also commutes with stalks by `Point.sheafFiberCompIso`. Thus finite local constancy
of that set restriction gives finiteness of the original abelian stalk's underlying set.

For any map from F with injective stalk maps at P, the same inverse-image stalk
identification, by naturality, gives injectivity at the geometric generic point of
every stratum. The inverse-image/forget comparison also gives local constancy of
the underlying set sheaf of the abelian restriction.
Apply `lem-weil-pbc-lisse-generic-kernel` on each stratum: the restriction of the map
is monomorphic, without a condition on its target. Every geometric point of X lifts
to its unique stratum, so the stalk identification makes the original map injective
at every geometric stalk. Exactness of stalks makes every stalk of its kernel zero.
Conservativity of geometric stalks then makes the kernel zero, hence the map mono.
For empty X take P empty; the sheaf category on the empty scheme has only zero objects.
-/
theorem exists_finite_stalk_tests_of_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ P : Finset X,
      (∀ x : P, Finite
        (((pointSmallEtale (X.algClosurePoint x.val)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F)) ∧
      (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G),
        (∀ x : P, Function.Injective
          (((pointSmallEtale (X.algClosurePoint x.val)).sheafFiber
            (A := AddCommGrpCat.{u + 1})).map φ)) → Mono φ) := by sorry

end AlgebraicGeometry.Scheme
