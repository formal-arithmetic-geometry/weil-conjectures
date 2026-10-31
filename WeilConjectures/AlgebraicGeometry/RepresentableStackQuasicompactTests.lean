/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.StackQcqsMorphism
public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace

import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
import WeilConjectures.AlgebraicGeometry.StackPointTopology
import WeilConjectures.AlgebraicGeometry.AlgebraicStackFibreProducts
import WeilConjectures.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Mathlib.Topology.Compactness.Compact

/-! # Quasi-compact representable stack morphisms on scheme and stack tests

Source: Stacks Project, `stacks-morphisms.tex`, Tag 050T
(blueprint: lem-sfb-representable-stack-quasicompact-tests).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace CategoryTheory

/-- For a morphism of algebraic stacks representable by algebraic spaces, quasi-compactness
on every scheme base change is equivalent to quasi-compactness after every quasi-compact
algebraic-stack base change.  The scheme test uses the specified algebraic-space
presentation and its actual projection to the test scheme.

Source: Stacks Project, `stacks-morphisms.tex`, Tag 050T, conditions (1) and (2)
(blueprint: lem-sfb-representable-stack-quasicompact-tests).

Proof, following the four steps of the DAG node:
1. Regard a space as its discrete fibred groupoid. Sheaf descent gives stack descent
and its representable diagonal gives the algebraic-space diagonal. Its etale atlas
is smooth and surjective by lem-sfb-fibred-groupoid-representable-smooth-calculus.
This proves algebraicity; schemes enter via def-trf-scheme-algebraic-space.
2. A quasi-compact etale atlas is also smooth. Conversely, a quasi-compact smooth
atlas surjects continuously onto the point space by lem-sfb-stack-point-topology.
The algebraic-space comparison there and lem-weil-pbc-continuous-image-quasi-compact
make the space of points compact. The final equivalence of
lem-a1-space-etale-open-image then gives a quasi-compact etale atlas. Thus space
and stack quasi-compactness agree, including for schemes.
3. Assume the scheme tests and take a quasi-compact stack V mapping to G. Choose
a smooth surjective atlas U -> V with U quasi-compact, by def-sfb-stack-qcqs-morphism.
The product W = F x_G V is algebraic by lem-sfb-algebraic-stack-fibre-products.
Representability makes E = F x_G U an algebraic space and the scheme test makes
E -> U quasi-compact, hence E quasi-compact by testing the identity of U. Step 2
makes E a quasi-compact stack. Reassociation of triples identifies E with W x_V U:
eliminate the intermediate V-object using its specified isomorphism to the image
of the U-section. The resulting E -> W is smooth and surjective by base change
in lem-sfb-fibred-groupoid-representable-smooth-calculus. Apply
lem-sfb-algebraic-stack-quasicompact-surjection to conclude that W is quasi-compact.
4. Conversely fix a scheme test T and its algebraic-space presentation E_T. For
any quasi-compact algebraic space C -> T, steps 1 and 2 make C a quasi-compact
algebraic stack. The stack-test hypothesis makes F x_G C quasi-compact. Its triples
identify it with E_T x_T C by inserting, or deleting, the image of c in T; since
T and C have discrete fibres, the same construction identifies arrows. This
identification preserves atlases. The sheaf product is an algebraic space by
lem-trf-space-fibre-products-etale-covers, so step 2 makes it quasi-compact as a
space. These are exactly the tests for quasi-compactness of E_T -> T (03HE),
equivalently the recorded MapIsQuasiCompact predicate (03KG). The right side is
precisely the stack-morphism predicate of def-sfb-stack-qcqs-morphism. No separation,
finite-type or Deligne--Mumford assumption enters. The upper test universes may be
enlarged by v₃ and w₃; the canonical universe lifts transport the same triples,
equivalences over the base and atlases, so no test is lost by the common bound.
-/
theorem representable_stack_quasicompact_tests
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)}
    {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G)
    (hF : IsAlgebraicModuliStack F)
    (hG : IsAlgebraicModuliStack G)
    (hrep : IsRepresentableByAlgebraicSpaces f) :
    (∀ (T : Over S)
        (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z p ∧
          AlgebraicSpace.MapIsQuasiCompact p) ↔
      IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₃, w₃} f := by
  sorry

end CategoryTheory
