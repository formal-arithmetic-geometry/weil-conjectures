/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType

import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # A multiplicity-one weight in a simple split semisimple module

Source: Milne, Algebraic Groups (2017), Theorem 22.2, pp.463--464, and
Theorem 22.18(b), p.467; semisimple groups are reductive by Chapter 19a--19b.
(blueprint: lem-sfb-split-simple-multiplicity-one-weight)

Rational representations and submodules use the existing coordinate coaction
interface, equivalent to the all-algebras action by the comodule dictionary.
The equalizer in the conclusion is exactly the character space: evaluate the
coaction identity at every algebra-valued torus point, or conversely at its
universal coordinate-valued point. It retains nonreduced test algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RationalHighestWeight

/-- A nonzero simple rational module of a split semisimple group has a
one-dimensional character space for the specified split maximal torus.

Source: Milne, Algebraic Groups (2017), Theorems 22.2 and 22.18(b), pp.463--467.
(blueprint: lem-sfb-split-simple-multiplicity-one-weight)

Proof (the five DAG steps):
1. Apply lem-sfb-split-semisimple-borel-pair to G and T, obtaining B = U ⋊ T
   with B split solvable. The closed triangular embedding from
   lem-sfb-split-solvable-triangular-embedding and the eigenline supplied by
   lem-sfb-triangular-group-representation-eigenline give a nonzero B-eigenvector
   v, using lem-sfb-rational-representation-comodule-dictionary to restrict V.
2. Its B-character kills U by lem-sfb-unipotent-to-multiplicative-trivial.
   Restriction gives a character lambda of T, and b acts on v by lambda(p(b)).
3. Expand the coaction in a basis of k[G]. Starting from kv, repeatedly add
   the images under its coefficient operators. Finite dimension makes this
   increasing sequence stabilize at a nonzero rational submodule, hence at V
   by simplicity. Over any field extension the extended coefficient operators
   give the scalar extensions of the same sequence. Thus v remains cyclic;
   no simplicity assertion after extension is needed.
4. Extend to an algebraic closure. Smoothness survives base change by
   lem-weil-pbc-smooth-ring-map-base-change-composition. Connectedness follows
   from lem-sbc-connected-rational-point-geometrically-connected using the
   identity point. The Borel pair extends by step 1. Semisimplicity implies
   reductivity by lem-sfb-reductive-borel-pair-structure, and
   lem-sfb-primitive-cyclic-weight-bound identifies the lambda-weight space
   with the line spanned by the extended v.
5. A character of the split torus is a Laurent monomial: compare distinct
   monomial coefficients in Delta(f) = f tensor f and epsilon(f) = 1.
   The dictionary identifies the all-algebras character space with the
   displayed coaction equalizer. Apply lem-sfb-relative-torus-bundle-weights
   to the finite free k-module V and the algebraic closure; the equalizer
   commutes with this scalar extension. Extending a basis preserves its
   dimension, so its dimension over k is one as well.
-/
theorem split_simple_multiplicity_one_weight {k : Type u} [Field k]
    (G T : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hG : IsSemisimpleGroupScheme
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X)
    (iT : T ⟶ G) (hclosed : IsClosedSubgroupScheme iT.hom.hom)
    (hmax : ReductiveTorusCentralizer.IsMaximalTorus
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map iT))
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    [IsAffine T.X.left]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (c : V →ₗ[k] V ⊗[k] coordinateAlgebra G)
    (hcoassoc : HopfAction.Coassociative k (coordinateAlgebra G) V c)
    (hcounit : HopfAction.Counital k (coordinateAlgebra G) V c)
    (hsimple : IsSimple c) :
    ∃ lam : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k),
      Module.finrank k
        (LinearMap.eqLocus ((coordinateMap iT).toLinearMap.lTensor V ∘ₗ c)
          ((TensorProduct.mk k V (coordinateAlgebra T)).flip (characterElement lam))) = 1 := by
  sorry

end AlgebraicGeometry.RationalHighestWeight
