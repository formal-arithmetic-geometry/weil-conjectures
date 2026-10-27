/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen

/-! # Finite-type points detect surjectivity of flat locally presented stack maps

Source: Stacks Project, stacks-morphisms.tex, Tag 06G2 and the last paragraph of
Tag 06N3; stacks-properties.tex, Tags 04XL and 04XI
(blueprint: lem-sfb-stack-flat-lfp-finite-type-surjectivity).

The finite-type-point condition is expressed through all locally finite-type field maps.
The conclusion retains the algebraic-space presentation of each actual 2-base change
and the surjectivity of its specified projection to the test scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A flat locally finitely presented map from a space to an algebraic stack is surjective
if its image contains every finite-type point. The image of a field spectrum is a single
point class, so `hfinite` is precisely containment of all points admitting a locally
finite-type field representative. Field extensions do not change that point class.
Source: Stacks Project, Tag 06G2, applied as in the final paragraph of Tag 06N3;
Tags 04XL and 04XI (blueprint: lem-sfb-stack-flat-lfp-finite-type-surjectivity).

Proof:
1. The algebraic-space diagonal of F makes q representable by algebraic spaces, by
lem-sfb-stack-diagonal-space-source-representability. Thus each scheme 2-base change
has an algebraic-space presentation compatible with its projection.
2. Apply lem-sfb-stack-point-topology-flat-lfp-open to q, with hflat and hlfp. Its
point map is open; its image O is therefore open in the smooth-atlas topology of F.
The discrete-stack point quotient agrees with the ordinary point classes of A.
3. If the closed complement of O were nonempty, it would be locally closed, and
lem-sfb-stack-locally-closed-finite-type-point would give a point in it with a locally
finite-type field representative. The condition hfinite puts that point in O, a
contradiction. Thus the point map of q is surjective.
4. Apply lem-sfb-representable-stack-point-surjectivity to this representable q.
Every scheme 2-base-change projection is surjective on algebraic-space points.
Equivalently, its etale scheme charts jointly cover all points of the test scheme,
which is SpaceMapIsSurjective. No preservation of finite-type points by an arbitrary
test scheme map is asserted or needed. -/
theorem stack_flat_lfp_finite_type_surjectivity {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (A : AlgebraicSpace S) (q : BasedFunctor (discreteModuli A.obj.obj) F)
    (hflat : ModuliSpaceTest @Flat q)
    (hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q)
    (hfinite : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) F),
      ModuliSpaceTest @LocallyOfFiniteType a →
        Set.range (moduliPointMap a) ⊆ Set.range (moduliPointMap q)) :
    ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange q T t Z p ∧ SpaceMapIsSurjective Z T p := by
  sorry

end CategoryTheory
