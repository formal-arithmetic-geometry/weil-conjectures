/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Algebra.Algebra.Defs
import Sheaf.AlgebraicGeometry.DecentSpaceFiniteFieldMap
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Rational points of locally separated algebraic spaces

Source: Stacks Project, Decent Spaces, Tags 088J, 08AL and 07U5;
Morphisms of Spaces, Tag 03KL; Spaces, Tag 02YU
(blueprint: lem-sfb-locally-separated-rational-point-closed-immersion).

Base change to `Spec K` is written as restriction along the composition functor
`Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. On a `K`-scheme `T`
this has value `Z(T)`, with `T` viewed as a `k`-scheme, so it is precisely the
functor of points of `Z ×_Spec k Spec K`, on schemes over `Spec K`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every rational point after a field base change of a locally separated algebraic
space is a representable closed immersion, and its singleton point image is closed.
The domain is the terminal scheme over `Spec K`, so `a` is a `K`-morphism.
Source: Stacks Project, Decent Spaces, Tags 088J, 08AL and 07U5; Spaces, Tag 02YU;
Properties of Spaces, Tag 03BX
(blueprint: lem-sfb-locally-separated-rational-point-closed-immersion).
Proof:
1. Form `Z_K` using [lem-trf-space-fibre-products-etale-covers]. Its relative
   diagonal remains an immersion by [lem-sfb-space-locally-separated-base-change].
   Composition with the locally separated scheme map `Spec K → Spec ℤ` makes
   it absolutely locally separated.
2. By [lem-sfb-locally-separated-space-decent], `Z_K` is decent: all field-spectrum
   maps to it are quasi-compact on affine scheme tests (Stacks 088J).
3. The composite of `a` with the structure map is the identity on `Spec K`.
   Its image in `Spec K` is closed and its residue-field extension is `K/K`,
   hence finite. Apply [lem-sfb-decent-space-finite-field-map] (Stacks 08AL)
   to obtain representability and finiteness on every scheme test.
4. A section is monic: composing an equality after `a` with its retraction
   cancels `a`. Every scheme base change of this section is likewise monic.
5. Each scheme test is therefore a finite monomorphism, hence a closed immersion
   by [lem-a1-finite-monomorphism-closed-immersion] (Stacks 03BB).
6. For any étale scheme test, [lem-a1-space-fibre-product-point] identifies the
   inverse image of the singleton with the image of this closed immersion.
   That image is closed by [def-weil-closed-immersion], so the singleton is closed
   in the final atlas topology [def-a1-space-point-topology] (Stacks 03BX).
No finite-type or quasi-separatedness assumption is used. -/
theorem rationalPoint_isClosedImmersion_of_locallySeparated
    (k : Type u) [Field k] (Z : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hdiag : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj)))
    (K : Type u) [Field K] [Algebra k K]
    (a : yoneda.obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⟶
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙ Z.obj.obj) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) a ∧
      IsClosed ({schemePointMap a (IsLocalRing.closedPoint K)} :
        Set (Point
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙ Z.obj.obj))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
