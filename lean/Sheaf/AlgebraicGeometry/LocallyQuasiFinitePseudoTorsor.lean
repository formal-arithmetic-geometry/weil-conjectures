/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus

/-! # Local quasi-finiteness of pseudo-torsors

Source: Stacks Project, spaces-groupoids.tex, Tag 0DSK(2),
lemma-pseudo-torsor-implications; Tag 04TW, definition-pseudo-torsor
(blueprint: lem-sfb-locally-quasifinite-pseudo-torsor).

The group and its action are internal objects in fppf sheaves over the base space.
The chosen cartesian product in that slice is the sheaf fibre product. Mathlib's
`ModObj.leftSMul` is the canonical morphism `(g,x) ↦ (g • x,x)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type pseudo-torsor under a locally quasi-finite group algebraic
space is locally quasi-finite. No surjectivity of the pseudo-torsor is required.
Source: Stacks Project, spaces-groupoids.tex, Tags 0DSK(2) and 04TW
(blueprint: lem-sfb-locally-quasifinite-pseudo-torsor).

Proof:
1. Fix an etale scheme chart V of B and put F = X times_B V. Its map to V is
locally of finite type. By lem-sfb-space-quasifinite-locus-open its quasi-finite
locus Q is open and commutes with arbitrary scheme base change. It suffices to
show that every point of F belongs to Q.
2. Represent a point z of F by x : Spec K to F, using
def-a1-algebraic-space-point-classes. Put P = F times_V Spec K and
H = G times_B Spec K. These are algebraic spaces by
lem-trf-space-fibre-products-etale-covers. The point x gives a section x_K of P.
Base change the pseudo-torsor isomorphism to H times_K P to P times_K P,
then pull it back along y to (y,x_K). This gives the isomorphism H to P,
g to a(g,x_K). Its inverse sends y to the first component of the inverse
pseudo-torsor isomorphism evaluated at (y,x_K); the two inverse identities
follow from those of that isomorphism.
3. By lem-sfb-representable-lqf-calculus-descent, H to Spec K is locally
quasi-finite. Transporting every etale scheme chart through H isomorphic to P
shows that P to Spec K is locally quasi-finite.
4. Thus its quasi-finite locus contains the point z_K induced by x_K. The
base-change equality of lem-sfb-space-quasifinite-locus-open implies z lies
in Q. Hence Q is all of F. Every etale chart is quasi-finite at every point
by pqf-def-quasifinite. V was arbitrary, so X to B is locally quasi-finite.
If F has no points the same pointwise conclusion is vacuous. -/
theorem locallyQuasiFinite_of_pseudoTorsor {S : Scheme.{u}} (B : AlgebraicSpace S)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace G.left) (hX : IsAlgebraicSpace X.left)
    (_hθ : IsIso (ModObj.leftSMul G X))
    (_hGft : MapIsLocally (@LocallyOfFiniteType)
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpace S) ⟶ B))
    (_hXft : MapIsLocally (@LocallyOfFiniteType)
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpace S) ⟶ B))
    (_hGq : SpaceMapIsLocallyQuasiFinite
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpace S) ⟶ B)) :
    SpaceMapIsLocallyQuasiFinite
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpace S) ⟶ B) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
