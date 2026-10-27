/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.GroupSpaceOverCartesian
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-! # Unramified pseudo torsors

Source: Stacks Project, spaces-groupoids.tex, Tags 0DSK(1), 04TW and 04TX(2)
(blueprint: lem-sfb-unramified-pseudo-torsor).

The group and action are internal objects in fppf sheaves over the base algebraic space.
The canonical map `ModObj.leftSMul` is `(g,x) ↦ (gx,x)`. Its invertibility requires no
surjectivity of the pseudo torsor over its base. Scheme properties use the existing
étale-chart test `MapIsLocally`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type pseudo torsor under a locally finite type unramified group
algebraic space is unramified, including the case of empty fibres.
Source: Stacks Project, spaces-groupoids.tex, Tag 0DSK(1), with Definition 04TW
and Lemma 04TX(2) (blueprint: lem-sfb-unramified-pseudo-torsor).

Proof:
1. For a point of `X`, choose a representative `x : Spec K → X`. Form the sheaf fibre
   products `X_K` and `G_K` over its image in `B`, using
   lem-trf-space-fibre-products-etale-covers. The point supplies a section `s` of `X_K`.
   Base change the given pseudo-torsor isomorphism and its inverse.
2. The section gives an isomorphism `G_K → X_K`, `g ↦ g s`. Its inverse sends `t` to
   the first component of the inverse pseudo-torsor map applied to `(t,s)`. The second
   component is `s`, so both composites are identities, as in Tag 04TX(2).
3. By lem-sfb-space-unramified-permanence, `G_K → Spec K` is unramified. Transport
   its scheme charts through the preceding isomorphism to conclude the same for `X_K`.
4. By lem-sfb-space-unramified-locus-base-change, the unramified locus of the locally
   finite type map `X → B` pulls back to the whole of `X_K`. Thus it contains the
   original point. Every point is in that locus, hence the map is unramified. If `X`
   is empty, the same conclusion is vacuous. No section over `B` is required. -/
theorem unramified_of_pseudoTorsor {S : Scheme.{u}} (B : AlgebraicSpace S)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace G.left) (hX : IsAlgebraicSpace X.left)
    (hiso : IsIso (ModObj.leftSMul G X))
    (hGft : MapIsLocally (@LocallyOfFiniteType)
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpace S) ⟶ B))
    (hXft : MapIsLocally (@LocallyOfFiniteType)
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpace S) ⟶ B))
    (hGunr : MapIsLocally (@IsUnramified)
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpace S) ⟶ B)) :
    MapIsLocally (@IsUnramified)
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpace S) ⟶ B) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
