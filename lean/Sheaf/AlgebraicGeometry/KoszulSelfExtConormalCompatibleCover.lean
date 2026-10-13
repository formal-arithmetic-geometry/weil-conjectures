/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # A compatible regular Koszul comparison cover

Source: Stacks Project, Tag 0BQY and Tag 062I. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A regular immersion admits a compatible Koszul comparison on a covering
family of neighborhoods, without gluing to an arbitrary prescribed neighborhood.

Source: Stacks Project, Tag 0BQY, change of regular generators, and Tag 062I.
(blueprint: new-s3-koszul-conormal-compatible-cover).

Proof: Choose a regular affine chart around each point of V. Use its augmented
Koszul resolution to compute derived Hom into the quotient. Its differential
is zero because the generators vanish in the quotient. Pair the dual increasing
wedge basis with the conormal basis to obtain the local comparison. On a common
subopen, refine by affine subopens around each point. The two conormal bases
have the same length over the nonzero local ring. Shrink until a substitution
of generators is invertible modulo the ideal. Exterior powers of the substitution
define a chain map: contraction with the generator row commutes with the
substitution in degree one, and the derivation identity gives all degrees.
Modulo the ideal these maps are the exterior powers of the conormal change of
basis; dualizing gives exactly the Hom change of coordinates. Comparison
homotopies show that different substitutions induce the same cohomology map.
Localization preserves the contraction and pairing formulas, so the two
comparison morphisms agree on the refinement. Sheaf separatedness gives equality
on the whole common subopen. No global gluing is performed in this lemma.
For an empty V choose the unique empty-indexed family. In degree zero the
comparison is the quotient unit, and above the length both sides are zero. -/
theorem koszulRegularImmersion_self_ext_conormal_compatible_cover
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ (W : V.toScheme → V.toScheme.Opens),
      (∀ z : V.toScheme, z ∈ W z) ∧
      ∃ c : ∀ z : V.toScheme, F.over (W z) ≅ T.over (W z),
        ∀ (x y : V.toScheme) (U : V.toScheme.Opens)
          (hx : U ≤ W x) (hy : U ≤ W y),
          (c x).hom.val.app (op (Over.mk (homOfLE hx))) =
            (c y).hom.val.app (op (Over.mk (homOfLE hy))) := by sorry

end AlgebraicGeometry
