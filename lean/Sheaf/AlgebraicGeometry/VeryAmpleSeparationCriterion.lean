/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The dimension-drop criterion for very ampleness on a curve

Source: Stacks Project, Varieties, Tag 0E8S; blueprint proof of
`lem-sc-degree-2g1-very-ample` (blueprint: lem-sc-very-ample-separation-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- One-point and two-point dimension drops make the complete linear system a closed
immersion, with pullback of `O(1)` equal to the given line bundle: a basis `b` of the whole
section space `H^0(C, M)` gives generating sections whose morphism
`ProjectiveSpace.homOfGeneratingSections` is a closed immersion pulling `O(1)` back to `M`
(the complete-linear-system clause of `def-sc-ample`), and `M` is very ample in the recorded
sense `IsVeryAmple f M`.
Closed points are exactly the k-rational points over the algebraically closed base field.
The section modules have scalars restricted along the structure morphism. Dimensions use
additive equalities, avoiding truncated subtraction in natural numbers. The conclusion
uses a basis of the entire section space, not an unspecified subsystem.

Source: Stacks Project, Varieties, Tag 0E8S, and the second and third paragraphs of the
blueprint proof of `lem-sc-degree-2g1-very-ample`
(blueprint: lem-sc-very-ample-separation-criterion).

Proof:
1. The one-point drop shows that evaluation at every closed point is nonzero, so the
   complete section space generates M (the base-point-free clause of
   `lem-sc-point-tangent-separation-closed-immersion`). Proper coherent cohomology makes
   this space finite-dimensional.
2. For distinct P and Q, the two-point drop compared with the one-point drop gives a
   section of M(-P) not in M(-P-Q). By `def-sc-divisor` it vanishes at P but not at Q.
3. For P = Q it gives a section of M(-P) not in M(-2P). By `lem-sc-point-cartier`,
   `lem-sc-smooth-regular` and `lem-sc-regular-dim1-dvr`, the local ideal of P is (t)
   in a DVR. In a local frame the section is tu with u a unit. Its nonzero cotangent
   class separates every nonzero tangent vector, since the cotangent space has dimension one.
4. Apply `lem-sc-point-tangent-separation-closed-immersion` to the full section space.
   A basis gives the complete linear system, a closed immersion pulling O(1) back to M.
   This is very ampleness in `def-sc-ample`. -/
theorem veryAmple_of_divisor_dimension_drops
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f]
    (M : C.Modules) [M.IsInvertible]
    (h₁ : ∀ P : closedPoints C,
      Module.finrank k ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          ((M ⊗ Divisor.moduleOfSmoothConnectedCurve k C f
            (Finsupp.single P (-1))).val.obj (Opposite.op ⊤))) + 1 =
      Module.finrank k ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          (M.val.obj (Opposite.op ⊤))))
    (h₂ : ∀ P Q : closedPoints C,
      Module.finrank k ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          ((M ⊗ Divisor.moduleOfSmoothConnectedCurve k C f
            (Finsupp.single P (-1) + Finsupp.single Q (-1))).val.obj (Opposite.op ⊤))) + 2 =
      Module.finrank k ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          (M.val.obj (Opposite.op ⊤)))) :
    IsVeryAmple f M ∧
      ∃ (I : Type u) (_ : Finite I)
        (b : Module.Basis I k ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
            (M.val.obj (Opposite.op ⊤))))
        (s : I → M.sections),
        (∀ i : I, (s i).val (Opposite.op ⊤) = b i) ∧
        ∃ hs : Epi (M.freeHomEquiv.symm s),
          IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I f M s hs) ∧
          Nonempty (ProjectiveSpace.twistRestrict
            (ProjectiveSpace.homOfGeneratingSections I f M s hs) 1 ≅ M) := by
  sorry

end AlgebraicGeometry.Scheme
