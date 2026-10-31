/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import WeilConjectures.AlgebraicGeometry.SectionBoundaryExact
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import WeilConjectures.AlgebraicGeometry.PointTangentSeparationClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Numerical very ampleness on a nodal curve

Source: Franciosi--Tenni, The canonical ring of a 3-connected curve (2014),
Section 2, Proposition 2.5(iii), printed p. 40, specialized to nodal curves
(blueprint: lem-sfb-nodal-numerical-very-ample).

Every nonempty reduced component union is tested, including disconnected ones.
The arithmetic genus is the integer `1 - chi(O)`. The conclusion uses a basis of
all global sections, so its projective morphism is the complete linear system.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The degree bound on every nonempty reduced component union makes an invertible
module very ample in the complete-linear-system sense.
Source: Franciosi--Tenni (2014), Section 2, Proposition 2.5(iii), printed p. 40;
Stacks Project, curves.tex, Tags 0E3E and 0E8X; varieties.tex, Tags 0E8T and 0E8S
(blueprint: lem-sfb-nodal-numerical-very-ample).

Proof plan:
1. By lem-kun-projective-implies-proper the structure map is proper, hence finite type.
   By lem-trf-proper-field-invertible-coherent the curve is Noetherian. A nonempty
   zero-dimensional closed test subscheme Z of degree at most two is finite affine,
   by lem-pc-zero-dimensional-closed-subscheme-finite.
2. If H^1(I_Z tensor A) were nonzero, lem-sfb-curve-ideal-h1-subcurve-obstruction
   would give a nonempty connected reduced subcurve B with
   deg(A|B) <= -2 chi(O_B) + length(Z intersection B). Its dimension-one components
   are ambient components, and connectedness excludes isolated zero-dimensional
   components. Thus B is a component union. Its intersection with Z is Spec(R/J),
   where Z = Spec R, so its length is at most two, including an empty intersection.
   The resulting bound deg(A|B) <= 2 p_a(B) contradicts the numerical hypothesis.
3. Tensor the closed-immersion ideal sequence with the invertible A. By
   lem-sc-module-section-boundary-exact, H^1(I_Z tensor A) = 0 makes restriction
   of global sections to Z surjective. Direct image identifies the quotient sections
   with the sections on Z (def-sbc-closed-immersion-ideal-sheaf and def-pc-module-pullback).
4. Closed points are k-rational by lem-weil-pbc-closed-point-residue-field-base.
   Degree-one tests give generation at closed points; two distinct reduced points
   give point separation. A nonzero tangent vector gives a surjection onto the dual
   numbers: its image contains k and epsilon. Its kernel, extended by the unit ideal
   off the point, gives a degree-two closed test subscheme. Lift epsilon times a
   local frame to obtain a section with nonzero derivative in that direction.
5. Apply lem-sc-point-tangent-separation-closed-immersion to the full section space.
   It is finite-dimensional, and a basis generates A and defines a closed immersion
   pulling back O(1) to A. Identify the resulting coordinate projective space with
   P(H^0(X,A)^dual). No Cartier hypothesis on Z or smooth-curve-only criterion is used.
-/
theorem nodal_numerical_very_ample
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsHProjective f]
    [ConnectedSpace X] [IsReduced X] (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, x ∉ f.smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)
            (X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C a))
    (A : X.Modules) [A.IsInvertible]
    (hdegree : ∀ (B : Scheme.{u}) (i : B ⟶ X),
      IsClosedImmersion i → IsReduced B → Nonempty B →
      (∃ S : Set (Set X), S ⊆ irreducibleComponents X ∧ Set.range i = ⋃₀ S) →
      2 * (1 - @Scheme.Modules.eulerChar k _ B ⟨i ≫ f⟩
        (SheafOfModules.unit B.ringCatSheaf)) + 1 ≤
        @Scheme.Modules.degree k _ B ⟨i ≫ f⟩
          ((Scheme.Modules.tensorPullback i).obj A)) :
    ∃ (I : Type u) (_ : Finite I)
      (b : Module.Basis I k ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          (A.val.obj (Opposite.op ⊤))))
      (s : I → A.sections),
      (∀ i : I, (s i).val (Opposite.op ⊤) = b i) ∧
      ∃ hs : Epi (A.freeHomEquiv.symm s),
        IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I f A s hs) ∧
        Nonempty ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.homOfGeneratingSections I f A s hs)).obj
            (ProjectiveSpace.twist I (Spec (.of k)) 1) ≅ A) := by
  sorry

end AlgebraicGeometry
