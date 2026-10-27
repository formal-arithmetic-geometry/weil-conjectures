/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A Clifford support subcurve for a special very ample line

Source: Morrison, GIT constructions of moduli spaces of stable curves and maps,
Section 3.2, proof step (7), printed p. 14; Gieseker, Proposition 1.0.8,
printed pp. 61--62; Stacks Project, curves.tex, Tags 0BS2, 0BS4, 0BS6 and 0E33.
(blueprint: lem-sfb-nodal-special-clifford-subcurve).

The finite family in the conclusion enumerates the reduced irreducible components
of the support subcurve exactly once. Its degree is the sum on their canonical
normalizations. The dimension inequality is written without division, over the integers.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A special very ample line on a connected projective nodal curve has a nonempty
connected reduced component union satisfying the Clifford bound and having degree at least two.
Source: Morrison, Section 3.2, proof step (7), p. 14; Gieseker, Proposition 1.0.8,
pp. 61--62; Stacks Project, curves.tex, Tags 0BS2, 0BS4, 0BS6 and 0E33
(blueprint: lem-sfb-nodal-special-clifford-subcurve).

Proof plan:
1. By lem-sfb-nodal-line-serre-riemann-roch, nonzero H¹ gives a nonzero map L → omega_D.
   Projectivity gives properness (lem-pc-projective-proper), hence finite type over the
   Noetherian field spectrum. Apply lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-noetherian-finitely-many-components. Choose a map with the fewest nonzero
   component generic values. Reducedness makes its component support Y nonempty and shows
   that its image is killed by I_Y. The canonical injection of
   lem-sfb-nodal-subcurve-dualizing-annihilator factors it through omega_Y.
2. If Y were disconnected, restrict to a connected component where the map is nonzero
   and extend by zero on the other open and closed components. The same injection would
   produce a map on D with smaller support. Thus Y is connected. Minimality also implies
   that every nonzero section of omega_Y tensor (L|Y) inverse is generically nonzero on
   every component of Y.
3. Set V = H⁰(Y,L|Y), W = H⁰(Y,omega_Y tensor (L|Y) inverse), and g = h¹(Y,O_Y).
   Reducedness and the preceding generic nonvanishing show multiplication V × W → H⁰(omega_Y)
   has no zero products. Nodal Serre duality and Riemann--Roch give dim W > 0,
   h⁰(omega_Y) = g and dim V - dim W = e + 1 - g, where e is the sum of degrees on
   normalized components. Apply lem-sfb-hopf-bilinear-image-dimension to obtain
   dim V + dim W - 1 ≤ g. Eliminating dim W gives 2 dim V ≤ e + 2.
4. Restrict the projective embedding to Y, using lem-weil-pbc-closed-immersion-comp.
   Its coordinate sections generate L|Y. If h⁰ were zero they could not generate; if it
   were one the embedding would be constant, impossible for a nonempty pure curve.
   Hence h⁰ ≥ 2 and e ≥ 2. Enumerate the finitely many reduced integral components of Y
   to express their normalized-component degree sum in the displayed conclusion.
-/
theorem exists_nodal_special_clifford_subcurve
    (k : Type u) [Field k] [IsAlgClosed k]
    (D : Scheme.{u}) (f : D ⟶ Spec (.of k)) [IsHProjective f]
    [ConnectedSpace D] [IsReduced D] (hpure : D.IsPureDimension 1)
    (hnodal : ∀ x : D, x ∉ f.smoothLocus →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk x))
          (D.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)})))
    (L : D.Modules) [L.IsInvertible] (hvery : IsVeryAmple f L)
    (hspecial : Nontrivial ((RingedSpace.moduleCohomology D.toRingedSpace 1).obj L)) :
    ∃ (Y : Scheme.{u}) (i : Y ⟶ D),
      IsClosedImmersion i ∧ IsReduced Y ∧ ConnectedSpace Y ∧
      (∃ S : Set (Set D), S ⊆ irreducibleComponents D ∧ Set.range i = ⋃₀ S) ∧
      ∃ (m : ℕ) (Z : Fin m → Scheme.{u}) (hZ : ∀ a, IsIntegral (Z a))
        (j : ∀ a, Z a ⟶ Y),
        (∀ a, IsClosedImmersion (j a)) ∧
        Function.Injective (fun a ↦ Set.range (j a)) ∧
        (∀ C : Set Y, C ∈ irreducibleComponents Y ↔ ∃ a, Set.range (j a) = C) ∧
        ∃ e : ℤ,
          e = ∑ a : Fin m,
            @Scheme.Modules.degree k _ (@Scheme.normalization (Z a) (hZ a))
              ⟨@Scheme.fromNormalization (Z a) (hZ a) ≫ j a ≫ i ≫ f⟩
              ((Scheme.Modules.tensorPullback
                (@Scheme.fromNormalization (Z a) (hZ a) ≫ j a ≫ i)).obj L) ∧
          2 ≤ e ∧
          2 * (Module.finrank k
            ((RingedSpace.moduleCohomology Y.toRingedSpace 0 ⋙
              ModuleCat.restrictScalars
                ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom).obj
                  ((Scheme.Modules.tensorPullback i).obj L)) : ℤ) ≤ e + 2 := by
  sorry

end AlgebraicGeometry
