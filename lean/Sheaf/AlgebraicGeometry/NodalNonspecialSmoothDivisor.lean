/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected
import Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier

/-! # Nonspecial divisors on nodal curves

Source: Deligne, Le lemme de Gabber, Astérisque 127 (1985), Lemma 4.4, printed p.143.
(blueprint: lem-sfb-nodal-nonspecial-smooth-divisor).

The disjoint-union description records a sum of distinct rational points scheme-theoretically.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- A projective geometrically reduced, geometrically connected nodal curve over a separably
closed field has a nonspecial effective Cartier divisor of degree its arithmetic genus,
supported at distinct smooth rational points. In genus zero it is the empty divisor.
The canonical constants map on global sections is bijective, hence is a linear isomorphism.

Source: Deligne, Le lemme de Gabber, Lemma 4.4, printed p.143; the distinctness refinement
avoids the previously chosen finite set of points.
(blueprint: lem-sfb-nodal-nonspecial-smooth-divisor).

Proof (the node's steps):
1. Projectivity gives properness, finite type, Noetherianity and finite presentation;
   flatness holds over a field. Connectedness and reducedness exclude isolated
   zero-dimensional components, so the curve is pure of dimension one. Proper coherent
   cohomology is finite-dimensional and vanishes above degree one. Geometric reducedness
   and connectedness give H^0(O_X)=k; thus chi(O_X)=1-g.
2. The Gorenstein relative-dualizing theorem supplies an invertible dualizing module.
   Uniqueness in the reduced-curve dualizing-pair theorem identifies it with omega_X;
   duality gives dim Gamma(omega_X)=g and detects maps at component-generic stalks.
3. A nonzero section of omega_X is nonzero at a component-generic point. Trivialize
   there and restrict to its nonvanishing open. Intersect the dense smooth locus and
   remove any previously chosen finite set. This open is nonempty; density of rational
   points on smooth schemes over separably closed fields supplies a new rational point
   where the section evaluates nontrivially.
4. Inductively choose g such points. Each nonzero evaluation on the remaining subspace
   of sections has one-dimensional image and lowers its dimension by one, leaving zero
   after g choices. For g=0 the family is empty from the start.
5. Their reduced disjoint union is a Cartier divisor on the smooth curve locus by the
   Cartier criterion, and extends across its complement with local equation 1. Its
   associated line module is the dual of the ideal, and its degree is g by the effective
   Cartier degree formula. The empty union has the unit ideal and degree zero.
6. Precomposition with O_X -> O_X(E) identifies Hom(O_X(E),omega_X) with sections
   vanishing at the chosen points, hence with the zero subspace constructed in step 4.
   Serre duality and finite-dimensionality give H^1(O_X(E))=0.
7. Riemann--Roch in Euler-characteristic form now gives h^0(O_X(E))=g+1-g=1.
   The canonical map sends 1 to the nonzero ideal inclusion (locally multiplication
   by a nonzerodivisor), so it is injective and then bijective. For g=0 these assertions
   reduce to the global-functions isomorphism and H^1(O_X)=0. -/
theorem exists_nodal_nonspecial_smooth_divisor (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [Nonempty X]
    [IsHProjective (X ↘ Spec (.of k))]
    [GeometricallyReduced (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasNodalGeometricFibres (X ↘ Spec (.of k)))
    (g : ℕ) (hg : g = Module.finrank k
      ((Scheme.Modules.moduleCohomologyOverField k X 1).obj (Scheme.Modules.unit X))) :
    ∃ J : X.IdealSheafData, J.IsInvertible ∧
      (∀ x : J.subscheme, J.subschemeι x ∈ (X ↘ Spec (.of k)).smoothLocus) ∧
      J.toModulesᵛ.degree k = (g : ℤ) ∧
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj J.toModulesᵛ) ∧
      Function.Bijective (fun a : k ↦
        ((SheafOfModules.homObjSectionsEquiv J.toModules (Scheme.Modules.unit X)).symm
          (a • J.toModulesι)).1 (op ⊤)) ∧
      (∃ e : (∐ fun _ : Fin g ↦ Spec (.of k)) ≅ J.subscheme,
        e.hom ≫ J.subschemeι ≫ X ↘ Spec (.of k) =
          Sigma.desc (fun _ : Fin g ↦ 𝟙 (Spec (.of k)))) ∧
      (g = 0 → J = ⊤) := by
  sorry

end AlgebraicGeometry
