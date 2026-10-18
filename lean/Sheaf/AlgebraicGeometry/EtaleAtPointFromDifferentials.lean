/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.GroupTheory.MonoidLocalization.Away
import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Étaleness from prescribed coordinate differentials

Source: Stacks Project, `morphisms.tex`, Tag 02GU (lemma-etale-at-point), condition (8),
Tag 01V7 (lemma-smooth-locally-standard-smooth), and `algebra.tex`, Tag 00T7
(lemma-standard-smooth), part (2)
(blueprint: lem-pur-etale-at-point-from-differentials).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A prescribed coordinate map on a smooth finite-type scheme over a field is étale on an
open neighbourhood of a point if its coordinate differentials form a basis of the cotangent
fibre there. `IsLocalRing.ResidueField (U.presheaf.stalk x)` is definitionally the field
`U.residueField x`. The tensor product has the residue field on the left, using the canonical
commutativity identification with the order in the source.
Source: Stacks Project, Tags 02GU(8), 01V7 and 00T7(2)
(blueprint: lem-pur-etale-at-point-from-differentials).

Proof:
1. Use `lem-weil-pbc-smooth-locally-standard-smooth` to choose an affine neighbourhood
   `Spec A` of the point with a standard smooth presentation
   `A = k[y_1,...,y_n]/(F_1,...,F_r)` and invertible first `r` Jacobian minor.
2. By `lem-weil-pbc-standard-smooth-kahler-basis`, the differentials of the remaining
   `n-r` variables form a basis. The affine differential-sheaf description and
   `lem-weil-pbc-spec-tilde-stalk-localization` identify its residue-field base change
   with the differential fibre in the hypothesis. Comparing bases gives `d = n-r`.
3. Lift the given functions to polynomials `H_j`. Over `R = k[T_1,...,T_d]`, the same
   algebra has the graph presentation `R[y]/(F_1,...,F_r,H_1-T_1,...,H_d-T_d)`.
   Evaluation of the `T_j` gives the presentation and its inverse; there are `n` equations.
4. Write the square Jacobian in blocks `B,C,D,E`, with `B` the invertible `r`-minor.
   The derivation rules give `B dy_first + C dy_last = 0`, so the prescribed differential
   basis has matrix `E-D B⁻¹ C` in the standard basis after reduction to the residue field.
   It is invertible. Block row elimination shows the whole determinant `Delta` is nonzero
   at the point. Empty blocks have determinant one, covering `r=0` and `d=0`.
5. Localize at the image of `Delta`. Adjoin a variable `t` and the relation `Delta*t-1`.
   This presents the localization with a square Jacobian of determinant `Delta^2`, a unit.
6. `lem-exc-etale-jacobian-presentation` makes this algebra étale over `R`.
   `lem-weil-pbc-etale-ring-map-iff-etale-affine` makes its spectrum étale over affine space,
   and `lem-weil-pbc-principal-localization-open-immersion` identifies it with the required
   principal open containing the point. Each `T_j` still maps to the original function,
   so this is the restriction of the prescribed map, not a different coordinate map. -/
theorem Scheme.exists_etale_open_of_coordinate_differentials_basis
    (k : Type u) [Field k] (U : Scheme.{u}) [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [Smooth (U ↘ Spec (.of k))] (x : U) (d : ℕ) (h : Fin d → Γ(U, ⊤))
    (hbasis : ∃ b : Module.Basis (Fin d) (IsLocalRing.ResidueField (U.presheaf.stalk x))
        (IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[U.presheaf.stalk x]
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
            (U ↘ Spec (.of k)).relativeDifferentials)),
      ∀ j : Fin d, b j = TensorProduct.tmul (U.presheaf.stalk x)
        (N := (RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
          (U ↘ Spec (.of k)).relativeDifferentials)
        (1 : IsLocalRing.ResidueField (U.presheaf.stalk x))
        ((U ↘ Spec (.of k)).relativeDifferentials.presheaf.germ ⊤ x trivial
          ((U ↘ Spec (.of k)).relativeDifferentialsDerivation.d (h j)))) :
    ∃ V : U.Opens, x ∈ V ∧
      Etale (V.ι ≫ AffineSpace.homOfVector (U ↘ Spec (.of k))
        (fun j : ULift.{u} (Fin d) ↦ h j.down)) := by
  sorry

end AlgebraicGeometry
