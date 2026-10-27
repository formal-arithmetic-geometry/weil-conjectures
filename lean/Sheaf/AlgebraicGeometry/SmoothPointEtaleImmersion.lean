/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20, SHEAF group Q58
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.TraceFormula.SmoothSeparableHypersurfaceSlice
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-! # Smooth fibre points admit étale immersion slices

Source: Stacks Project, Tag 057G, lemma-slice-smooth.
(blueprint: lem-trf-smooth-point-etale-immersion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth morphism admits an étale immersion slice through a closed fibre point
with finite separable residue extension, with singleton fibre over the base point.
Source: Stacks Project, Tag 057G (blueprint: lem-trf-smooth-point-etale-immersion).
Both extension properties use the algebra induced by the specified residue map.

Proof:
1. Smoothness gives local finite presentation (def-sbc-smooth-morphisms and
   def-sbc-locally-finite-presentation). Choose affine charts around `x` and `f x`.
   By lem-trf-affine-fibre-point-dimension their fibre has a finite nonnegative
   dimension `d` at `x`. Induct strongly on `d`, simultaneously for all smooth
   morphisms and all closed fibre points with finite separable residue extension.
2. If `d = 0`, apply lem-trf-smooth-zero-dimensional-singleton-open with `W = X`.
   Its open neighbourhood gives the immersion, étaleness and singleton fibre.
3. If `d > 0`, lem-trf-smooth-separable-hypersurface-slice gives an affine open
   neighbourhood `U` and a Cartier divisor `D` through `x`, smooth over the base,
   whose fibre dimension at the lifted point is `d - 1`. Closed-immersion base
   change (lem-weil-pbc-proper-fp-permanence (b)) makes its fibre closed in `U_s`.
   Its point is closed since it is the inverse image of the closed singleton
   in `X_s`. Closed and open immersions preserve residue fields by
   lem-weil-pbc-closed-immersion-residue-field-iso and
   lem-weil-pbc-residue-field-point-naturality. Functoriality of residue maps
   (def-weil-residue-field) respects the base-field algebra, so the new extension
   is again finite separable.
4. Apply induction to `D → S`. Compose its immersion with `D → U → X`, using
   lem-weil-pbc-proper-fp-permanence (e). It sends the chosen point to `x`.
   The map to `S` and its singleton fibre are precisely those from induction. -/
theorem Smooth.exists_etale_immersion_slice
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (hx : IsClosed {f.asFiber x})
    (h : @Module.Finite (S.residueField (f x)) (X.residueField x) _ _
        (@Algebra.toModule _ _ _ _ (f.residueFieldMap x).hom.toAlgebra) ∧
      @Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) _ _
        (f.residueFieldMap x).hom.toAlgebra) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z), IsImmersion i ∧ i z = x ∧
      Etale (i ≫ f) ∧
      Set.range ((i ≫ f).fiberι (f x)) = Set.singleton z := by
  sorry

end AlgebraicGeometry
