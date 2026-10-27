/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Character tangent weights at fixed points of a scheme

Source: Milne, Algebraic Groups (2017), p.272, convention before Theorem 13.47;
Corollary 13.48, p.273; Stacks Tag 0B2C.
(blueprint: def-sfb-fixed-point-tangent-weights).

This extends the group-scheme-only tangent-weight interface to arbitrary schemes.
The tangent space and its vector-space structure are the existing schemeTangentSpace.
At a rational fixed point over an algebraically closed field, the equations below
are the usual character eigenspaces. Taking their residue-linear span gives honest
submodules without postponing any proof or choosing any new tangent-space operations.
Only rational fixed points are used by the attracting-cell theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveAttractingCells

/-- The scalar map F to the residue field at p, induced by the structural morphism.
Source: Milne, tangent convention before 13.47, p.272; Stacks Tag 0B2C
(blueprint: def-sfb-fixed-point-tangent-weights). -/
def residueScalars {F : Type u} [Field F] (X : Over (Spec (.of F))) (p : X.left) :
    F →+* X.left.residueField p :=
  (StructureSheaf.toStalk F (X.hom p) ≫ X.hom.stalkMap p ≫ X.left.residue p).hom

/-- The dual-number spectrum over F used by the existing scheme tangent space.
Source: Stacks Tag 0B2C (blueprint: def-sfb-fixed-point-tangent-weights). -/
def tangentBase {F : Type u} [Field F] (X : Over (Spec (.of F))) (p : X.left) :
    Over (Spec (.of F)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom (X.left.residueField p)
    (X.left.residueField p))) ≫ X.left.fromSpecResidueField p ≫ X.hom)

/-- A vector's actual dual-number point, retaining its base equation.
Source: Stacks Tag 0B2C (blueprint: def-sfb-fixed-point-tangent-weights). -/
def tangentPoint {F : Type u} [Field F] {X : Over (Spec (.of F))} {p : X.left}
    (v : schemeTangentSpace F X.left X.hom p) : tangentBase X p ⟶ X :=
  Over.homMk v.val v.property.2

/-- Character-weight a in T_p X. The action is tested on actual tangent points and the
character is t to the integer power a, including in positive characteristic. Over the
algebraically closed base these eigenspaces are residue-linear subspaces, so span does
not enlarge them. This uses the existing tangent space, dual to m_p / m_p squared.
Source: Milne, p.272, convention before 13.47 and Corollary 13.48
(blueprint: def-sfb-fixed-point-tangent-weights). -/
def weightSpace {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X) (p : X.left) (n : ℤ) :
    Submodule (X.left.residueField p) (schemeTangentSpace F X.left X.hom p) :=
  Submodule.span (X.left.residueField p) {v | ∀ t : Fˣ,
    lift (toUnit (tangentBase X p) ≫
      StandardGroupSchemes.identitySection F
        { toRingHom := LaurentPolynomial.eval₂ (RingHom.id F) t
          commutes' := fun r ↦ LaurentPolynomial.eval₂_C _ _ r })
      (tangentPoint v) ≫ a.smul =
        tangentPoint ((residueScalars X p ((t ^ n : Fˣ) : F)) • v)}

/-- The sum of the strictly positive character-weight spaces.
Source: Milne, p.272, Tgt-positive, and Corollaries 13.48--13.49
(blueprint: def-sfb-fixed-point-tangent-weights). -/
def positiveSpace {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X) (p : X.left) :
    Submodule (X.left.residueField p) (schemeTangentSpace F X.left X.hom p) :=
  ⨆ (n : ℤ) (_ : 0 < n), weightSpace a p n

end AlgebraicGeometry.ProjectiveAttractingCells
