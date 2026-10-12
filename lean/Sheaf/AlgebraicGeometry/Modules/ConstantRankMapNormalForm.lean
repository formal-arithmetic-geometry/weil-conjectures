/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Sheaf.LinearAlgebra.MatrixRankFieldExtension

/-! # Local block normal form of a constant rank sheaf map

Source: `thm-pc-semicontinuity-base-change`, proof (3), reduced-ring normal form.
(blueprint: lem-pc-constant-rank-map-local-normal-form)
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A constant rank map on an open part of a reduced scheme is locally a projection
followed by an inclusion, in finite free bases.

Source: `thm-pc-semicontinuity-base-change`, proof (3), normal-form claim;
`lem-pc-constant-rank-map-kernel-image`, proof steps 1 and 2.
(blueprint: lem-pc-constant-rank-map-local-normal-form)

Proof: Restrict the chosen bases to an affine neighbourhood in Z. A field-valued point
with singleton image factors through the residue field at that image. The induced
extension of residue fields preserves matrix rank. Thus the matrix has rank a over
all residue fields of this affine ring. Every (a+1)-minor belongs to every prime ideal,
hence to the nilradical, and is zero because the ring is reduced. At the chosen point
some a-minor is nonzero. Shrink to its principal open and permute the corresponding
rows and columns into the leading block B. This block is invertible. Multiply by
invertible block row and column matrices to reduce the original matrix to
 diag(I_a, D-C B⁻¹ E). Each entry of the second block times det B is, up to sign,
an (a+1)-minor, so the second block is zero. Order the source coordinates with its
m-a zero coordinates first, and its a pivot coordinates last; order the target
coordinates with its a pivot coordinates first. These basis changes give the two
isomorphisms in the statement and the displayed factorization. For a=0 the empty
minor is 1 and the matrix is zero. A point of Z ensures a ≤ m and a ≤ n. For empty
Z the pointwise assertion is vacuous. All objects are ordinary restrictions and free
sheaves; no kernel or image local-freeness assertion is used. -/
theorem exists_local_normal_form_of_constantRank
    {Y Z : Scheme.{u}} [IsReduced Y] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank = a) :
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin (m - a))) ⊞ free (ULift.{u} (Fin a)))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
          eS.hom ≫ biprod.snd ≫ biprod.inl ≫ eT.inv := by sorry

end AlgebraicGeometry.Scheme.Modules
