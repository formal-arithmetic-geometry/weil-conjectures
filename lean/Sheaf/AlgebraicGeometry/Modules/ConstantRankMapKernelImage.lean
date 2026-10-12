/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import Sheaf.LinearAlgebra.MatrixRankFieldExtension
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Kernel and image of a constant rank map on a reduced scheme

Source: `thm-pc-semicontinuity-base-change`, proof (3), reduced-ring normal form.
(blueprint: lem-pc-constant-rank-map-kernel-image)
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A constant rank map between finite free sheaves has a finite locally free kernel
and image, and its image inclusion admits retractions locally on the open subscheme.

Source: `thm-pc-semicontinuity-base-change`, proof (3), normal-form claim.
(blueprint: lem-pc-constant-rank-map-kernel-image)

Proof: Restrict to affine neighbourhoods inside the open subscheme. Its affine rings are
reduced. A field-valued point with singleton image factors through the residue field of
that point; matrix rank is invariant under field extension. Thus all (a+1)-minors vanish
in every residue field. Each such minor belongs to every prime ideal, hence to the
nilradical, and reducedness makes it zero. At any point choose a nonvanishing a-minor
and shrink to its principal open. Permute rows and columns to make that minor the leading
block. Invertible row and column operations replace the matrix by diag(I_a,S), where S
is the Schur complement. Its entries are (a+1)-minors divided by the chosen unit minor,
so S is zero. The kernel is free of rank m-a and the image free of rank a on this open.
Projection onto the first a target coordinates is a retraction of the image inclusion.
These neighbourhoods cover the open subscheme and yield both local freeness assertions.
For a=0 the empty minor is 1 and reducedness forces the entire matrix to vanish. If the
open subscheme is empty all covering and neighbourhood conditions are vacuous. -/
theorem kernel_image_pullback_of_constantRank
    {Y Z : Scheme.{u}} [IsReduced Y] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank = a) :
    (kernel ((Modules.pullback j).map φ)).IsFiniteLocallyFreeOfRank (m - a) ∧
    (Abelian.image ((Modules.pullback j).map φ)).IsFiniteLocallyFreeOfRank a ∧
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map
        (Abelian.image.ι ((Modules.pullback j).map φ))) := by sorry

end AlgebraicGeometry.Scheme.Modules
