/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Surjectivity of relatively flat single base change

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor.
(blueprint: lem-pc-standard-flat-single-base-change-epi).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical single-module base-change comparison is surjective on cohomology.

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor, specialized to
E = O_Y[0] and G = M[0], and Tag 0DJ9, lemma-single-complex-base-change.
(blueprint: lem-pc-standard-flat-single-base-change-epi).

Proof: Work locally on the new base and the original base, so both bases are
affine. On an affine source chart, relative flatness of M makes its module of
sections flat over the original base ring. The affine derived direct image is
therefore a flat module in degree zero; derived scalar extension computes it by
ordinary tensor product. The affine tensor-pullback section formula identifies
that tensor product with the sections of the pulled-back module. The canonical
mate followed by the left-derived counit is precisely this section comparison:
its component in degree zero is the tensor identification, and all other
cohomology objects are zero. In particular its degree-n map is surjective.
For a general qcqs source, use the single-complex source-open induction of
Tag 0DJ9: compare the two Mayer--Vietoris triangles for U, V, their intersection
and union. The affine comparisons identify the local tensor-cohomology maps;
relative flatness makes them valid at every stalk, including on the
intersection. The long exact cohomology sequences and the five lemma propagate
the comparison along the quasi-compact-open induction. Take the surjectivity half
of that degree-n conclusion. Finally exact open restriction detects epimorphisms
and gives the asserted global epimorphism. This argument includes zero M,
empty schemes, and negative n, and assumes neither flatness of g nor intrinsic
flatness of M over O_Y. -/
theorem standard_flat_single_baseChange_homology_epi
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (n : ℤ) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings A.toRingedSpace)) n).map
        (standardSingleBaseChangeMap p M g)) := by sorry

end AlgebraicGeometry
