/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenCechResolutionDoubleComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import Sheaf.CategoryTheory.InjectiveSheafCechAcyclic

/-! # Total homology of the étale open Čech resolution

Source: Stacks Project, Tags 03AW, 03F6 and 03AZ.
(blueprint: lem-sc-etale-open-cech-resolution-total)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The total Čech complex of an injective resolution over an open covering
computes derived evaluation, without affineness or acyclicity of G on opens.

Source: Stacks Project, Tags 03AW, 03F6 and 03AZ, the augmentation comparison.
(blueprint: lem-sc-etale-open-cech-resolution-total)

Proof: Cover preservation sends the open covering to a covering of i(top).
Preservation of finite limits identifies iterated fibre products of this image
cover with i of the intersections of opens, compatibly with all projections.
Thus each horizontal Čech row of the displayed double complex is the Čech
complex of the corresponding injective étale sheaf on this cover. Augment it by
its sections at i(top). The sheaf condition identifies degree-zero homology with
those sections, and injective Čech acyclicity (03AW, 03F6) gives zero positive
homology. The restriction augmentations commute with the resolution differential
and define a map from the evaluated resolution to the total complex. The
horizontal differential on its image is zero and the vertical sign in Čech
degree zero is +1. Filter its cone by resolution degree: its rows are exact
augmented Čech complexes. The first-quadrant boundedness makes the filtration
finite in each total degree, so the row spectral sequence of the cone has zero
abutment. Therefore the augmentation is a quasi-isomorphism. Finally the
injective-resolution computation of rightDerived identifies homology of the
evaluated resolution with derived evaluation. Compose with the inverse of the
augmentation homology isomorphism. This includes empty coverings: the sheaf
condition then forces sections at i(top) of all resolution terms to be zero.
No separatedness or affine vanishing is involved. -/
theorem nonempty_etale_openCech_resolution_total_iso
    (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (I : InjectiveResolution G) (n : ℕ) :
    Nonempty (((etaleOpenCechResolutionDoubleComplex X i U I).total (.up ℕ)).homology n ≅
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (i.obj ⊤))).rightDerived n).obj G)) := by sorry

end AlgebraicGeometry.Scheme
