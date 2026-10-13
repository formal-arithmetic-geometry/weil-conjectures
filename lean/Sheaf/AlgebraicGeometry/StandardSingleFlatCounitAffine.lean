/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation

/-! # Affine case of flat counit presentations

Source: Stacks Project, Tags 0A1D and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Affine source charts have bounded flat presentations over affine bases.
Source: Stacks Project, Tag 0A1D, affine tensor calculation; Tag 0DJ9,
initial affine case. (blueprint: lem-pc-standard-single-flat-counit-affine).

Proof: Identify the three affine schemes U, B and A with spectra of their section
rings. The one-member affine cover of U has alternating section complex N(U) in
degree zero and zero in all other degrees. Relative flatness evaluated on the
top opens makes N(U) flat over the section ring of B. Sheafify this module on B;
its stalks are localizations, so it is a flat sheaf, and take its single complex K.
Affine direct image of a quasi-coherent module is acyclic; the augmentation gives
e identifying Rp_*N[0] with QK. On the pulled-back affine chart the pure-tensor
section formula identifies ordinary g-pullback of K with the target, giving t.
The formula sends b tensor n to b times the pulled-back section n and commutes
with the augmentation. Transpose the canonical mate under the derived adjunction
for the source pullback. Naturality and the two triangle identities cancel its
units and leave that pure-tensor section map. Thus its composite with the pinned
single pullback counit is Lg*(e) followed by the pinned counit at K and t.
Transport along the affine-spectrum isomorphisms using the derived composition
comparisons; their defining counit equations preserve this equality. Bound K by
zero. If U is empty its section ring is zero and the same single complex is zero.
No flatness of g or invertibility of a counit is assumed. -/
theorem standardSingleFlatCounitOnOpen_affine
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [IsAffine B] [IsAffine A]
    (g : A ⟶ B) (U : Y.Opens) (hU : IsAffineOpen U) :
    StandardSingleFlatCounitOnOpen p g U := by sorry

end AlgebraicGeometry
