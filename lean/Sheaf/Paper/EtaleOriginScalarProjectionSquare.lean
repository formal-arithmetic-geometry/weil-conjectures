/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W6
-/
module

public import Sheaf.Paper.ProperEtaleOriginScalarData
import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale

/-! # Scalar restriction of the etale-origin projection square

Source: Stacks Project, Tags 0E48 and 0B56. This is a compatibility of specified
maps for a qcqs morphism; it does not assert a projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Etale.scalarTensorIso Scheme.completedAdicDerivedChange

/-- The etale projection and the restricted scalar mate give the same square
through the canonical tensor comparisons and the bounded-below direct-image mates.
The morphism is only required to be qcqs. In particular, this statement neither
uses properness nor claims that either projection morphism is invertible.

Source: Stacks Project, sites-cohomology.tex, Tag 0E48,
remark-compatible-with-diagram, and Tag 0B56, equation-projection-formula-map;
proetale.tex, Tag 09A6.
(blueprint: lem-fix-etale-origin-scalar-projection-square).

Proof: apply projection_comparison_etale_proetale to E and the constant A-module
B_Y in degree zero. The canonical coefficient pullback identifies E tensor p*B_Y
with H = E tensor B_Z; its two bounds are exactly the assumptions. The comparison
square uses the included fixed counit mates at E and H. Transport that square
through the intrinsic coefficient-realization equivalences. On ordinary sections
the realization, restriction, and direct-image comparisons are the identity;
on flat K-flat total tensors the tensor/scalar comparisons send each x tensor b
to the same balanced tensor. The uniqueness in their representative normalizations
therefore identifies the transported tensor maps with properOriginTensorIso and
the transported direct-image maps with properOriginMateIso. Naturality moves the
coefficient-pullback identification past the target mate. Finally apply
proEtaleScalarMateNormalization: its restriction/direct-image factor is precisely
scalarMateRestrictionPush and its projection is the transported pro-etale projection.
Cancel the intermediate realization and tensor identifications. The remaining
inverse-free square is the displayed equation. This uses only the bounds on E and H,
not on scalar extension of the direct image, and applies to zero coefficient rings
and to identity morphisms as well.
-/
theorem etaleOriginScalarProjectionSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (E : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hH : ∃ n : ℤ,
      (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj).IsGE n) :
    (properOriginTensorIso φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          E.obj)).hom ≫
      (directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory).map
        (properOriginMateIso A p E).hom ≫
      (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((directImageScalarComparison φ p).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ≫
      (scalarMateRestrictionPush φ p).hom.app
        ((directImageScalarExtension φ Z).obj
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) =
    (finiteCoefficientIntrinsicDerivedComparison Y A).map
        (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
      (properOriginMateIso A p
        ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
      (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
  sorry

end AlgebraicGeometry.ProEtale
