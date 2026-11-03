/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData

/-!
# Intrinsic compact-support restriction of scalars

Source: Stacks Project, Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).

The open comparison is the published section-normalized intrinsic comparison.
The proper comparison is the inverse of the published K-injective-normalized ring-sheaf
comparison. Their composite acts on exactly the compact-support functors used by b.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The specified compact-support restriction comparison on intrinsic constant-ring modules.
Source: Stacks Tags 03DI and 0D6E
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
def intrinsicCompactSupportRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (h : Z ⟶ Y) :
    scalarRestriction φ X ⋙ reductionCompactSupport A j h ≅
      reductionCompactSupport B j h ⋙ scalarRestriction φ Y :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ))
      (directImageConstantPush A h) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j B).mapDerivedCategory
      (proEtaleRingRestrictionDerivedDirectImage h
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
        (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift φ))).symm).symm

end AlgebraicGeometry.ProEtale
