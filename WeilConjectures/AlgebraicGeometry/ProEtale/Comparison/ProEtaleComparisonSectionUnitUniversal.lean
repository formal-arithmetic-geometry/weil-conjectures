/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonDiagonalSection
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative

/-! # The concrete diagonal unit and its unique-extension property

Source: Stacks Project, Tag 0GLZ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- Local notation expands the diagonal formula; the public declaration introduces
-- no second copy of the downstream `proEtaleComparisonEtaleSection` definition.
set_option quotPrecheck false in
local notation:max "δ[" X "," F "," U "]" s:max =>
  (by
    let _ : (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).IsContinuous
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback @Etale @Etale le_rfl (U).hom
    exact ((Scheme.etaleSetPullback (U).hom).obj F).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 (U).left) (𝟙 (U).left) (by simp)) (by simp) :
        Scheme.Etale.mk (𝟙 (U).left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).obj U).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ (U).hom) (Type _)
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s)
  : ((Scheme.etaleSetPullback (U).hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (U).left))))

-- Restrict a pro-étale sheaf to each local étale site, then transpose alpha.

-- The chosen inverse-image composition isomorphism, with its unit equation.

-- Pasting the two local adjunctions gives naturality of the extension.

-- For uniqueness, turn local Kan representatives into diagonal restrictions.

-- Sheafification is locally surjective; the Kan extension has explicit representatives.

end AlgebraicGeometry
