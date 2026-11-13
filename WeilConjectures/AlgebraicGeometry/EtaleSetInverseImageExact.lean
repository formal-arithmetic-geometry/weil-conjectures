/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

/-!
# Exact inverse image of set-valued small etale sheaves

Source: Stacks Project, Lemma 59.36.2 (Tag 03Q1), assertion (2), and Definition
59.36.1 (Tag 03PZ); Sites, Definition 00X1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The inverse image is left Kan extension followed by sheafification, as in
`Scheme.etaleSetPullback`. The direct image is precomposition with base change, hence its
sections over `V` are `F(V ×_T T')` (Stacks, Tags 03Q1, 03PZ, 00X1). -/
theorem etaleSetInverseImage_exact {T T' : Scheme.{u}} (h : T' ⟶ T) :
    (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
      (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale) ∧
    Nonempty
      (Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
        (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale) ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ h).sheafPushforwardContinuous
        (Type (u + 1)) (T.smallGrothendieckTopology @Etale)
        (T'.smallGrothendieckTopology @Etale)) ∧
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
        (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale)) ∧
    PreservesFiniteColimits
      (Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
        (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale)) := by
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
    (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale)
  have := a.isLeftAdjoint
  refine ⟨inferInstance, ⟨a⟩, ?_, inferInstance⟩
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
  infer_instance

end AlgebraicGeometry
