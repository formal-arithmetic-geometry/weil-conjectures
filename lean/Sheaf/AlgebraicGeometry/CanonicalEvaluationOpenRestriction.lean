/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.KFlatResolution

/-! # Open restriction of canonical derived evaluation

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-pc-canonical-evaluation-open-restriction).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-canonical-evaluation-open-restriction). -/
local instance restrictionEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- Restriction preserves the canonical derived evaluation arrow, including its
source and target comparisons. This is independent of any ordinary complex model.

Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom),
Tag 08DL (lemma-restriction-RHom-to-U), and Tag 06YH (derived tensor construction).
(blueprint: lem-pc-canonical-evaluation-open-restriction).

Proof:
1. Pass from the over-site to the open scheme by Modules.overEquiv. Its derived
   functor is an equivalence, also between independently specified localization
   universes. Compose it with exact open restriction to form R.
2. Restrict K-flat tensor representatives. Restriction preserves K-flatness and
   commutes with sheaf tensor and its direct-sum totalization. This gives the
   natural strong tensor comparison and the comparison of the degree-zero units.
3. Restrict the fixed K-injective Hom representatives. Open restriction preserves
   K-injectivity and commutes with the product Hom complex. This gives the natural
   Hom comparison. Its representative formula is restriction of each local map.
4. On a total-tensor summand, the uncurrying formula for the canonical tensor-Hom
   family evaluates the same local map before or after restriction. Thus its
   evaluation counit commutes with the tensor and Hom comparisons. Naturality of
   associators and right unitors, and the unit comparison, carry the adjunct
   defining g to the corresponding adjunct on the open scheme. Composing the
   tensor comparison with the dual Hom comparison gives a, and the Hom comparison
   gives b. Faithfulness of the tensor-Hom equivalence gives the displayed square.
No ordinary evaluation inverse or exactness assumption on a complex is used.
The same constructions apply to the empty open and to zero objects. -/
theorem exists_canonicalEvaluation_open_restriction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
    let HU := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let KU := R.obj K
    let NU := R.obj N
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let DU := HU.obj (op KU, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    let gU := ((schemeDerivedTensorHomEquiv U.toScheme) (NU ⊗ DU) KU NU).symm
      ((α_ NU DU KU).hom ≫ NU ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) DU KU
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 DU)) ≫ (ρ_ NU).hom)
    ∃ a : R.obj (N ⊗ D) ≅ NU ⊗ DU,
      ∃ b : R.obj (H.obj (op K, N)) ≅ HU.obj (op KU, NU),
        R.map g ≫ b.hom = a.hom ≫ gU := by sorry

end AlgebraicGeometry
