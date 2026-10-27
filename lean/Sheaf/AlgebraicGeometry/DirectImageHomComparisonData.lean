/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module
public import WeilConjectures.AlgebraicGeometry.MixedHomDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

/-! # Fixed data for the direct-image internal-Hom comparison

Source: Stacks Project, cohomology.tex, remark-projection-formula-for-internal-hom,
Tag 0B69; Tags 079W and 079U for the pullback adjunction and tensor comparison.
(blueprint: def-sfb-direct-image-hom-comparison-data).

These definitions expose the existing canonical constructions through the open-Ext
interface. The comparison is selected by the existing evaluation-mate existence theorem,
whose mate equation determines it; no global-Hom isomorphism is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The canonical derived pullback/direct-image adjunction, pinned by the simultaneous
left-derived counits, right-derived unit and ordinary tensor-pullback adjunction.
It is the existing `schemeHomPullbackAdjunction` choice.
Source: Stacks Project, cohomology.tex, Tag 079W.
(blueprint: def-sfb-direct-image-hom-comparison-data). -/
def sfbHomPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  schemeHomPullbackAdjunction f

/-- The existing natural pullback tensorator. Its components satisfy the shared-counit
K-flat normalization of `IsCanonicalPullbackTensorComparison`.
Source: Stacks Project, cohomology.tex, Tag 079U.
(blueprint: def-sfb-direct-image-hom-comparison-data). -/
def sfbHomTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X) :=
  mixedHomTensorPullbackIso f

/-- The evaluation-mate direct-image internal-Hom comparison. Its component is the
existing selected natural transformation whose all-test-map mate equation is stated by
`exists_mixedHomDirectImageComparison`.
Source: Stacks Project, cohomology.tex, Tag 0B69.
(blueprint: def-sfb-direct-image-hom-comparison-data). -/
def sfbDirectImageHomComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E N : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).obj
        ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op E, N)) ⟶
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op ((schemeDerivedDirectImage f).obj E), (schemeDerivedDirectImage f).obj N) :=
  (Classical.choose (exists_mixedHomDirectImageComparison f)).app (op E, N)

end AlgebraicGeometry
