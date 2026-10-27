/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Canonical comparisons for derived tensor pullback of algebraic spaces

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 0D6D; Cohomology of Spaces,
section Derived Categories (blueprint: def-sfb-space-derived-pullback).

The pullback is the existing derivedTensorPullback. This module supplies its identity
and composition comparisons, normalized on local tensors before deriving them.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

variable {X Y Z : AlgebraicSpace S}

/-- A chart for the identity map is a morphism of the same small étale site.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-space-derived-pullback). -/
def moduleChartIdentityHom (X : AlgebraicSpace S) (V : X.EtaleSite)
    (q : ModuleChart (𝟙 X) V) : q.left ⟶ V :=
  ⟨q.hom⟩

/-- The unit tensor comparison is uniquely multiplication on every chart.
Source: Stacks, Modules on Sites, Tag 03D7 (blueprint: def-sfb-space-derived-pullback).
Proof: send b tensor m to b times the restriction of m. The inverse sends a section
to 1 tensor that section. Tensor balancing makes the two composites identities. These
local descriptions agree on chart overlaps and generate after sheafification, proving
existence, naturality and uniqueness. -/
theorem moduleTensorPullbackId_existsUnique (X : AlgebraicSpace S) :
    ∃! e : moduleTensorPullback (𝟙 X) ≅ 𝟭 X.Modules,
      ∀ (M : X.Modules) (V : X.EtaleSite) (q : ModuleChart (𝟙 X) V)
        (b : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
        (e.hom.app M).val.app (op q.left) (moduleTensorSection (𝟙 X) M V q b m) =
          b • M.val.map (moduleChartIdentityHom X V q).op m := by
  sorry

/-- Canonical ordinary tensor identity, with the multiplication normalization.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-space-derived-pullback). -/
def moduleTensorPullbackId (X : AlgebraicSpace S) :
    moduleTensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  Classical.choose (moduleTensorPullbackId_existsUnique X)

/-- Transport of the normalized ordinary tensor composition comparison.
Source: Stacks, Tags 0D6D and 039Z (blueprint: def-sfb-space-derived-pullback). -/
def smallModuleTensorPullbackComp (f : X ⟶ Y) (g : Z ⟶ X) :
    smallModuleTensorPullback f ⋙ smallModuleTensorPullback g ≅
      smallModuleTensorPullback (g ≫ f) :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.associator _ _ _).symm) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (isoWhiskerRight X.smallModuleEquivalence.unitIso.symm _)) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.leftUnitor _)) ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (isoWhiskerRight (moduleTensorComposition g f) _)

/-- Transport of the ordinary multiplication comparison for the identity.
Source: Stacks, Tags 03D7 and 039Z (blueprint: def-sfb-space-derived-pullback). -/
def smallModuleTensorPullbackId (X : AlgebraicSpace S) :
    smallModuleTensorPullback (𝟙 X) ≅ 𝟭 X.SmallModules :=
  isoWhiskerLeft _ (isoWhiskerRight (moduleTensorPullbackId X) _) ≪≫
    isoWhiskerLeft _ (Functor.leftUnitor _) ≪≫ X.smallModuleEquivalence.counitIso

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
  [HasDerivedCategory.{w} Z.SmallModules]

/-- The existing canonical total left derived tensor pullback, with a common localization size.
Source: Stacks, Tag 06YY (blueprint: def-sfb-space-derived-pullback). -/
abbrev spaceDerivedPullback (f : X ⟶ Y) : Y.DerivedModules ⥤ X.DerivedModules :=
  derivedTensorPullback.{u, w, w} f

/-- Its canonical comparison to termwise tensor pullback.
Source: Stacks, Tag 06YY (blueprint: def-sfb-space-derived-pullback). -/
abbrev spaceDerivedPullbackCounit (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ spaceDerivedPullback f ⟶ smallTensorPullbackComplex f :=
  (smallTensorPullbackComplex f).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.SmallModules (ComplexShape.up ℤ))

/-- The composite comparison: first derive f, then g, then ordinary tensor associativity.
Source: Stacks, Tag 0D6D (blueprint: def-sfb-space-derived-pullback). -/
def spaceDerivedPullbackCompCounit (f : X ⟶ Y) (g : Z ⟶ X) :
    DerivedCategory.Q ⋙ (spaceDerivedPullback f ⋙ spaceDerivedPullback g) ⟶
      smallTensorPullbackComplex (g ≫ f) :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (spaceDerivedPullbackCounit f) (spaceDerivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft ((smallModuleTensorPullback f).mapHomologicalComplex (ComplexShape.up ℤ))
      (spaceDerivedPullbackCounit g) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight
      (Functor.mapHomologicalComplexCompIso (smallModuleTensorPullbackComp f g)
        (ComplexShape.up ℤ)).hom
      DerivedCategory.Q

/-- Composition is again the universal derived functor with that exact comparison.
Source: Stacks, Tag 0D6D (blueprint: def-sfb-space-derived-pullback).
Proof: a K-flat complex with flat terms remains so after tensor pullback: locally this
is the usual flat-base tensor calculation against acyclic complexes. Hence both stages
are computed by the same termwise composite on those resolutions. The ordinary
comparison is normalized by tensor associativity. The resolving-class universal
property proves the asserted derived universal property with the displayed counit. -/
@[instance] theorem spaceDerivedPullbackComp_isLeftDerived (f : X ⟶ Y) (g : Z ⟶ X) :
    (spaceDerivedPullback f ⋙ spaceDerivedPullback g).IsLeftDerivedFunctor
      (spaceDerivedPullbackCompCounit f g)
      (HomologicalComplex.quasiIso Y.SmallModules (ComplexShape.up ℤ)) := by
  sorry

/-- Canonical composition, fixed by the two universal derived counits.
Source: Stacks, Tag 0D6D (blueprint: def-sfb-space-derived-pullback). -/
def spaceDerivedPullbackComp (f : X ⟶ Y) (g : Z ⟶ X) :
    spaceDerivedPullback (g ≫ f) ≅ spaceDerivedPullback f ⋙ spaceDerivedPullback g :=
  Functor.leftDerivedUnique _
    ((smallTensorPullbackComplex (g ≫ f)).totalLeftDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso Y.SmallModules (ComplexShape.up ℤ)))
    ((smallTensorPullbackComplex (g ≫ f)).totalLeftDerivedCounit DerivedCategory.Q
      (HomologicalComplex.quasiIso Y.SmallModules (ComplexShape.up ℤ)))
    (spaceDerivedPullbackCompCounit f g)
    (HomologicalComplex.quasiIso Y.SmallModules (ComplexShape.up ℤ))

/-- Identity comparison before invoking uniqueness of the derived functor.
Source: Stacks, Tag 06YY (blueprint: def-sfb-space-derived-pullback). -/
def spaceDerivedPullbackIdCounit (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    DerivedCategory.Q ⋙ 𝟭 (X.DerivedModules) ⟶ smallTensorPullbackComplex (𝟙 X) :=
  (DerivedCategory.Q.rightUnitor).hom ≫
    whiskerRight
      (NatIso.mapHomologicalComplex (smallModuleTensorPullbackId X)
        (ComplexShape.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso X.SmallModules (ComplexShape.up ℤ)).inv
      DerivedCategory.Q

/-- The identity derived functor has the indicated universal comparison.
Source: Stacks, Tag 06YY (blueprint: def-sfb-space-derived-pullback).
Proof: ordinary identity tensor pullback is the identity by multiplication. Its complex
comparison is an isomorphism, so localization already gives its universal derived
functor; the specified comparison is exactly that multiplication comparison. -/
@[instance] theorem spaceDerivedPullbackId_isLeftDerived (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    (𝟭 (X.DerivedModules)).IsLeftDerivedFunctor (spaceDerivedPullbackIdCounit X)
      (HomologicalComplex.quasiIso X.SmallModules (ComplexShape.up ℤ)) := by
  sorry

/-- Canonical identity pullback, normalized by multiplication on ordinary modules.
Source: Stacks, Tag 06YY (blueprint: def-sfb-space-derived-pullback). -/
def spaceDerivedPullbackId (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    spaceDerivedPullback (𝟙 X) ≅ 𝟭 (X.DerivedModules) :=
  Functor.leftDerivedUnique _
    ((smallTensorPullbackComplex (𝟙 X)).totalLeftDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso X.SmallModules (ComplexShape.up ℤ)))
    ((smallTensorPullbackComplex (𝟙 X)).totalLeftDerivedCounit DerivedCategory.Q
      (HomologicalComplex.quasiIso X.SmallModules (ComplexShape.up ℤ)))
    (spaceDerivedPullbackIdCounit X)
    (HomologicalComplex.quasiIso X.SmallModules (ComplexShape.up ℤ))

end AlgebraicGeometry.AlgebraicSpace
