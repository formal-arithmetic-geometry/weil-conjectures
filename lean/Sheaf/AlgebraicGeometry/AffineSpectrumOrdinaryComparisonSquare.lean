/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The ordinary affine spectrum stalk comparison square

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The comparison before applying the inverse derived pullback counit.
Source: Stacks Project, Tag 0DJ8, equation-bc; Tag 0098, stalk pullback formula.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square). -/
def comparisonIntoTensorPullback {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv

/-- The actual chain isomorphism between the two successive ordinary pullbacks.
It is the adjunction mate of pushforward composition, with isoSpec naturality.
Source: Stacks Project, Tags 0096 and 0D5S, pullback composition.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square). -/
def affineSpectrumTensorComplexIso {X X' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
      (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P) ≅
    ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatIso.mapHomologicalComplex
    ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
    (.up ℤ)).app P

/-- The base-derived tensor comparison is invariant under affine spectrum coordinates
before introducing either inverse counit for g'. No K-flatness is needed here.

Proof: isoSpec naturality and stalkMap_comp identify R, A, B and C and their
structural maps in the original and spectrum squares. The map on A tensor_R B
is the tensor of the stalk ring isomorphisms; its inverse is the tensor of their
inverses. On the two tensor inclusions these maps intertwine tensorMap, including
its stalkCongr factor. The germ formula of Tag 0098 identifies the stalk complex
of the termwise pullback P0 with extension of the stalk complex of P along the
A-isomorphism. Restriction along its inverse is exact and inverse to this extension.
Transport the left-derived R-to-B extension through these exact equivalences.
Uniqueness of a left-derived lift identifies the transported functor and its
counit with the spectrum model. Apply homology, use cohomologyIso_smul for each
A-element, and tensor induction to lift the B-linear cohomology isomorphism to
an isomorphism over A tensor_R B. Extend scalars to C and forget scalars to get l.
The equations comparison_eq and localized_eq identify the model comparisons with
the transported counits. The tensorStalkIso germ formulas identify the ordinary
pullback factors with affineSpectrumTensorComplexIso. Restriction-stalk naturality
identifies the remaining stalk change with isoPullbackStalkCohomologyIso followed
by the exact iso-pullback complex counit. These equalities give the displayed
square. This uses only exact coordinate equivalences, with no flatness over R,
no invertibility of the comparisons, and no derived pullback composition along g'.
Zero complexes and empty schemes satisfy the same tensor and counit equations.
Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098,
lemma-stalk-pullback-modules; Tag 0096, pullback adjunction.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square). -/
theorem exists_affineSpectrum_ordinaryComparison_square
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    ∃ l : F.obj (Arrow.mk (comparisonIntoTensorPullback f f' g g' sq z P i)).left ≅
        F0.obj (Arrow.mk
          (comparisonIntoTensorPullback (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0 i)).left,
      l.hom ≫ F0.map
        (comparisonIntoTensorPullback (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0 i) =
      F.map (comparisonIntoTensorPullback f f' g g' sq z P i) ≫
        (isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i).hom.app
          (DerivedCategory.Q.obj Pg) ≫
        F0.map (H0.map ((isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app Pg ≫
          DerivedCategory.Q.map (affineSpectrumTensorComplexIso g' P).inv)) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
