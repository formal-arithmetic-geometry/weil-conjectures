module

public import Sheaf.Algebra.Homology.LocalizedStrictTensorData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Ordinary strict tensor-model and evaluation data

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03CY;
sites-cohomology.tex, Tags 06YM and 06YU.
(blueprint: def-sf-strict-tensor-ordinary-model-data).

These records retain the actual cochain tensor maps, their naturality and their
local pure-tensor normalization. They do not assert existence of comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.StrictTensorEvaluation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The actual constant strict module tower, before any localization.
Source: Stacks 015F, 06YU (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def diagonal :
  LocalizedStrictTensor.Modules.{c, v, r} R ⥤
    (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) := Functor.const ℕᵒᵖ

/-- Exact diagonal is additive, using its existing constant-functor instance.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance diagonalAdditive : (diagonal.{c, v, r} R).Additive :=
  inferInstanceAs (Functor.const ℕᵒᵖ : LocalizedStrictTensor.Modules.{c, v, r} R ⥤ _).Additive

/-- Exact diagonal preserves finite limits, computed pointwise.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance diagonalLimits : PreservesFiniteLimits (diagonal.{c, v, r} R) :=
  inferInstanceAs (PreservesFiniteLimits
    (Functor.const ℕᵒᵖ : LocalizedStrictTensor.Modules.{c, v, r} R ⥤ _))

/-- Exact diagonal preserves finite colimits, computed pointwise.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance diagonalColimits : PreservesFiniteColimits (diagonal.{c, v, r} R) :=
  inferInstanceAs (PreservesFiniteColimits
    (Functor.const ℕᵒᵖ : LocalizedStrictTensor.Modules.{c, v, r} R ⥤ _))

attribute [irreducible] diagonal

/-- Actual complexes of strict diagrams, not diagrams in a derived category.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
abbrev TowerComplex := CochainComplex (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) ℤ

/-- Cache the standard pointwise countable coproduct structure for strict towers.
Source: Stacks 02MZ (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance towerColimits :
    HasColimitsOfSize.{0, 0} (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) :=
  inferInstance

/-- The existing pointwise tensor of strict module diagrams.
Source: Stacks 03EK (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def towerTensor : (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) ⥤
    (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) ⥤
      (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) :=
  curriedTensor _

/-- Cache zero preservation of the pointwise tensor in the first variable.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance towerTensorZero : (towerTensor.{c, v, r} R).PreservesZeroMorphisms :=
  inferInstanceAs (curriedTensor
    (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R)).PreservesZeroMorphisms

/-- Cache zero preservation of the pointwise tensor in the second variable.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance towerTensorObjZero (M : ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) :
    ((towerTensor.{c, v, r} R).obj M).PreservesZeroMorphisms :=
  inferInstanceAs ((curriedTensor
    (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R)).obj M).PreservesZeroMorphisms

attribute [irreducible] towerTensor

/-- Total tensor exists for the existing strict diagram tensor.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
instance (priority := 2000) towerHasMapBifunctor (P Q : TowerComplex.{c, v, r} R) :
    CochainComplex.HasMapBifunctor P Q
      (towerTensor.{c, v, r} R) :=
  fun _ ↦ ((towerColimits.{c, v, r} R).has_colimits_of_shape _).has_colimit _

/-- The total tensor already used by the diagram-site derived tensor.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def towerTotal : TowerComplex.{c, v, r} R ⥤ TowerComplex.{c, v, r} R ⥤
    TowerComplex.{c, v, r} R :=
  (towerTensor.{c, v, r} R).map₂CochainComplex

/-- The existing base-site total tensor, named to share its dependent instances.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def baseTotal : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ ⥤
    CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ ⥤
      CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ :=
  (curriedTensor (LocalizedStrictTensor.Modules.{c, v, r} R)).map₂CochainComplex

attribute [irreducible] towerTotal baseTotal

/-- The coefficient tower as the actual degree-zero complex.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def coefficient (S : AlgebraTowers.{c, v, r} R) : TowerComplex.{c, v, r} R :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj
    (S ⋙ algebraModules.{c, v, r} R)

/-- The ordinary complex T_S(P), using the recorded strict tensor reduction.
Its differential and transitions are inherited from that additive functor.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
abbrev strictComplex (S : AlgebraTowers.{c, v, r} R)
    (P : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ) :=
  ((LocalizedStrictTensor.reduction.{c, v, r} R S).mapHomologicalComplex (.up ℤ)).obj P

attribute [local semireducible] towerTotal baseTotal towerTensor

/-- A local generator of the actual total tensor of strict diagrams.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def towerGenerator (A B : TowerComplex.{c, v, r} R) (i j k : ℤ) (h : i + j = k)
    (n : ℕᵒᵖ) (W : Cᵒᵖ) (x : ((A.X i).obj n).val.obj W)
    (y : ((B.X j).obj n).val.obj W) :
    (((((towerTotal.{c, v, r} R).obj A).obj B).X k).obj n).val.obj W :=
  ((CochainComplex.ιMapBifunctor A B (towerTensor.{c, v, r} R) i j k h).app n).val.app W
    (LocalizedStrictTensor.pure.{c, v, r} R ((A.X i).obj n) ((B.X j).obj n) W x y)

/-- A local generator of the actual total tensor on the base site.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def baseGenerator (A B : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ)
    (i j k : ℤ) (h : i + j = k) (W : Cᵒᵖ)
    (x : (A.X i).val.obj W) (y : (B.X j).val.obj W) :
    ((((baseTotal.{c, v, r} R).obj A).obj B).X k).val.obj W :=
  (CochainComplex.ιMapBifunctor A B
    (curriedTensor (LocalizedStrictTensor.Modules.{c, v, r} R)) i j k h).val.app W
    (LocalizedStrictTensor.pure.{c, v, r} R (A.X i) (B.X j) W x y)

/-- Insert a coefficient into the actual degree-zero complex.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def coefficientZero (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ) (W : Cᵒᵖ)
    (y : ((algebraModules.{c, v, r} R).obj (S.obj n)).val.obj W) :
    (((coefficient.{c, v, r} R S).X 0).obj n).val.obj W :=
  (((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (S ⋙ algebraModules.{c, v, r} R)).inv.app n).val.app W) y

attribute [local irreducible] towerTotal baseTotal towerTensor

/-- The actual exact evaluation on cochain complexes, with its categories shared.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-ordinary-model-data). -/
def evaluationComplex (n : ℕᵒᵖ) : TowerComplex.{c, v, r} R ⥤
    CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ :=
  (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapHomologicalComplex (.up ℤ)

/-- Ordinary evaluation of the total tensor, normalized on its direct-sum generators.
The field `pure` says the ordinary map is the identity on local pure tensors.
Source: Stacks 03EK, 07A4 and 06YU
(blueprint: def-sf-strict-tensor-ordinary-model-data). -/
structure OrdinaryEvaluation (n : ℕᵒᵖ) where
  chain : ∀ A B : TowerComplex.{c, v, r} R,
    ((evaluationComplex.{c, v, r} R n)).obj
        (((towerTotal.{c, v, r} R).obj A).obj B) ≅
      ((baseTotal.{c, v, r} R).obj
        (((evaluationComplex.{c, v, r} R n)).obj A)).obj
        (((evaluationComplex.{c, v, r} R n)).obj B)
  natural : ∀ (A A' B B' : TowerComplex.{c, v, r} R) (f : A ⟶ A') (g : B ⟶ B'),
    ((evaluationComplex.{c, v, r} R n)).map
        ((((towerTotal.{c, v, r} R).map f).app B) ≫
          (((towerTotal.{c, v, r} R).obj A').map g)) ≫ (chain A' B').hom =
      (chain A B).hom ≫
        (((baseTotal.{c, v, r} R).map
          (((evaluationComplex.{c, v, r} R n)).map f)).app
          (((evaluationComplex.{c, v, r} R n)).obj B)) ≫
        (((baseTotal.{c, v, r} R).obj
          (((evaluationComplex.{c, v, r} R n)).obj A')).map
          (((evaluationComplex.{c, v, r} R n)).map g))
  pure : ∀ (A B : TowerComplex.{c, v, r} R) (i j k : ℤ) (h : i + j = k)
    (W : Cᵒᵖ) (x : ((A.X i).obj n).val.obj W) (y : ((B.X j).obj n).val.obj W),
    (((chain A B).hom.f k).val.app W)
      (towerGenerator.{c, v, r} R A B i j k h n W x y) =
    baseGenerator.{c, v, r} R
      (((evaluationComplex.{c, v, r} R n)).obj A)
      (((evaluationComplex.{c, v, r} R n)).obj B) i j k h W x y

attribute [local semireducible] diagonal

/-- The ordinary total tensor of a constant complex with a degree-zero algebra tower.
The normalization singles out bidegree (i,0); it includes every strict transition.
Source: Stacks 06YU and 03EK
(blueprint: def-sf-strict-tensor-ordinary-model-data). -/
structure OrdinaryModel (S : AlgebraTowers.{c, v, r} R) where
  chain : ∀ P : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ,
    ((towerTotal.{c, v, r} R).obj
      (((diagonal.{c, v, r} R).mapHomologicalComplex (.up ℤ)).obj P)).obj
        (coefficient.{c, v, r} R S) ≅ strictComplex.{c, v, r} R S P
  natural : ∀ (P P' : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ)
    (f : P ⟶ P'),
    (((towerTotal.{c, v, r} R).map
      (((diagonal.{c, v, r} R).mapHomologicalComplex (.up ℤ)).map f)).app
        (coefficient.{c, v, r} R S)) ≫ (chain P').hom =
      (chain P).hom ≫
        ((LocalizedStrictTensor.reduction.{c, v, r} R S).mapHomologicalComplex
          (.up ℤ)).map f
  pure : ∀ (P : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ)
    (i : ℤ) (n : ℕᵒᵖ) (W : Cᵒᵖ) (x : (P.X i).val.obj W)
    (y : ((algebraModules.{c, v, r} R).obj (S.obj n)).val.obj W),
    ((((chain P).hom.f i).app n).val.app W)
      (towerGenerator.{c, v, r} R
        (((diagonal.{c, v, r} R).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficient.{c, v, r} R S) i 0 i (add_zero i) n W x
        (coefficientZero.{c, v, r} R S n W y)) =
      LocalizedStrictTensor.pure.{c, v, r} R (P.X i)
        ((algebraModules.{c, v, r} R).obj (S.obj n)) W x y


end SheafOfModules.StrictTensorEvaluation
