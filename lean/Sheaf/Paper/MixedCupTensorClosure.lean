module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupTensorElementary
public import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-tensor-closure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

attribute [local irreducible] commonStageTensorComparison rationalDerivedTensor

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- The prescribed identity-stage scalar unitor, including the transition identification.
Source: proof step 4 (blueprint: def-sf-mixed-cup-tensor-closure). -/
def stageUnit (W : Scheme.{u}) (F : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  operationStageTransitionIso C.l C.Qbar W F F le_rfl ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor C.l C.Qbar W F

universe i v w

/-- Represent the inverse tensor comparison at a common stage using inclusion and
its fixed stage isomorphism. Source: proof step 4
(blueprint: def-sf-mixed-cup-tensor-closure). -/
def representedTensorMap {I : Type i} [Preorder I] [IsDirectedOrder I]
    {B : I → Type v} [∀ j, Category.{w} (B j)] (U : StageSystem B)
    (j : I) (R : B j × B j ⥤ B j) (e : U.T (le_refl j) ≅ 𝟭 (B j))
    (K L : B j) (V : U.PairCategory) (h : V.stage ≤ j)
    (c : V.toStage h ≅ R.obj ((U.T (le_refl j)).obj K, (U.T (le_refl j)).obj L)) :
    (U.ι j).obj (R.obj (K, L)) ⟶ V :=
  (U.ι j).map
    (R.map (Prod.mkHom (e.inv.app K) (e.inv.app L)) ≫ c.inv) ≫
      (U.isoToStage V h).inv

/-- The canonical closure tensor representative before recorded object equalities.
Source: proof step 4 (blueprint: def-sf-mixed-cup-tensor-closure). -/
def closureTensorRepresentative (W : Scheme.{u})
    [∀ x : W, Invertible (C.l : W.residueField x)]
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K L : sfRationalConstructibleCategory C.l (FieldAt C F) W)
    (h : (commonStageTensorObject C.l C.Qbar W
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := W) F).obj K)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := W) F).obj L)).stage ≤ F) :=
  let A := (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := C.l) (Ω := C.Qbar) (Y := W) F).obj K
  let B := (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := C.l) (Ω := C.Qbar) (Y := W) F).obj L
  representedTensorMap (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar W)
    F (rationalDerivedTensor C.l (FieldAt C F) W) (stageUnit C W F)
    K L (commonStageTensorObject C.l C.Qbar W A B) h
    (commonStageTensorComparison C.l C.Qbar W A B F h)

/-- The closure tensor map is the representative of the canonical inverse common-stage
comparison. All object-coordinate equalities are fixed by the recorded normalizations.
Source: proof step 4 (blueprint: def-sf-mixed-cup-tensor-closure). -/
def ClosureTensorNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (t : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    (K L : (domain C X.obj.left (.rational F)).FullSubcategory),
    let A := ((change C X (.closure F)).obj K).obj
    let B := ((change C X (.closure F)).obj L).obj
    ∀ h : (commonStageTensorObject C.l C.Qbar X.obj.left A B).stage ≤ F,
    HEq ((t (.closure F) K L).hom).hom
      (closureTensorRepresentative C X.obj.left F K.obj L.obj h)

end WeilConjectures.MixedCupCoefficientChange
