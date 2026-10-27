module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Invertible sheaves on finite pinching squares

Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU, restricted to
rank-one finite projectives and glued on an affine open cover
(blueprint: def-sfb-pinching-line-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The affine fibre-product hypothesis, using the actual rings of sections.
`IsPullback` says that the canonical map to the matching-pairs ring is an
isomorphism. The fourth ring is evaluated on the inverse image of the same open.
Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU
(blueprint: def-sfb-pinching-line-data). -/
def HasAffinePinchingCover {X A B : Scheme.{u}} (v : A ⟶ X) (j : B ⟶ X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
    IsAffineOpen (v ⁻¹ᵁ U) ∧ IsAffineOpen (j ⁻¹ᵁ U) ∧
    IsAffineOpen ((pullback.fst v j ≫ v) ⁻¹ᵁ U) ∧
    Function.Surjective ((pullback.fst v j).app (v ⁻¹ᵁ U)).hom ∧
    IsPullback (v.app U) (j.app U)
      ((pullback.fst v j).app (v ⁻¹ᵁ U))
      ((pullback.snd v j).appLE (j ⁻¹ᵁ U) ((pullback.fst v j ≫ v) ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, pullback.condition]))

/-- The overlap identification of the two actual pullbacks of a module.
Source: Stacks Project, Sheaves, Tag 0097; More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingOverlap {X A B : Scheme.{u}} (v : A ⟶ X) (j : B ⟶ X)
    (L : X.Modules) :
    (tensorPullback (pullback.fst v j)).obj ((tensorPullback v).obj L) ≅
      (tensorPullback (pullback.snd v j)).obj ((tensorPullback j).obj L) :=
  ((tensorPullbackCompositionIso (pullback.fst v j) v
    (pullback.fst v j ≫ v) rfl).app L).symm ≪≫
    (tensorPullbackCompositionIso (pullback.snd v j) j
      (pullback.fst v j ≫ v) pullback.condition.symm).app L

/-- A line-bundle triple, including the specified overlap isomorphism.
Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU
(blueprint: def-sfb-pinching-line-data). -/
structure PinchingLineTriple {X A B : Scheme.{u}} (v : A ⟶ X) (j : B ⟶ X) where
  left : A.Modules
  right : B.Modules
  left_invertible : left.IsInvertible
  right_invertible : right.IsInvertible
  overlap : (tensorPullback (pullback.fst v j)).obj left ≅
    (tensorPullback (pullback.snd v j)).obj right

/-- Compatibility for all module maps, without requiring maps to be isomorphisms.
Source: Stacks Project, More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
def PinchingLineTriple.Compatible {X A B : Scheme.{u}} {v : A ⟶ X} {j : B ⟶ X}
    (D E : PinchingLineTriple v j) (a : D.left ⟶ E.left) (b : D.right ⟶ E.right) : Prop :=
  (tensorPullback (pullback.fst v j)).map a ≫ E.overlap.hom =
    D.overlap.hom ≫ (tensorPullback (pullback.snd v j)).map b

/-- A lift of the prescribed triple, with its specified projection identifications.
Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU
(blueprint: def-sfb-pinching-line-data). -/
structure PinchingLineLift {X A B : Scheme.{u}} {v : A ⟶ X} {j : B ⟶ X}
    (D : PinchingLineTriple v j) where
  line : X.Modules
  invertible : line.IsInvertible
  left : (tensorPullback v).obj line ≅ D.left
  right : (tensorPullback j).obj line ≅ D.right
  commutes : (tensorPullback (pullback.fst v j)).map left.hom ≫ D.overlap.hom =
    (pinchingOverlap v j line).hom ≫ (tensorPullback (pullback.snd v j)).map right.hom

/-- The equivalence expressed by essential surjectivity and unique lifting of every
compatible pair of module maps. This retains all Hom sets, hence automorphisms too.
Source: Stacks Project, More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
def PinchingLineEquivalence {X A B : Scheme.{u}} (v : A ⟶ X) (j : B ⟶ X) : Prop :=
  (∀ D : PinchingLineTriple v j, Nonempty (PinchingLineLift D)) ∧
  ∀ (L K : X.Modules) (_hL : L.IsInvertible) (_hK : K.IsInvertible)
    (a : (tensorPullback v).obj L ⟶ (tensorPullback v).obj K)
    (b : (tensorPullback j).obj L ⟶ (tensorPullback j).obj K),
    (tensorPullback (pullback.fst v j)).map a ≫ (pinchingOverlap v j K).hom =
      (pinchingOverlap v j L).hom ≫ (tensorPullback (pullback.snd v j)).map b →
    ∃! f : L ⟶ K, (tensorPullback v).map f = a ∧ (tensorPullback j).map f = b

/-- The base-changed finite map; the pullbacks are over the named base scheme.
Source: Stacks Project, Schemes, fibre products; More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingBaseMap {S X A : Scheme.{u}} (p : X ⟶ S) (v : A ⟶ X)
    {T : Scheme.{u}} (t : T ⟶ S) : Limits.pullback (v ≫ p) t ⟶ Limits.pullback p t :=
  pullback.map (v ≫ p) t p t v (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- Componentwise tensor of line triples, using the section-normalized tensor comparison.
Source: Stacks Project, More on Algebra, Tag 0D2J; Modules, Tag 01CD
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def PinchingLineTriple.tensor {X A B : Scheme.{u}}
    {v : A ⟶ X} {j : B ⟶ X} (D E : PinchingLineTriple v j) : PinchingLineTriple v j where
  left := D.left ⊗ E.left
  right := D.right ⊗ E.right
  left_invertible := @IsInvertible.tensorObj _ _ _ D.left_invertible E.left_invertible
  right_invertible := @IsInvertible.tensorObj _ _ _ D.right_invertible E.right_invertible
  overlap := (Classical.choose (module_pullback_tensor (pullback.fst v j))) D.left E.left ≪≫
    (D.overlap ⊗ᵢ E.overlap) ≪≫
      ((Classical.choose (module_pullback_tensor (pullback.snd v j))) D.right E.right).symm

/-- Map on the overlap schemes under base change.
Source: Stacks Project, Schemes, fibre products; More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingBaseOverlap {S X A B : Scheme.{u}}
    (p : X ⟶ S) (v : A ⟶ X) (j : B ⟶ X) {T : Scheme.{u}} (t : T ⟶ S) :
    Limits.pullback (pinchingBaseMap p v t) (pinchingBaseMap p j t) ⟶
      Limits.pullback v j :=
  pullback.map (pinchingBaseMap p v t) (pinchingBaseMap p j t) v j
    (pullback.fst (v ≫ p) t) (pullback.fst (j ≫ p) t) (pullback.fst p t)
    (by simp [pinchingBaseMap]) (by simp [pinchingBaseMap])

/-- The overlap comparison between pulling to a base-changed branch and to the old
intersection. It is defined by adjunction-normalized composition, not an arbitrary map.
Source: Stacks Project, Sheaves, Tag 0097; More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingBaseLeft {S X A B : Scheme.{u}}
    (p : X ⟶ S) (v : A ⟶ X) (j : B ⟶ X) {T : Scheme.{u}} (t : T ⟶ S)
    (M : A.Modules) :
    (tensorPullback (pullback.fst (pinchingBaseMap p v t) (pinchingBaseMap p j t))).obj
        ((tensorPullback (pullback.fst (v ≫ p) t)).obj M) ≅
      (tensorPullback (pinchingBaseOverlap p v j t)).obj
        ((tensorPullback (pullback.fst v j)).obj M) :=
  ((tensorPullbackCompositionIso _ _ _ rfl).app M).symm ≪≫
    (tensorPullbackCompositionIso _ _ _ (by simp [pinchingBaseOverlap])).app M

/-- The corresponding comparison on the closed branch.
Source: Stacks Project, Sheaves, Tag 0097; More on Algebra, Tag 0D2J
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingBaseRight {S X A B : Scheme.{u}}
    (p : X ⟶ S) (v : A ⟶ X) (j : B ⟶ X) {T : Scheme.{u}} (t : T ⟶ S)
    (N : B.Modules) :
    (tensorPullback (pullback.snd (pinchingBaseMap p v t) (pinchingBaseMap p j t))).obj
        ((tensorPullback (pullback.fst (j ≫ p) t)).obj N) ≅
      (tensorPullback (pinchingBaseOverlap p v j t)).obj
        ((tensorPullback (pullback.snd v j)).obj N) :=
  ((tensorPullbackCompositionIso _ _ _ rfl).app N).symm ≪≫
    (tensorPullbackCompositionIso _ _ _ (by simp [pinchingBaseOverlap])).app N

/-- Base change of a triple: the two coefficient lines are the actual tensor pullbacks,
and the overlap is the pullback of the prescribed overlap with composition comparisons.
Source: Stacks Project, More on Algebra, Tag 0D2J; Sheaves, Tag 0097
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def PinchingLineTriple.baseChange {S X A B : Scheme.{u}}
    (p : X ⟶ S) {v : A ⟶ X} {j : B ⟶ X} {T : Scheme.{u}} (t : T ⟶ S)
    (D : PinchingLineTriple v j) :
    PinchingLineTriple (pinchingBaseMap p v t) (pinchingBaseMap p j t) where
  left := (tensorPullback (pullback.fst (v ≫ p) t)).obj D.left
  right := (tensorPullback (pullback.fst (j ≫ p) t)).obj D.right
  left_invertible := by
    let := D.left_invertible
    exact ((invertible_pullback_tensor (pullback.fst (v ≫ p) t)).1 D.left).2
  right_invertible := by
    let := D.right_invertible
    exact ((invertible_pullback_tensor (pullback.fst (j ≫ p) t)).1 D.right).2
  overlap := pinchingBaseLeft p v j t D.left ≪≫
    (tensorPullback (pinchingBaseOverlap p v j t)).mapIso D.overlap ≪≫
      (pinchingBaseRight p v j t D.right).symm

/-- A specified pair of projection isomorphisms realizes a triple on a given line.
Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU
(blueprint: def-sfb-pinching-line-data). -/
def PinchingLineTriple.IsLift {X A B : Scheme.{u}} {v : A ⟶ X} {j : B ⟶ X}
    (D : PinchingLineTriple v j) (L : X.Modules)
    (a : (tensorPullback v).obj L ≅ D.left)
    (b : (tensorPullback j).obj L ≅ D.right) : Prop :=
  (tensorPullback (pullback.fst v j)).map a.hom ≫ D.overlap.hom =
    (pinchingOverlap v j L).hom ≫ (tensorPullback (pullback.snd v j)).map b.hom

/-- The composition comparison for pulling a reconstructed line to a branch after
base change. Source: Stacks Project, Sheaves, Tag 0097
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingBaseProjection {S X A : Scheme.{u}}
    (p : X ⟶ S) (v : A ⟶ X) {T : Scheme.{u}} (t : T ⟶ S) (L : X.Modules) :
    (tensorPullback (pinchingBaseMap p v t)).obj
        ((tensorPullback (pullback.fst p t)).obj L) ≅
      (tensorPullback (pullback.fst (v ≫ p) t)).obj ((tensorPullback v).obj L) :=
  ((tensorPullbackCompositionIso _ _ _ rfl).app L).symm ≪≫
    (tensorPullbackCompositionIso _ _ _ (by simp [pinchingBaseMap])).app L

/-- The canonical structure-sheaf pullback isomorphism, fixed by the adjunction unit.
Source: Stacks Project, Modules, Tags 0096 and 01CA
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorPullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules := by
  letI := (tensorPullbackObjUnitToUnit_isIso f).1
  exact asIso (tensorPullbackObjUnitToUnit f)

/-- The tensor unit triple, with the canonical identification of its two structure lines.
Source: Stacks Project, More on Algebra, Tag 0D2J; Modules, Tag 01CA
(blueprint: def-sfb-pinching-line-data). -/
noncomputable def pinchingUnitTriple {X A B : Scheme.{u}} (v : A ⟶ X) (j : B ⟶ X) :
    PinchingLineTriple v j where
  left := 𝟙_ A.Modules
  right := 𝟙_ B.Modules
  left_invertible := inferInstance
  right_invertible := inferInstance
  overlap := pinchingUnitIso (pullback.fst v j) ≪≫ (pinchingUnitIso (pullback.snd v j)).symm

end AlgebraicGeometry.Scheme.Modules
