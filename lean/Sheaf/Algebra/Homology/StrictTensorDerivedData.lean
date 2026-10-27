module

public import Sheaf.Algebra.Homology.StrictTensorOrdinaryData
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized strict tensor computation and derived evaluation data

Source: Stacks Project, sites-cohomology.tex, Tags 06YN, 06YS, 06YU and 07A4;
derived.tex, Tag 015F.
(blueprint: def-sf-strict-tensor-derived-evaluation-data).

These records specify the one-sided and evaluation normalization equations for a
fixed two-sided tensor presentation. The comparison is an explicit composite;
existence of the records is asserted by the consuming statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r x₂ x₃ y₂ y₃ a₁ a₂ h₁ h₂ u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
open SheafOfModules.KFlatFixedTensor
namespace SheafOfModules.StrictTensorEvaluation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- K-flatness on strict diagrams, with flat terms tested by exact evaluation.
This is the acyclic-tensor definition on the diagram site, transported along its
normalized module equivalence; flatness of a diagram is levelwise flatness.
Source: Stacks 06YN, 03ER and the diagram-site realization
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def ResolvingTower (P : TowerComplex.{c, v, r} R) : Prop :=
  (∀ F : TowerComplex.{c, v, r} R, F.Acyclic →
    (((towerTotal.{c, v, r} R).obj F).obj P).Acyclic) ∧
  ∀ (i : ℤ) (n : ℕᵒᵖ), IsFlatOnSite (J := J) (R := R) ((P.X i).obj n)

/-- The full resolving homotopy subcategory on strict diagrams.
Source: Stacks 06YS (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def towerProperty : ObjectProperty
    (HomotopyCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ)) :=
  fun X ↦ ResolvingTower.{c, v, r} R X.as

/-- The existing homotopy localization, with its source category fixed explicitly.
Source: Stacks 05RU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def towerQ :
    HomotopyCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) :=
  DerivedCategory.Qh

/-- The ordinary tower tensor in uncurried form, with its categories fixed.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def towerF : TowerComplex.{c, v, r} R × TowerComplex.{c, v, r} R ⥤
    TowerComplex.{c, v, r} R := Functor.uncurry.obj (towerTotal.{c, v, r} R)

/-- The ordinary base tensor in uncurried form, with its categories fixed.
Source: Stacks 06YM (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def baseF : (CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ ×
    CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ) ⥤
      CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ :=
  Functor.uncurry.obj (baseTotal.{c, v, r} R)

/-- The specified two-sided tensor descent data on the diagram site, transported
through its normalized module equivalence. This is the existing tensor-presentation
record, so both the homotopy and the two-sided derived comparison are retained.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
abbrev TowerTensor := TensorPresentation
  (HomotopyCategory.quotient (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
  (towerQ.{c, v, r} R) (towerF.{c, v, r} R)
  (towerProperty.{c, v, r} R)

/-- The resolving property on the base site is the recorded flat-term K-flat property.
Source: Stacks 06YS (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def baseProperty : ObjectProperty
    (HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ)) :=
  fun X ↦ Resolving.{c, v, r} R X.as

/-- The existing base homotopy localization, sharing its declared source category.
Source: Stacks 05RU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def baseQ : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) ⥤
    DerivedCategory (LocalizedStrictTensor.Modules.{c, v, r} R) := DerivedCategory.Qh

/-- The actual exact diagonal on homotopy categories, with its target fixed.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def diagonalH : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) ⥤
    HomotopyCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) :=
  (diagonal.{c, v, r} R).mapHomotopyCategory (.up ℤ)

/-- The actual exact diagonal on derived categories.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def diagonalD : DerivedCategory (LocalizedStrictTensor.Modules.{c, v, r} R) ⥤
    DerivedCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) :=
  (diagonal.{c, v, r} R).mapDerivedCategory

/-- The specified exact-diagonal localization comparison.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def diagonalFactors : baseQ.{c, v, r} R ⋙ diagonalD.{c, v, r} R ≅
    diagonalH.{c, v, r} R ⋙ towerQ.{c, v, r} R :=
  (diagonal.{c, v, r} R).mapDerivedCategoryFactorsh

/-- The same specified tensor-presentation record on the base ringed site.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
abbrev BaseTensor := TensorPresentation
  (HomotopyCategory.quotient (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
  (baseQ.{c, v, r} R) (baseF.{c, v, r} R) (baseProperty.{c, v, r} R)

section Generic
variable {H : Type x₂} [Category.{y₂} H] {D : Type x₃} [Category.{y₃} D]
  {Q : H ⥤ D} (P : ObjectProperty H)

/-- The one-sided comparison with its specified two-sided normalization and naturality
in every homotopy map of the resolving factor. The NatIso supplies naturality in
all maps of the unrestricted second factor.
Source: Stacks 06YU and lem-trf-site-one-sided-tensor-normalization
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def OneSidedFamily (B : H × H ⥤ H) (T : D × D ⥤ D) :=
  ∀ (K : H) (_hK : P K), Q ⋙ (Functor.curry.obj T).obj (Q.obj K) ≅
    (Functor.curry.obj B).obj K ⋙ Q

/-- The conditions identifying a one-sided family with the fixed two-sided descent.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
structure OneSidedConditions (B : H × H ⥤ H) (T : D × D ⥤ D)
    (δ : (P.ι.prod P.ι) ⋙ B ⋙ Q ≅ ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ T)
    (family : OneSidedFamily P B T) : Prop where
  normalized : ∀ (K V : H) (hK : P K) (hV : P V),
    (family K hK).app V = (δ.app (⟨K, hK⟩, ⟨V, hV⟩)).symm
  natural_first : ∀ (K K' : H) (hK : P K) (hK' : P K')
    (g : K ⟶ K') (M : H),
    (family K hK).hom.app M ≫
        Q.map (((Functor.curry.obj B).map g).app M) =
      ((Functor.curry.obj T).map (Q.map g)).app (Q.obj M) ≫
        (family K' hK').hom.app M

end Generic

/-- The degree-zero coefficient in the strict homotopy category.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def coefficientH (S : AlgebraTowers.{c, v, r} R) :
    HomotopyCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) :=
  (HomotopyCategory.quotient _ (.up ℤ)).obj (coefficient.{c, v, r} R S)

/-- The ordinary strict tensor model on homotopy categories.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def strictHomotopy (S : AlgebraTowers.{c, v, r} R) :
    HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) ⥤
      HomotopyCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) :=
  (LocalizedStrictTensor.reduction.{c, v, r} R S).mapHomotopyCategory (.up ℤ)



/-- The derived diagram tensor with the actual coefficient tower, using exact diagonal.
Source: Stacks 06YU and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def derivedReduction (t : TowerTensor.{c, v, r} R) (S : AlgebraTowers.{c, v, r} R) :=
  (diagonalD.{c, v, r} R) ⋙
    (Functor.curry.obj t.derivedTensor).flip.obj
      (DerivedCategory.Qh.obj (coefficientH.{c, v, r} R S))


/-- The normalized comparison is the composite of exact-diagonal localization,
one-sided tensor computation, and the ordinary strict tensor identification.
Source: Stacks 06YU and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def comparison (t : TowerTensor.{c, v, r} R)
    (one : OneSidedFamily (Q := towerQ.{c, v, r} R) (towerProperty.{c, v, r} R)
      t.homotopyTensor t.derivedTensor)
    (S : AlgebraTowers.{c, v, r} R)
    (θ : diagonalH.{c, v, r} R ⋙
      (Functor.curry.obj t.homotopyTensor).flip.obj (coefficientH.{c, v, r} R S) ≅
      strictHomotopy.{c, v, r} R S)
    (P : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
    (hP : towerProperty.{c, v, r} R
      ((diagonalH.{c, v, r} R).obj P)) :=
  t.derivedTensor.mapIso
    (Iso.prod ((diagonalFactors.{c, v, r} R).app P)
      (Iso.refl (DerivedCategory.Qh.obj (coefficientH.{c, v, r} R S)))) ≪≫
    (one ((diagonalH.{c, v, r} R).obj P) hP).app
      (coefficientH.{c, v, r} R S) ≪≫ DerivedCategory.Qh.mapIso (θ.app P)

/-- The given resolving base homotopy complex remains resolving after exact diagonal.
Source: Stacks 06YN, 03ER (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def Good (P : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ)) : Prop :=
  baseProperty.{c, v, r} R P ∧ towerProperty.{c, v, r} R
    ((diagonalH.{c, v, r} R).obj P)

/-- Localization of exact evaluation, using its recorded canonical comparison.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def evalLocalization (n : ℕᵒᵖ) (P : TowerComplex.{c, v, r} R) :
    (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≅
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((evaluationComplex.{c, v, r} R n)).obj P)) :=
  (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.app _ ≪≫
    DerivedCategory.Qh.mapIso
      (((LocalizedStrictTensor.evaluation.{c, v, r} R n).mapHomotopyCategoryFactors
        (.up ℤ)).app P)

/-- Exact evaluation on homotopy categories, with both categories fixed.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def evaluationH (n : ℕᵒᵖ) :
    HomotopyCategory (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) ⥤
      HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ) :=
  (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapHomotopyCategory (.up ℤ)

/-- The exact-evaluation homotopy comparison with shared cochain functor.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def evaluationHFactors (n : ℕᵒᵖ) :
    HomotopyCategory.quotient _ (.up ℤ) ⋙ evaluationH.{c, v, r} R n ≅
      evaluationComplex.{c, v, r} R n ⋙ HomotopyCategory.quotient _ (.up ℤ) :=
  (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapHomotopyCategoryFactors (.up ℤ)

/-- Evaluation comparison of the fixed tensors, with its actual ordinary normalization.
The representative square is the specified comparison descent on two resolving factors.
Source: Stacks 07A4, 06YU and tensorComparisonDescent
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
structure EvaluationMaps (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (n : ℕᵒᵖ) where
  ordinary : OrdinaryEvaluation.{c, v, r} R n
  preserves : ∀ P : HomotopyCategory
    (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ),
    towerProperty.{c, v, r} R P → baseProperty.{c, v, r} R
      ((evaluationH.{c, v, r} R n).obj P)
  homotopy : t.homotopyTensor ⋙
      evaluationH.{c, v, r} R n ≅
    ((evaluationH.{c, v, r} R n).prod
      (evaluationH.{c, v, r} R n)) ⋙
        b.homotopyTensor
  derived : t.derivedTensor ⋙
      (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategory ≅
    ((LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategory.prod
      (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategory) ⋙ b.derivedTensor

/-- The ordinary-to-homotopy tensor evaluation square in arbitrary categories.
Source: Stacks 07A4 (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def TensorEvaluationSquare
    {A : Type a₁} [Category.{u₁} A] {B : Type a₂} [Category.{u₂} B]
    {H : Type h₁} [Category.{v₁} H] {K : Type h₂} [Category.{v₂} K]
    {D : Type x₂} [Category.{y₂} D] {D' : Type x₃} [Category.{y₃} D']
    (q : A ⥤ H) (q' : B ⥤ K) (Q : H ⥤ D) (Q' : K ⥤ D')
    (P : ObjectProperty H) (P' : ObjectProperty K)
    (F : A × A ⥤ A) (G : B × B ⥤ B)
    (t : TensorPresentation q Q F P) (b : TensorPresentation q' Q' G P')
    (E : A ⥤ B) (e : H ⥤ K) (ε : q ⋙ e ≅ E ⋙ q')
    (σ : t.homotopyTensor ⋙ e ≅ (e.prod e) ⋙ b.homotopyTensor)
    (ordinary : ∀ X Y : A, E.obj (F.obj (X, Y)) ≅ G.obj (E.obj X, E.obj Y)) : Prop :=
  ∀ X Y : A,
    e.map (t.homotopyComparison.hom.app (X, Y)) ≫ ε.hom.app (F.obj (X, Y)) ≫
        q'.map ((ordinary X Y).hom) =
      σ.hom.app (q.obj X, q.obj Y) ≫
        b.homotopyTensor.map (Prod.mkHom (ε.hom.app X) (ε.hom.app Y)) ≫
        b.homotopyComparison.hom.app (E.obj X, E.obj Y)

/-- Homotopy evaluation is induced by the ordinary normalized map.
Source: Stacks 07A4 (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def EvaluationHomotopyNormalized (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (n : ℕᵒᵖ) (e : EvaluationMaps.{c, v, r} R t b n) : Prop :=
  TensorEvaluationSquare
    (HomotopyCategory.quotient _ (.up ℤ)) (HomotopyCategory.quotient _ (.up ℤ))
    (towerQ.{c, v, r} R) (baseQ.{c, v, r} R)
    (towerProperty.{c, v, r} R) (baseProperty.{c, v, r} R)
    (towerF.{c, v, r} R)
    (baseF.{c, v, r} R) t b
    (evaluationComplex.{c, v, r} R n)
    (evaluationH.{c, v, r} R n)
    (evaluationHFactors.{c, v, r} R n)
    e.homotopy e.ordinary.chain

/-- The fixed two-sided comparisons determine derived evaluation.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def EvaluationDerivedNormalized (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (n : ℕᵒᵖ) (e : EvaluationMaps.{c, v, r} R t b n) : Prop := ∀ (A B : HomotopyCategory
    (ℕᵒᵖ ⥤ LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
    (hA : towerProperty.{c, v, r} R A) (hB : towerProperty.{c, v, r} R B),
    (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategory.map
        (t.resolvingComparison.hom.app (⟨A, hA⟩, ⟨B, hB⟩)) ≫
      e.derived.hom.app (DerivedCategory.Qh.obj A, DerivedCategory.Qh.obj B) ≫
      b.derivedTensor.map (Prod.mkHom
        ((LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.hom.app A)
        ((LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.hom.app B)) =
    (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.hom.app
        (t.homotopyTensor.obj (A, B)) ≫
      DerivedCategory.Qh.map (e.homotopy.hom.app (A, B)) ≫
      b.resolvingComparison.hom.app
        (⟨(evaluationH.{c, v, r} R n).obj A,
            e.preserves A hA⟩,
         ⟨(evaluationH.{c, v, r} R n).obj B,
            e.preserves B hB⟩)

/-- Evaluation comparisons with both normalization equations retained.
Source: Stacks 07A4, 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
structure Evaluation (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (n : ℕᵒᵖ) extends EvaluationMaps.{c, v, r} R t b n where
  homotopy_normalized : EvaluationHomotopyNormalized.{c, v, r} R t b n toEvaluationMaps
  normalized : EvaluationDerivedNormalized.{c, v, r} R t b n toEvaluationMaps

/-- The actual map of degree-zero coefficient complexes induced by an algebra-tower map.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def coefficientMap {S T : AlgebraTowers.{c, v, r} R} (a : S ⟶ T) :
    coefficientH.{c, v, r} R S ⟶ coefficientH.{c, v, r} R T :=
  (HomotopyCategory.quotient _ (.up ℤ)).map
    ((HomologicalComplex.single _ (.up ℤ) 0).map
      (Functor.whiskerRight a (algebraModules.{c, v, r} R)))

/-- The prescribed homotopy map with components 1 tensor a_n.
Source: Stacks 03EK (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def strictMap {S T : AlgebraTowers.{c, v, r} R} (a : S ⟶ T) :
    strictHomotopy.{c, v, r} R S ⟶ strictHomotopy.{c, v, r} R T :=
  NatTrans.mapHomotopyCategory ((reductionFamily.{c, v, r} R).map a) (.up ℤ)



universe d₁ w₁

/-- The actual exact diagonal on cochain complexes with shared source and target.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def diagonalComplex : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ ⥤
    TowerComplex.{c, v, r} R := (diagonal.{c, v, r} R).mapHomologicalComplex (.up ℤ)

/-- The ordinary-to-homotopy diagonal localization factor.
Source: Stacks 015F (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def diagonalHFactors :
    HomotopyCategory.quotient _ (.up ℤ) ⋙ diagonalH.{c, v, r} R ≅
      diagonalComplex.{c, v, r} R ⋙ HomotopyCategory.quotient _ (.up ℤ) :=
  (diagonal.{c, v, r} R).mapHomotopyCategoryFactors (.up ℤ)

/-- The actual strict tensor reduction functor on cochain complexes.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def strictC (S : AlgebraTowers.{c, v, r} R) :
    CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ ⥤
      TowerComplex.{c, v, r} R :=
  (LocalizedStrictTensor.reduction.{c, v, r} R S).mapHomologicalComplex (.up ℤ)

/-- The canonical homotopy factor for the actual strict tensor reduction.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def strictHFactors (S : AlgebraTowers.{c, v, r} R) :
    HomotopyCategory.quotient _ (.up ℤ) ⋙ strictHomotopy.{c, v, r} R S ≅
      strictC.{c, v, r} R S ⋙ HomotopyCategory.quotient _ (.up ℤ) :=
  (LocalizedStrictTensor.reduction.{c, v, r} R S).mapHomotopyCategoryFactors (.up ℤ)

/-- The ordinary model comparison with the same named tensor and reduction functors.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def ordinaryModelComparison (S : AlgebraTowers.{c, v, r} R)
    (o : OrdinaryModel.{c, v, r} R S)
    (P : CochainComplex (LocalizedStrictTensor.Modules.{c, v, r} R) ℤ) :
    (towerF.{c, v, r} R).obj
        ((diagonalComplex.{c, v, r} R).obj P, coefficient.{c, v, r} R S) ≅
      (strictC.{c, v, r} R S).obj P := o.chain P

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All computations are fixed by ordinary pure tensors and two-sided tensor descent.
The comparison itself is the explicit `comparison`, not an arbitrary derived isomorphism.
Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
structure ComputationMaps (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R) where
  towerOne : OneSidedFamily (Q := towerQ.{c, v, r} R) (towerProperty.{c, v, r} R)
    t.homotopyTensor t.derivedTensor
  baseOne : OneSidedFamily (Q := baseQ.{c, v, r} R) (baseProperty.{c, v, r} R)
    b.homotopyTensor b.derivedTensor
  ordinary : ∀ S : AlgebraTowers.{c, v, r} R, OrdinaryModel.{c, v, r} R S
  theta : ∀ S : AlgebraTowers.{c, v, r} R,
    diagonalH.{c, v, r} R ⋙
      (Functor.curry.obj t.homotopyTensor).flip.obj (coefficientH.{c, v, r} R S) ≅
        strictHomotopy.{c, v, r} R S
  evaluation : ∀ n : ℕᵒᵖ, Evaluation.{c, v, r} R t b n

/-- The model-identification square for a fixed tensor presentation.
Source: Stacks 06YU (blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def TensorModelSquare
    {A : Type a₁} [Category.{u₁} A] {B : Type a₂} [Category.{u₂} B]
    {H : Type h₁} [Category.{v₁} H] {K : Type h₂} [Category.{v₂} K]
    {D : Type d₁} [Category.{w₁} D]
    (q : A ⥤ H) (q' : B ⥤ K) (Q : K ⥤ D) (Pr : ObjectProperty K)
    (F : B × B ⥤ B) (t : TensorPresentation q' Q F Pr)
    (d : A ⥤ B) (δ : H ⥤ K) (μ : q ⋙ δ ≅ d ⋙ q') (coefficient : B)
    (s : A ⥤ B) (σ : H ⥤ K) (ν : q ⋙ σ ≅ s ⋙ q')
    (ordinary : ∀ X : A, F.obj (d.obj X, coefficient) ≅ s.obj X)
    (θ : δ ⋙ (Functor.curry.obj t.homotopyTensor).flip.obj (q'.obj coefficient) ≅ σ) : Prop :=
  ∀ X : A,
    θ.hom.app (q.obj X) =
      t.homotopyTensor.map (Prod.mkHom (μ.hom.app X) (𝟙 (q'.obj coefficient))) ≫
        t.homotopyComparison.hom.app (d.obj X, coefficient) ≫
        q'.map ((ordinary X).hom) ≫ ν.inv.app X

/-- The `theta_normalized` equation for the specified computation maps.
Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def ComputationThetaNormalized (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (m : ComputationMaps.{c, v, r} R t b) : Prop :=
  ∀ S : AlgebraTowers.{c, v, r} R,
    TensorModelSquare
      (HomotopyCategory.quotient _ (.up ℤ)) (HomotopyCategory.quotient _ (.up ℤ))
      (towerQ.{c, v, r} R) (towerProperty.{c, v, r} R) (towerF.{c, v, r} R) t
      (diagonalComplex.{c, v, r} R) (diagonalH.{c, v, r} R) (diagonalHFactors.{c, v, r} R)
      (coefficient.{c, v, r} R S)
      (strictC.{c, v, r} R S) (strictHomotopy.{c, v, r} R S) (strictHFactors.{c, v, r} R S)
      (ordinaryModelComparison.{c, v, r} R S (m.ordinary S)) (m.theta S)

/-- The `natural_first` equation for the specified computation maps.
Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def ComputationNaturalFirst (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (m : ComputationMaps.{c, v, r} R t b) : Prop := ∀ (S : AlgebraTowers.{c, v, r} R)
    (P P' : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
    (f : P ⟶ P') (hP : Good.{c, v, r} R P) (hP' : Good.{c, v, r} R P'),
    (derivedReduction.{c, v, r} R t S).map (DerivedCategory.Qh.map f) ≫
        (comparison.{c, v, r} R t m.towerOne S (m.theta S) P' hP'.2).hom =
      (comparison.{c, v, r} R t m.towerOne S (m.theta S) P hP.2).hom ≫
        DerivedCategory.Qh.map ((strictHomotopy.{c, v, r} R S).map f)

/-- The `natural_coefficient` equation for the specified computation maps.
Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def ComputationNaturalCoefficient (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (m : ComputationMaps.{c, v, r} R t b) : Prop :=
  ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (P : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
    (hP : Good.{c, v, r} R P),
    t.derivedTensor.map (Prod.mkHom
        (𝟙 (((diagonalD.{c, v, r} R)).obj (DerivedCategory.Qh.obj P)))
        (DerivedCategory.Qh.map (coefficientMap.{c, v, r} R a))) ≫
        (comparison.{c, v, r} R t m.towerOne T (m.theta T) P hP.2).hom =
      (comparison.{c, v, r} R t m.towerOne S (m.theta S) P hP.2).hom ≫
        DerivedCategory.Qh.map ((strictMap.{c, v, r} R a).app P)

/-- The `evaluation_normalized` equation for the specified computation maps.
Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
def ComputationEvaluationNormalized (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (m : ComputationMaps.{c, v, r} R t b) : Prop := ∀ (n : ℕᵒᵖ) (S : AlgebraTowers.{c, v, r} R)
    (P : HomotopyCategory (LocalizedStrictTensor.Modules.{c, v, r} R) (.up ℤ))
    (hP : Good.{c, v, r} R P),
    (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategory.map
        ((m.towerOne
          ((diagonalH.{c, v, r} R).obj P) hP.2).hom.app
            (coefficientH.{c, v, r} R S)) ≫
      (LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.hom.app
        (t.homotopyTensor.obj
          ((diagonalH.{c, v, r} R).obj P,
            coefficientH.{c, v, r} R S)) ≫
      DerivedCategory.Qh.map ((m.evaluation n).homotopy.hom.app
        ((diagonalH.{c, v, r} R).obj P,
          coefficientH.{c, v, r} R S)) =
    (m.evaluation n).derived.hom.app
        (DerivedCategory.Qh.obj
          ((diagonalH.{c, v, r} R).obj P),
          DerivedCategory.Qh.obj (coefficientH.{c, v, r} R S)) ≫
      b.derivedTensor.map (Prod.mkHom
        ((LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.hom.app
          ((diagonalH.{c, v, r} R).obj P))
        ((LocalizedStrictTensor.evaluation.{c, v, r} R n).mapDerivedCategoryFactorsh.hom.app
          (coefficientH.{c, v, r} R S))) ≫
      (m.baseOne
        ((evaluationH.{c, v, r} R n).obj
          ((diagonalH.{c, v, r} R).obj P))
        ((m.evaluation n).preserves _ hP.2)).hom.app
        ((evaluationH.{c, v, r} R n).obj
          (coefficientH.{c, v, r} R S))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The specified computation maps with all normalization and naturality equations.
Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-sf-strict-tensor-derived-evaluation-data). -/
structure Computation (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    extends ComputationMaps.{c, v, r} R t b where
  towerOne_conditions : OneSidedConditions (Q := towerQ.{c, v, r} R) (towerProperty.{c, v, r} R)
    t.homotopyTensor t.derivedTensor t.resolvingComparison towerOne
  baseOne_conditions : OneSidedConditions (Q := baseQ.{c, v, r} R) (baseProperty.{c, v, r} R)
    b.homotopyTensor b.derivedTensor b.resolvingComparison baseOne
  theta_normalized : ComputationThetaNormalized.{c, v, r} R t b toComputationMaps
  natural_first : ComputationNaturalFirst.{c, v, r} R t b toComputationMaps
  natural_coefficient : ComputationNaturalCoefficient.{c, v, r} R t b toComputationMaps
  evaluation_normalized : ComputationEvaluationNormalized.{c, v, r} R t b toComputationMaps

end SheafOfModules.StrictTensorEvaluation
