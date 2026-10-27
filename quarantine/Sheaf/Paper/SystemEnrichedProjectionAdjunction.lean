module

public import Sheaf.Paper.SystemInternalHomRepresentability
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Order.Category.Preord
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Mathlib.CategoryTheory.Yoneda
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Representing-system adjunction from the compact-support projection

Source: the retained ordinary-system refinement of the middle RHom comparison in
prop-coef-integral-exceptional-adjoint, proof paragraph 2 and its final paragraph;
Stacks Project, Categories, Tag 0037
(blueprint: lem-coef-system-enriched-projection-adjunction).

The maps are defined on the coefficient-system category, using all punctual tests.
The index n denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry

attribute [local instance] Etale.SystemProjection.Image.inverseAdditive
  Etale.SystemProjection.Image.inverseLimits Etale.SystemProjection.Image.inverseColimits
open WeilConjectures.SemilinearSections

namespace WeilConjectures.SystemEnrichedProjection

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open SystemInternalHom

variable {X Y s : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  (RX : Representability l E aX) (RY : Representability l E aY)
  (F : Et l E X ⥤ Et l E Y) (G : Et l E Y ⥤ Et l E X) (adj : F ⊣ G)

/-- The coefficient-first tensor action on FM, before the projection map.
Source: retained ordinary-system proof, step 1
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def actionSource : Et l E s × Et l E X ⥤ Et l E Y :=
  (RY.structureImage.P.prod F) ⋙ RY.etale.closed.tensor

/-- Compact support of the coefficient-first tensor action on M.
Source: retained ordinary-system proof, step 1
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def actionTarget : Et l E s × Et l E X ⥤ Et l E Y :=
  (RX.structureImage.P.prod (𝟭 (Et l E X))) ⋙ RX.etale.closed.tensor ⋙ F

/-- The canonical base-change associator on the actual sequence sites.
Source: Stacks 03Q2, retained proof steps 1 and 5
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def structureSiteIso {f : X ⟶ Y} (c : Compactification f) (h : aX = f ≫ aY) :
    Etale.SystemProjection.siteMap aX ≅
      Etale.SystemProjection.siteMap aY ⋙ Etale.SystemProjection.siteMap c.g ⋙
        Etale.SystemProjection.siteMap c.i :=
  NatIso.prod (Iso.refl (𝟭 ℕ))
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f aY aX h) ≪≫
      isoWhiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ aY)
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) c.i c.g f c.comm))

/-- Canonical geometric tensor preservation, fixed on ordinary pure tensors and
on every K-flat total summand. The comparison cannot be multiplied by a scalar.
Source: Stacks 03EL and 07A4, retained proof step 1
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
structure PullTensor {V W : Scheme.{u}} {g : V ⟶ W}
    (d : Etale.SystemProjection.Image g (coefficients l E))
    (A : EtData l E W) (B : EtData l E V) where
  tensor : A.closed.tensor ⋙ d.P ≅ (d.P.prod d.P) ⋙ B.closed.tensor
  model : letI := d.inverseAdditive
    letI := d.inverseLimits
    letI := d.inverseColimits
    TensorComparisonModel.{u + 1, u, u}
      (coefficientSequenceTopology W.smallEtaleTopology)
      (coefficientSequenceTopology V.smallEtaleTopology)
      (Etale.SystemProjection.rings W (coefficients l E))
      (Etale.SystemProjection.rings V (coefficients l E)) d.inverse A.closed B.closed
      A.tensorModels B.tensorModels tensor
  pure : ∀ (M N : Etale.SystemProjection.Modules W (coefficients l E))
    (n : ℕ) (U : W.Etaleᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
    HEq ((((d.adjunction.homEquiv _ _) (model.ordinary M N).hom).val.app
      (op (n, U.unop)))
        (tensorSection.{u + 1, u, u} (coefficientSequenceTopology W.smallEtaleTopology)
          (Etale.SystemProjection.rings W (coefficients l E)) M N (op (n, U.unop)) x y))
      (tensorSection.{u + 1, u, u} (coefficientSequenceTopology V.smallEtaleTopology)
        (Etale.SystemProjection.rings V (coefficients l E)) (d.inverse.obj M)
        (d.inverse.obj N)
        (op (n, (MorphismProperty.Over.pullback @Etale ⊤ g).obj U.unop))
        (((d.adjunction.unit.app M).val.app (op (n, U.unop))) x)
        (((d.adjunction.unit.app N).val.app (op (n, U.unop))) y))

/-- Presentation of the canonical system projection. The structure pullback
compositor is the mate of the actual base-change associator on sections, localized
termwise. The open comparison is the transpose of the open unit and inverse tensor
comparison. The projection below is then its proper-counit mate, before evaluation.
Source: Stacks 03EL, 03S2, 07A4 and 0B56, retained proof steps 1 and 5
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
structure ProjectionData {f : X ⟶ Y} (c : Compactification f) (h : aX = f ≫ aY)
    (support : Etale.SystemProjection.Support c (coefficients l E)) where
  ambient : EtData l E c.Z
  properTensor : PullTensor l E support.proper RY.etale ambient
  openTensor : PullTensor l E support.openImage.toImage ambient RX.etale
  ordinaryPush : support.openImage.toDirectImage.push ⋙ support.proper.toDirectImage.push ⋙
    RY.structureImage.toDirectImage.push ≅ RX.structureImage.toDirectImage.push
  sections : ∀ (M : Etale.SystemProjection.Modules X (coefficients l E))
    (n : ℕ) (U : s.Etaleᵒᵖ)
    (x : ((support.openImage.toDirectImage.push ⋙ support.proper.toDirectImage.push ⋙
      RY.structureImage.toDirectImage.push).obj M).val.obj (op (n, U.unop))),
    HEq (((ordinaryPush.hom.app M).val.app (op (n, U.unop))) x)
      (M.val.map ((structureSiteIso c h).hom.app (n, U.unop)).op x)
  composition : RY.structureImage.P ⋙ support.proper.P ⋙ support.openImage.P ≅
    RX.structureImage.P
  composition_termwise : composition =
    (letI := RY.structureImage.inverseAdditive
     letI := RY.structureImage.inverseLimits
     letI := RY.structureImage.inverseColimits
     letI := support.proper.inverseAdditive
     letI := support.proper.inverseLimits
     letI := support.proper.inverseColimits
     letI := support.openImage.inverseAdditive
     letI := support.openImage.inverseLimits
     letI := support.openImage.inverseColimits
     letI := RX.structureImage.inverseAdditive
     letI := RX.structureImage.inverseLimits
     letI := RX.structureImage.inverseColimits
     let q := ((conjugateIsoEquiv
       ((RY.structureImage.adjunction.comp support.proper.adjunction).comp
         support.openImage.adjunction) RX.structureImage.adjunction).symm ordinaryPush).symm
     isoWhiskerRight (Functor.mapDerivedCategoryCompIso
       RY.structureImage.inverse support.proper.inverse).symm
         support.openImage.inverse.mapDerivedCategory ≪≫
       (Functor.mapDerivedCategoryCompIso
         (RY.structureImage.inverse ⋙ support.proper.inverse)
           support.openImage.inverse).symm ≪≫ Functor.mapDerivedCategoryNatIso q)
  openComparison : ∀ (P : Et l E s) (M : Et l E X),
    ambient.closed.tensor.obj
      (support.proper.P.obj (RY.structureImage.P.obj P), support.openImage.J.obj M) ≅
      support.openImage.J.obj
        (RX.etale.closed.tensor.obj (RX.structureImage.P.obj P, M))
  open_transpose : ∀ (P : Et l E s) (M : Et l E X),
    (support.openImage.derivedAdjunction.homEquiv _ _)
      ((openComparison P M).inv) =
      RX.etale.closed.tensor.map (Prod.mkHom (composition.inv.app P)
        (support.openImage.derivedAdjunction.unit.app M)) ≫
      openTensor.tensor.inv.app
        (support.proper.P.obj (RY.structureImage.P.obj P), support.openImage.J.obj M)

/-- Canonical compact-support projection as the proper counit transpose followed
by the specified open tensor comparison. No map is chosen from its finite fibers.
Source: Stacks 0B56 and 07A4, retained proof steps 1 and 5
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def ProjectionData.component {f : X ⟶ Y} {c : Compactification f} {h : aX = f ≫ aY}
    {support : Etale.SystemProjection.Support c (coefficients l E)}
    (d : ProjectionData l E RX RY c h support) (P : Et l E s) (M : Et l E X) :
    (actionSource l E RY support.F).obj (P, M) ⟶
      (actionTarget l E RX support.F).obj (P, M) :=
  (support.proper.derivedAdjunction.homEquiv _ _)
    (d.properTensor.tensor.hom.app
      (RY.structureImage.P.obj P, support.proper.R.obj (support.openImage.J.obj M)) ≫
      d.ambient.closed.tensor.map
        (Prod.mkHom (𝟙 _) (support.proper.derivedAdjunction.counit.app
          (support.openImage.J.obj M)))) ≫
    support.proper.R.map ((d.openComparison P M).hom)

variable (π : actionSource l E RY F ≅ actionTarget l E RX F)

/-- The all-test representing bijection, in the order tensor-Hom, inverse projection,
actual adjunction, inverse tensor-Hom. Both representing bijections are the recorded
structure-morphism adjunction followed by closed transposition.
Source: retained ordinary-system proof, step 1; Stacks 0037
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def testEquiv (M : Et l E X) (N : Et l E Y) (P : Et l E s) :
    (P ⟶ representingObject l E RY.structureImage (F.obj M) N) ≃
      (P ⟶ representingObject l E RX.structureImage M (G.obj N)) :=
  (representingEquiv l E RY.structureImage RY.etale (F.obj M) N P).trans
    ((Iso.homCongr (π.app (P, M)) (Iso.refl N)).trans
      ((adj.homEquiv _ N).trans
        (representingEquiv l E RX.structureImage RX.etale M (G.obj N) P).symm))

/-- The forward representing morphism is obtained by testing at its source identity.
It is defined before any finite evaluation or inverse limit.
Source: retained ordinary-system proof, step 2
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def forward (M : Et l E X) (N : Et l E Y) :
    representingObject l E RY.structureImage (F.obj M) N ⟶
      representingObject l E RX.structureImage M (G.obj N) :=
  testEquiv l E RX RY F G adj π M N _ (𝟙 _)

/-- The inverse representing morphism is obtained from the inverse all-test bijection.
Source: retained ordinary-system proof, steps 2--3
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def backward (M : Et l E X) (N : Et l E Y) :
    representingObject l E RX.structureImage M (G.obj N) ⟶
      representingObject l E RY.structureImage (F.obj M) N :=
  (testEquiv l E RX RY F G adj π M N _).symm (𝟙 _)

/-- The canonical change of inputs on the punctual representing object.
Source: retained ordinary-system proof, step 2
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def representingMap {W : Scheme.{u}} {a : W ⟶ s}
    (R : Representability l E a) {M M' N N' : Et l E W}
    (m : M' ⟶ M) (n : N ⟶ N') :
    representingObject l E R.structureImage M N ⟶
      representingObject l E R.structureImage M' N' :=
  R.structureImage.R.map ((etHom l E W).map (Prod.mkHom m.op n))

/-- Transport of the explicitly defined forward map through the canonical comparisons
of the recorded representability theorem. Invertibility is a conclusion below.
Source: retained ordinary-system proof, step 6
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def towerForward (M : Et l E X) (N : Et l E Y)
    (cY : IsIso (mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections
      (F.obj M) N)) :
    (coefficientSequenceGlobalHom.{u, u} l E Y).obj
        (op (RY.comparison.P.obj (F.obj M)), RY.comparison.P.obj N) ⟶
      (coefficientSequenceGlobalHom.{u, u} l E X).obj
        (op (RX.comparison.P.obj M), RX.comparison.P.obj (G.obj N)) :=
  (@asIso _ _ _ _ (mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections
    (F.obj M) N) cY).inv ≫
    RY.point.derived.map (forward l E RX RY F G adj π M N) ≫
    mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections M (G.obj N)

/-- Underlying abelian-tower inverse, defined by the same canonical comparisons.
Source: retained ordinary-system proof, step 6
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def towerBackward (M : Et l E X) (N : Et l E Y)
    (cX : IsIso (mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections
      M (G.obj N))) :
    (coefficientSequenceGlobalHom.{u, u} l E X).obj
        (op (RX.comparison.P.obj M), RX.comparison.P.obj (G.obj N)) ⟶
      (coefficientSequenceGlobalHom.{u, u} l E Y).obj
        (op (RY.comparison.P.obj (F.obj M)), RY.comparison.P.obj N) :=
  (@asIso _ _ _ _ (mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections
    M (G.obj N)) cX).inv ≫
    RX.point.derived.map (backward l E RX RY F G adj π M N) ≫
    mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections (F.obj M) N

/-- Punctual internal Hom at one finite coefficient level, with actual derived
structure-morphism pushforward. Source: Stacks 08J9, retained proof step 4
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def finiteObject {W : Scheme.{u}} (a : W ⟶ s) (n : ℕ)
    (M N : Etale.DerivedCategoryModule (coefficient l E n) W) :=
  (Etale.lowerStar (ModuleCat.{u + 1} (coefficient l E n)) a).rightDerivedFunctor.obj
    (((Etale.derivedHom (ModuleCat.{u + 1} (coefficient l E n)) W).obj (op M)).obj N)

/-- The finite representing bijection is the actual geometric and tensor-Hom
adjunction. The fixed-ring presentation puts the mapping input first, as in the
published finite projection formula. Source: Stacks 0037 and 08J9, retained proof step 4
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def finiteEquiv {W : Scheme.{u}} (a : W ⟶ s) (n : ℕ)
    (M N : Etale.DerivedCategoryModule (coefficient l E n) W)
    (P : Etale.DerivedCategoryModule (coefficient l E n) s) :
    (P ⟶ finiteObject l E a n M N) ≃
      (((Etale.derivedTensor (ModuleCat.{u + 1} (coefficient l E n)) W).obj M).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (coefficient l E n)) a).leftDerivedFunctor.obj P)
          ⟶ N) :=
  ((Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (coefficient l E n)) a).homEquiv P _).symm.trans
      ((Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} (coefficient l E n)) M).homEquiv
        ((Etale.upperStar (ModuleCat.{u + 1} (coefficient l E n)) a).leftDerivedFunctor.obj P)
          N).symm

/-- Exact pullback composition in the fixed finite-coefficient presentation.
Source: Stacks 0037, retained proof step 4
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def finitePullComp (f : X ⟶ Y) (h : aX = f ≫ aY) (n : ℕ) :=
  Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (coefficient l E n)) f aY aX h

/-- The actual finite compactification projection followed by structure pullback
composition. This is the published proper-counit/open-extension word.
Source: retained proof step 4; Stacks 0B56
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def finiteProjection {f : X ⟶ Y} (c : Compactification f) (h : aX = f ≫ aY)
    (n : ℕ) (P : Etale.DerivedCategoryModule (coefficient l E n) s)
    (M : Etale.DerivedCategoryModule (coefficient l E n) X) :=
  ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} (coefficient l E n)) c).app M).app
      ((Etale.upperStar (ModuleCat.{u + 1} (coefficient l E n)) aY).leftDerivedFunctor.obj P) ≫
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (coefficient l E n)) c).map
        (((Etale.derivedTensor (ModuleCat.{u + 1} (coefficient l E n)) X).obj M).map
          ((finitePullComp l E f h n).inv.app P))

/-- The finite inverse mapping-complex adjunction, defined by transposing the
actual finite counit after the actual finite projection and mapped evaluation.
Source: retained proof steps 3--4; Stacks 0037, 08J9 and 0B56
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def finiteBackward {f : X ⟶ Y} (c : Compactification f) (h : aX = f ≫ aY)
    (n : ℕ)
    (Gn : Etale.DerivedCategoryModule (coefficient l E n) Y ⥤
      Etale.DerivedCategoryModule (coefficient l E n) X)
    (adjn : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (coefficient l E n)) c ⊣ Gn)
    (M : Etale.DerivedCategoryModule (coefficient l E n) X)
    (N : Etale.DerivedCategoryModule (coefficient l E n) Y) :
    finiteObject l E aX n M (Gn.obj N) ⟶
      finiteObject l E aY n
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (coefficient l E n)) c).obj M) N :=
  (finiteEquiv l E aY n _ N _).symm
    (finiteProjection l E c h n (finiteObject l E aX n M (Gn.obj N)) M ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (coefficient l E n)) c).map
          (finiteEquiv l E aX n M (Gn.obj N) _ (𝟙 _)) ≫ adjn.counit.app N)

/-- Finite evaluation of the specified adjunction, retaining the counit equation.
Source: Zheng Lemma 4.10, retained proof step 4
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
structure FiniteAdjunction {f : X ⟶ Y} (c : Compactification f) (n : ℕ) where
  right : Etale.DerivedCategoryModule (coefficient l E n) Y ⥤
    Etale.DerivedCategoryModule (coefficient l E n) X
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (coefficient l E n)) c ⊣ right
  leftComparison : F ⋙ (RY.levels n).E ≅ (RX.levels n).E ⋙
    Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (coefficient l E n)) c
  rightComparison : G ⋙ (RX.levels n).E ≅ (RY.levels n).E ⋙ right
  counit : ∀ N : Et l E Y,
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (coefficient l E n)) c).map (rightComparison.hom.app N) ≫
        adjunction.counit.app ((RY.levels n).E.obj N) =
      leftComparison.inv.app (G.obj N) ≫ (RY.levels n).E.map (adj.counit.app N)

/-- Finite evaluation of the coefficient-system isomorphism is the finite derived
mapping-complex adjunction. The comparisons are part of the conclusion and their
inverse is fixed by the explicit finite counit transpose, rather than chosen up to
an unnamed isomorphism. Source: retained proof step 4
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def FiniteCompatibility {f : X ⟶ Y} (c : Compactification f) (h : aX = f ≫ aY)
    (M : Et l E X) (N : Et l E Y) : Prop :=
  ∀ (n : ℕ) (d : FiniteAdjunction l E RX RY F G adj c n)
    (es : Etale.SystemProjection.Evaluation s (coefficients l E) n),
    ∃ (cY : es.E.obj (representingObject l E RY.structureImage (F.obj M) N) ≅
      finiteObject l E aY n
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (coefficient l E n)) c).obj ((RX.levels n).E.obj M))
        ((RY.levels n).E.obj N))
      (cX : es.E.obj (representingObject l E RX.structureImage M (G.obj N)) ≅
        finiteObject l E aX n ((RX.levels n).E.obj M)
          (d.right.obj ((RY.levels n).E.obj N))),
      cX.inv ≫ es.E.map (backward l E RX RY F G adj π M N) ≫ cY.hom =
        finiteBackward l E c h n d.right d.adjunction
          ((RX.levels n).E.obj M) ((RY.levels n).E.obj N) ∧
      (cY.inv ≫ es.E.map (forward l E RX RY F G adj π M N) ≫ cX.hom) ≫
        finiteBackward l E c h n d.right d.adjunction
          ((RX.levels n).E.obj M) ((RY.levels n).E.obj N) = 𝟙 _ ∧
      finiteBackward l E c h n d.right d.adjunction
          ((RX.levels n).E.obj M) ((RY.levels n).E.obj N) ≫
        (cY.inv ≫ es.E.map (forward l E RX RY F G adj π M N) ≫ cX.hom) = 𝟙 _ ∧
      ∃ (tX : ∀ P : Et l E s,
          (RX.levels n).E.obj
            (RX.etale.closed.tensor.obj (RX.structureImage.P.obj P, M)) ≅
          ((Etale.derivedTensor (ModuleCat.{u + 1} (coefficient l E n)) X).obj
            ((RX.levels n).E.obj M)).obj
              ((Etale.upperStar (ModuleCat.{u + 1} (coefficient l E n)) aX).leftDerivedFunctor.obj
                (es.E.obj P)))
        (tY : ∀ P : Et l E s,
          (RY.levels n).E.obj
            (RY.etale.closed.tensor.obj (RY.structureImage.P.obj P, F.obj M)) ≅
          ((Etale.derivedTensor (ModuleCat.{u + 1} (coefficient l E n)) Y).obj
            ((Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (coefficient l E n)) c).obj
                ((RX.levels n).E.obj M))).obj
              ((Etale.upperStar (ModuleCat.{u + 1} (coefficient l E n)) aY).leftDerivedFunctor.obj
                (es.E.obj P))),
        (∀ (P : Et l E s)
          (x : P ⟶ representingObject l E RX.structureImage M (G.obj N)),
          finiteEquiv l E aX n _ _ (es.E.obj P) (es.E.map x ≫ cX.hom) =
            (tX P).inv ≫ (RX.levels n).E.map
              (representingEquiv l E RX.structureImage RX.etale M (G.obj N) P x) ≫
                d.rightComparison.hom.app N) ∧
        (∀ (P : Et l E s)
          (y : P ⟶ representingObject l E RY.structureImage (F.obj M) N),
          finiteEquiv l E aY n _ _ (es.E.obj P) (es.E.map y ≫ cY.hom) =
            (tY P).inv ≫ (RY.levels n).E.map
              (representingEquiv l E RY.structureImage RY.etale (F.obj M) N P y)) ∧
        (∀ P : Et l E s,
          (RY.levels n).E.map (π.hom.app (P, M)) ≫
            d.leftComparison.hom.app
              (RX.etale.closed.tensor.obj (RX.structureImage.P.obj P, M)) ≫
            (Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (coefficient l E n)) c).map (tX P).hom =
          (tY P).hom ≫ finiteProjection l E c h n (es.E.obj P) ((RX.levels n).E.obj M))

/-- The actual coefficient ring system, placed in degree zero.
Source: Stacks 08J9, retained proof step 5
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def pointUnit (s : Scheme.{u}) : Et l E s :=
  DerivedCategory.Q.obj (ringedTensorUnitComplex.{u + 1, u, u}
    (coefficientSequenceTopology s.smallEtaleTopology)
    (Etale.SystemProjection.rings s (coefficients l E)))

/-- Degree-zero Hom is the unit-test specialization, with unit-action identifications
and the projection-unit equation retained explicitly.
Source: Stacks 0037, retained proof step 5
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
def UnitCompatibility : Prop :=
  ∃ (ux : ∀ U : Et l E X,
      RX.etale.closed.tensor.obj (RX.structureImage.P.obj (pointUnit l E s), U) ≅ U)
    (uy : ∀ V : Et l E Y,
      RY.etale.closed.tensor.obj (RY.structureImage.P.obj (pointUnit l E s), V) ≅ V),
    (∀ U : Et l E X, π.hom.app (pointUnit l E s, U) ≫ F.map (ux U).hom =
      (uy (F.obj U)).hom) ∧
    (∀ (U : Et l E X) (V : Et l E Y) (h : F.obj U ⟶ V),
      (ux U).inv ≫ representingEquiv l E RX.structureImage RX.etale U (G.obj V)
        (pointUnit l E s)
        (testEquiv l E RX RY F G adj π U V (pointUnit l E s)
          ((representingEquiv l E RY.structureImage RY.etale (F.obj U) V
            (pointUnit l E s)).symm ((uy (F.obj U)).hom ≫ h))) =
        adj.unit.app U ≫ G.map h) ∧
    (∀ (U : Et l E X) (V : Et l E Y) (g : U ⟶ G.obj V),
      (uy (F.obj U)).inv ≫ representingEquiv l E RY.structureImage RY.etale (F.obj U) V
        (pointUnit l E s)
        ((testEquiv l E RX RY F G adj π U V (pointUnit l E s)).symm
          ((representingEquiv l E RX.structureImage RX.etale U (G.obj V)
            (pointUnit l E s)).symm ((ux U).hom ≫ g))) =
        F.map g ≫ adj.counit.app V)

/-- The complete enriched adjunction assertion: actual system equations, conditional
finite evaluation, degree-zero formulas, and conjugation to towers followed by total
right derived limit. Bounds and Tor amplitudes are allowed to depend on the level.
Source: retained ordinary-system argument, steps 1--7; Stacks 0037, 08J9, 0941
(blueprint: lem-coef-system-enriched-projection-adjunction). -/
structure Conclusion {f : X ⟶ Y} (c : Compactification f) (h : aX = f ≫ aY)
    (M : Et l E X) (N : Et l E Y)
    (hM : EtNormalized l E RX.etale M) (hN : EtNormalized l E RY.etale N)
    (hFM : EtNormalized l E RY.etale (F.obj M))
    (hGN : EtNormalized l E RX.etale (G.obj N))
    (fM : EtFinite l E X RX.levels M) (fN : EtFinite l E Y RY.levels N)
    (fFM : EtFinite l E Y RY.levels (F.obj M))
    (fGN : EtFinite l E X RX.levels (G.obj N)) : Prop where
  system_isomorphism : IsIso (forward l E RX RY F G adj π M N)
  forward_inverse : forward l E RX RY F G adj π M N ≫
    backward l E RX RY F G adj π M N = 𝟙 _
  inverse_forward : backward l E RX RY F G adj π M N ≫
    forward l E RX RY F G adj π M N = 𝟙 _
  forward_transpose : ∀ (P : Et l E s)
    (x : P ⟶ representingObject l E RY.structureImage (F.obj M) N),
    representingEquiv l E RX.structureImage RX.etale M (G.obj N) P
      (x ≫ forward l E RX RY F G adj π M N) =
    adj.unit.app (RX.etale.closed.tensor.obj (RX.structureImage.P.obj P, M)) ≫
      G.map (π.inv.app (P, M) ≫
        representingEquiv l E RY.structureImage RY.etale (F.obj M) N P x)
  inverse_transpose : ∀ (P : Et l E s)
    (y : P ⟶ representingObject l E RX.structureImage M (G.obj N)),
    representingEquiv l E RY.structureImage RY.etale (F.obj M) N P
      (y ≫ backward l E RX RY F G adj π M N) =
    π.hom.app (P, M) ≫ F.map
      (representingEquiv l E RX.structureImage RX.etale M (G.obj N) P y) ≫
        adj.counit.app N
  tests : ∀ (P : Et l E s)
    (x : P ⟶ representingObject l E RY.structureImage (F.obj M) N),
    x ≫ forward l E RX RY F G adj π M N = testEquiv l E RX RY F G adj π M N P x
  inverse_tests : ∀ (P : Et l E s)
    (y : P ⟶ representingObject l E RX.structureImage M (G.obj N)),
    y ≫ backward l E RX RY F G adj π M N =
      (testEquiv l E RX RY F G adj π M N P).symm y
  naturality : ∀ (M' : Et l E X) (N' : Et l E Y) (m : M' ⟶ M) (n : N ⟶ N'),
    representingMap l E RY (F.map m) n ≫ forward l E RX RY F G adj π M' N' =
      forward l E RX RY F G adj π M N ≫ representingMap l E RX m (G.map n)
  inverse_naturality : ∀ (M' : Et l E X) (N' : Et l E Y) (m : M' ⟶ M) (n : N ⟶ N'),
    representingMap l E RX m (G.map n) ≫ backward l E RX RY F G adj π M' N' =
      backward l E RX RY F G adj π M N ≫ representingMap l E RY (F.map m) n
  finite : FiniteCompatibility l E RX RY F G adj π c h M N
  degree_zero : UnitCompatibility l E RX RY F G adj π
  tower_isomorphism : IsIso
    (towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN))
  tower_forward_inverse :
    towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN) ≫
      towerBackward l E RX RY F G adj π M N (RX.mapping_iso _ _ hM hGN fM fGN) = 𝟙 _
  tower_inverse_forward :
    towerBackward l E RX RY F G adj π M N (RX.mapping_iso _ _ hM hGN fM fGN) ≫
      towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN) = 𝟙 _
  tower_tests : ∀ (P : Et l E s)
    (x : P ⟶ representingObject l E RY.structureImage (F.obj M) N),
    RY.point.derived.map x ≫
      mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections (F.obj M) N ≫
      towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN) =
    RX.point.derived.map (testEquiv l E RX RY F G adj π M N P x) ≫
      mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections M (G.obj N)
  tower_inverse_tests : ∀ (P : Et l E s)
    (y : P ⟶ representingObject l E RX.structureImage M (G.obj N)),
    RX.point.derived.map y ≫
      mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections M (G.obj N) ≫
      towerBackward l E RX RY F G adj π M N (RX.mapping_iso _ _ hM hGN fM fGN) =
    RY.point.derived.map ((testEquiv l E RX RY F G adj π M N P).symm y) ≫
      mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections (F.obj M) N
  tower_naturality : ∀ (M' : Et l E X) (N' : Et l E Y) (m : M' ⟶ M) (n : N ⟶ N'),
    RY.point.derived.map
      (representingMap l E RY (F.map m) n ≫ forward l E RX RY F G adj π M' N') =
    RX.point.derived.map
      (forward l E RX RY F G adj π M N ≫ representingMap l E RX m (G.map n))
  limit_naturality : ∀ (M' : Et l E X) (N' : Et l E Y) (m : M' ⟶ M) (n : N ⟶ N'),
    coefficientMappingLimit.{u + 1}.map (RY.point.derived.map
      (representingMap l E RY (F.map m) n ≫ forward l E RX RY F G adj π M' N')) =
    coefficientMappingLimit.{u + 1}.map (RX.point.derived.map
      (forward l E RX RY F G adj π M N ≫ representingMap l E RX m (G.map n)))
  limit_tests : ∀ (P : Et l E s)
    (x : P ⟶ representingObject l E RY.structureImage (F.obj M) N),
    coefficientMappingLimit.{u + 1}.map (RY.point.derived.map x ≫
      mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections (F.obj M) N ≫
      towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN)) =
    coefficientMappingLimit.{u + 1}.map
      (RX.point.derived.map (testEquiv l E RX RY F G adj π M N P x) ≫
        mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections M (G.obj N))
  limit_inverse_tests : ∀ (P : Et l E s)
    (y : P ⟶ representingObject l E RX.structureImage M (G.obj N)),
    coefficientMappingLimit.{u + 1}.map (RX.point.derived.map y ≫
      mappingComparison l E RX.tensor RX.structureImage RX.point RX.sections M (G.obj N) ≫
      towerBackward l E RX RY F G adj π M N (RX.mapping_iso _ _ hM hGN fM fGN)) =
    coefficientMappingLimit.{u + 1}.map
      (RY.point.derived.map ((testEquiv l E RX RY F G adj π M N P).symm y) ≫
        mappingComparison l E RY.tensor RY.structureImage RY.point RY.sections (F.obj M) N)
  limit_isomorphism : IsIso (coefficientMappingLimit.{u + 1}.map
    (towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN)))
  limit_forward_inverse :
    coefficientMappingLimit.{u + 1}.map
      (towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN)) ≫
    coefficientMappingLimit.{u + 1}.map
      (towerBackward l E RX RY F G adj π M N (RX.mapping_iso _ _ hM hGN fM fGN)) = 𝟙 _
  limit_inverse_forward :
    coefficientMappingLimit.{u + 1}.map
      (towerBackward l E RX RY F G adj π M N (RX.mapping_iso _ _ hM hGN fM fGN)) ≫
    coefficientMappingLimit.{u + 1}.map
      (towerForward l E RX RY F G adj π M N (RY.mapping_iso _ _ hFM hN fFM fN)) = 𝟙 _

/-- Enriched adjunction for the actual compactification support functor and its
specified adjunction. The invertible projection is required to be exactly the
canonical proper-counit/open-unit word, with its ordinary and K-flat normalizations.
Source: retained refinement of prop-coef-integral-exceptional-adjoint, second and
final paragraphs; Stacks 0037, 08J9, 0B56 and 0941
(blueprint: lem-coef-system-enriched-projection-adjunction).

Proof: construct the ordinary tensor pullback comparison by sheafifying the map
on pure tensors determined by the geometric adjunction unit. Its inverse on total
summands and K-flat preservation give the derived tensor comparison. The ordinary
pushforward compositor is restriction by the base-change associator; take its mate
and localize termwise. The open tensor comparison is the open-unit transpose, and
its proper-counit mate is the specified projection. Then compose the two representing
bijections with inverse projection and the
actual adjunction for every test P. Their naturality gives mutually inverse Yoneda
maps, obtained by testing at the respective identity maps. Yoneda injectivity proves
the inverse and naturality equations in the system category. Reading the inverse
bijection gives projection, mapped evaluation, and the specified counit; reading the
forward gives the unit and mapped inverse projection. Under counit-compatible finite
identifications these explicit words evaluate to the finite words, using normalized
first inputs for internal Hom. Evaluation only transports the already proved inverse
equations. At the coefficient unit the proper projection is the identity by its
unit normalization, as is the open comparison, so the formulas reduce to the ordinary
unit/counit Hom bijections. For the two normalized constructible finite-Tor pairs,
the recorded representability comparisons are invertible; conjugating the two maps
by these comparisons proves the abelian-tower equations and transports all naturality
and projection squares. Finally apply the actual total right derived limit functor:
functoriality preserves those inverse equations and every transported square. -/
theorem systemEnrichedProjectionAdjunction (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (RX : Representability l E (X ↘ Spec (CommRingCat.of D.k)))
    (RY : Representability l E (Y ↘ Spec (CommRingCat.of D.k)))
    (support : Etale.SystemProjection.Support c (coefficients l E))
    (G : Et l E Y ⥤ Et l E X) (adj : support.F ⊣ G) :
    Nonempty (ProjectionData l E RX RY c (comp_over f _).symm support) ∧
    ∀ (d : ProjectionData l E RX RY c (comp_over f _).symm support)
    (π : actionSource l E RY support.F ≅ actionTarget l E RX support.F)
    (_canonical : ∀ (P : Et l E (Spec (CommRingCat.of D.k))) (U : Et l E X),
      π.hom.app (P, U) = ProjectionData.component l E RX RY d P U)
    (M : Et l E X) (N : Et l E Y)
    (hM : EtNormalized l E RX.etale M) (hN : EtNormalized l E RY.etale N)
    (hFM : EtNormalized l E RY.etale (support.F.obj M))
    (hGN : EtNormalized l E RX.etale (G.obj N))
    (fM : EtFinite l E X RX.levels M) (fN : EtFinite l E Y RY.levels N)
    (fFM : EtFinite l E Y RY.levels (support.F.obj M))
    (fGN : EtFinite l E X RX.levels (G.obj N)),
    Conclusion l E RX RY support.F G adj π c (comp_over f _).symm M N
      hM hN hFM hGN fM fN fFM fGN := by
  sorry

end WeilConjectures.SystemEnrichedProjection

