module

public import Sheaf.Paper.SmoothOperationCoefficientComparisons
public import Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison
public import Sheaf.Paper.RationalScalarComparisonIdentification
public import Sheaf.Paper.PbcDescentFunctors
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Whiskering

/-! # Identification of smooth operations on common coefficient stages

Source: smooth-purity transport, Step 2, common-stage morphisms and inverse equations
(blueprint: def-pur-smooth-operation-descent-specification).

The finite PBC operations are the specified localized integral operations transported
through the identity coefficient-presentation equivalences. The conclusion fixes
all comparison components, representative actions, shifts and transformation equations.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w z
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CommonStageSmoothOperationIdentification
set_option allowUnsafeReducibility true
attribute [local irreducible] HasDerivedCategory.standard stageEquivalence
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [smooth : SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System.{u, v} l Ω D hl (f := f))
  [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (JX : FdCoefficientComparison l Ω X) (JY : FdCoefficientComparison l Ω Y)

attribute [local irreducible] finiteOperation commonOperation
  conjugate conjugateIso pbcOperation finiteComparison strictComparison objectComparison

/-- Naturality on every unequal-field representative, its enlargement equation and
its explicit descended action. The comparisons have orientation beta = a (respectively b).
Source: smooth-purity transport Step 2, common-stage arrow calculation
(blueprint: def-pur-smooth-operation-descent-specification). -/
@[irreducible] def RepresentativeSpec
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    {A B : I → Type w}
    [∀ E, Category.{z} (A E)] [∀ E, Category.{z} (B E)]
    {SY : StageSystem A} {SX : StageSystem B} (P : StageSystem.Morphism SY SX) : Prop :=
  (∀ (K L : SY.PairCategory) (M : I) (hK : K.stage ≤ M) (hL : L.stage ≤ M)
    (a : K.toStage hK ⟶ L.toStage hL),
    P.functor.map (StageSystem.PairCategory.mkHom M hK hL a) =
      StageSystem.PairCategory.mkHom (X := P.functor.obj K) (Y := P.functor.obj L)
        M hK hL ((P.β hK).hom.app K.obj ≫ (P.Φ M).map a ≫ (P.β hL).inv.app L.obj)) ∧
  (∀ (E F M N : I) (hE : E ≤ M) (hF : F ≤ M) (h : M ≤ N)
    (K : A E) (L : A F) (a : (SY.T hE).obj K ⟶ (SY.T hF).obj L),
    SX.tr h (P.mapAt a) = P.mapAt (SY.tr h a))

/-- Components, equations, identities, composition and inverse equations of all
compatible transformations. Nothing assumes faithfulness of coefficient inclusions.
Source: smooth-purity transport Step 2, final two paragraphs
(blueprint: def-pur-smooth-operation-descent-specification). -/
@[irreducible] def TransformationSpec
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    {A B : I → Type w}
    [∀ E, Category.{z} (A E)] [∀ E, Category.{z} (B E)]
    {SY : StageSystem A} {SX : StageSystem B}
    (H G : StageSystem.Morphism SY SX) : Prop :=
  (∀ (θ : StageSystem.Morphism.Hom H G) (K : SY.PairCategory),
    (StageSystem.Morphism.descNatTrans θ).app K =
      (SX.ι K.stage).map ((θ.τ K.stage).app K.obj)) ∧
  (∀ (θ θ' : StageSystem.Morphism.Hom H G),
    (∀ E, θ.τ E = θ'.τ E) →
      StageSystem.Morphism.descNatTrans θ = StageSystem.Morphism.descNatTrans θ') ∧
  (StageSystem.Morphism.descNatTrans (StageSystem.Morphism.Hom.id H) = 𝟙 H.functor) ∧
  (StageSystem.Morphism.descNatTrans (StageSystem.Morphism.Hom.id G) = 𝟙 G.functor) ∧
  (∀ (θ : StageSystem.Morphism.Hom H G) (ψ : StageSystem.Morphism.Hom G H),
    StageSystem.Morphism.descNatTrans (θ.comp ψ) =
      StageSystem.Morphism.descNatTrans θ ≫ StageSystem.Morphism.descNatTrans ψ) ∧
  (∀ (θ : StageSystem.Morphism.Hom H G) (ψ : StageSystem.Morphism.Hom G H),
    (∀ E, θ.τ E ≫ ψ.τ E = 𝟙 (H.Φ E)) →
    (∀ E, ψ.τ E ≫ θ.τ E = 𝟙 (G.Φ E)) →
    (StageSystem.Morphism.descNatTrans θ ≫ StageSystem.Morphism.descNatTrans ψ =
      𝟙 H.functor) ∧
    (StageSystem.Morphism.descNatTrans ψ ≫ StageSystem.Morphism.descNatTrans θ =
      𝟙 G.functor) ∧
    (∀ E (K : A E),
      (SX.ι E).map ((θ.τ E).app K ≫ (ψ.τ E).app K) =
        (SX.ι E).map (𝟙 ((H.Φ E).obj K))) ∧
    (∀ E (K : A E),
      (SX.ι E).map ((ψ.τ E).app K ≫ (θ.τ E).app K) =
        (SX.ι E).map (𝟙 ((G.Φ E).obj K))))


/-- The framework representative u becomes j(target) J(u) j(source) inverse.
Here the recorded beta is inverse j. This explicitly retains both endpoints.
Source: smooth-purity transport Step 2, framework representative formula
(blueprint: def-pur-smooth-operation-descent-specification). -/
@[irreducible] def FrameworkRepresentativeSpec (W : Scheme.{max u v}) [IsNoetherian W]
    [dW : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [iW : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    (J : FdCoefficientComparison l Ω W) : Prop :=
  RepresentativeSpec J.family ∧ J.equivalence.functor = J.family.functor

/-- All operation-identification conclusions for one of the two specified functors.
No operation or arrow is supplied as an unconstrained hypothesis: the stage functor,
scalar map, component and normalization equations fix every one.
Source: smooth-purity transport Step 2, common-stage identification
(blueprint: def-pur-smooth-operation-descent-specification). -/
@[irreducible] def OperationSpec (exceptional : Bool)
    (P : StageSystem.Morphism
      (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out))
    (R : commonOperation.{u, v} l Ω D hl f d S exceptional ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ P.functor) : Prop :=
  (∀ E, HEq (P.Φ E) (pbcOperation.{u, v} l Ω D hl f d S JX JY exceptional E)) ∧
  (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    ∃ q : JX.equivalence.functor.obj
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι K.stage).obj
          ((finiteOperation.{u, v} l Ω D hl f d S exceptional K.stage).obj K.obj)) ≅
        P.functor.obj (JY.equivalence.functor.obj K),
      HEq q.hom (((pbcScalarSystem l Ω X dX.out iX.out).ι K.stage).map
        ((finiteComparisonAt.{u, v} l Ω D hl f d S JX JY exceptional K.stage K.obj).hom)) ∧
      R.hom.app K = JX.equivalence.functor.map
        ((objectComparison.{u, v} l Ω D hl f d S exceptional K).hom) ≫ q.hom) ∧
  (∀ (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E),
    ∃ a : ((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
        ((pbcOperation.{u, v} l Ω D hl f d S JX JY exceptional E).obj
          ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K)) ⟶
      (pbcOperation.{u, v} l Ω D hl f d S JX JY exceptional F).obj
        (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj
          ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K)),
      HEq a ((P.β h).hom.app ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K)) ∧
      ∃ (jX : (stageEquivalence.{u, v} l Ω X JX F).functor.obj
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj
              ((finiteOperation.{u, v} l Ω D hl f d S exceptional E).obj K)) ⟶
          ((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
            ((stageEquivalence.{u, v} l Ω X JX E).functor.obj
              ((finiteOperation.{u, v} l Ω D hl f d S exceptional E).obj K)))
        (jY : (stageEquivalence.{u, v} l Ω Y JY F).functor.obj
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).obj K) ⟶
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj
            ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K)),
        HEq jX ((JX.family.β h).inv.app
          ((finiteOperation.{u, v} l Ω D hl f d S exceptional E).obj K)) ∧
        HEq jY ((JY.family.β h).inv.app K) ∧
      (stageEquivalence.{u, v} l Ω X JX F).functor.map
          ((strictComparison.{u, v} l Ω D hl f d S exceptional h K).hom) ≫
        (finiteComparisonAt.{u, v} l Ω D hl f d S JX JY exceptional F
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).obj K)).hom ≫
        (pbcOperation.{u, v} l Ω D hl f d S JX JY exceptional F).map
          jY =
      jX ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T h).map
          ((finiteComparisonAt.{u, v} l Ω D hl f d S JX JY exceptional E K).hom) ≫ a) ∧
  RepresentativeSpec P ∧ StageSystem.Morphism.DescentSpec P



end WeilConjectures.CommonStageSmoothOperationIdentification
