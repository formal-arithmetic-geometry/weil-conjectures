# AlgebraicGeometry.Scheme.completedPullbackFunctor and finite-reduction interfaces

## Reason

Proving completed-pullback quotient coherence needs the existing
FiniteQuotientTransitionCompatibility theorem. That module and two of its
normalization dependencies imported CompletedPullbackReduction, so importing it
back from the parent would create a cycle. Move the already proved finite
interface, including its private proof helpers, into CompletedPullbackReductionData;
publicly re-export it from the parent, and redirect only the three lower imports.
The mathematical statements and component maps are unchanged. The generic
composite-counit helper is generalized to supplied functors and comparisons
between arbitrary categories. Native complex counits are assembled without
reconstructing their underlying abelian-category data.

The extracted file also avoids large unfolding/typeclass searches: use the explicit
universe-correct module adjunction, identify the coefficient map by its limit
projections, and use the tensor comparison equations rather than full unfolding.
Local irreducibility boundaries keep large coefficient and pullback constructions
abstract. The derived counit computation uses the existing K-flat computation
property on representatives, and component equations identify its model maps.
No source-library declaration is edited and no target meaning changes.

## Old

The following public declarations lived in Sheaf.Paper.CompletedPullbackReduction.
Their original signatures below are copied verbatim. All retain their signatures
except completedReductionCompositeCounitNat, whose generalized signature appears
below under New. completedReductionPulledModelMap is rebuilt from the native
counits with the same component formula; the two derived normalization predicates are repackaged with exactly their
original component equations, as detailed below. Other public non-theorem data
bodies are retained.

```lean
def completedPullbackFunctor :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d))

theorem completedReductionModelPushforward_isRightAdjoint
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (@SheafOfModules.pushforward.{u + 1} _ _ _ _ _ _ _ _ _
      (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)).IsRightAdjoint

def completedReductionInverseImageGenerator
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (M : pbcModules Y R)
    (V : Y.ProEt) (U : X.ProEt) (f : U ⟶ (proEtaleBaseChange g).obj V)
    (m : M.val.obj (op V)) :
    ((proEtaleModuleInverseImage g R).obj M).val.obj (op U)

def completedReductionRestrictionFactors (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedRestrict φ ≅
      (pbcRestrict φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

abbrev completedReductionFiniteModules (n : ℕ)

abbrev completedReductionFiniteDerived (n : ℕ)

def completedReductionFiniteTarget (n : ℕ) :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (reductionCoefficient X d n))

def completedReductionFiniteTensor (n : ℕ)
    (M : pbcModules Y (reductionCoefficient Y d n))
    (U : X.ProEtᵒᵖ) (s : (reductionCoefficient X d n).obj.obj U)
    (m : ((proEtaleModuleInverseImage g
      (reductionCoefficient Y d n)).obj M).val.obj U) :
    ((completedReductionFiniteModules g d n).obj M).val.obj U

def completedReductionFiniteGenerator (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (proEtaleBaseChange g).obj V)
    (s : (reductionCoefficient X d n).obj.obj (op U))
    (z : (reductionCoefficient Y d n).obj.obj (op V)) (m : M.val.obj (op V)) :
    ((completedReductionFiniteModules g d n).obj
      ((reductionChange Y (completedReductionProjection Y d n)).obj M)).val.obj (op U)

instance completedReductionOrdinarySource_preservesZero (n : ℕ) :
    (completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).PreservesZeroMorphisms

def completedReductionLimitProjection (n : ℕ) :
    completedTowerRlim d X ⟶ pbcTowerEvaluation X (pbcAdicCompletion X d) n

def completedReductionQuotientAssoc (T : Scheme.{u}) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c)
    (M : DerivedCategory (pbcModules T (reductionCoefficient T d c)))

def completedPullbackSourceNormalization (T : Scheme.{u}) (a b : ℕ) (h : a ≤ b)
    (M : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))

def completedReductionSectionEquation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M : pbcModules T R} {N : pbcModules T S}
    (ν : M ⟶ (pbcRestrict φ).obj N) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : Prop

def HasCompletedReductionOrdinaryComparisonNormalization (n : ℕ)
    (e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n))) : Prop

theorem completedReductionOrdinaryComparison_exists (n : ℕ) :
    ∃! e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n)),
      HasCompletedReductionOrdinaryComparisonNormalization g d n e

def completedReductionOrdinaryComparison (n : ℕ) :
    completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n))

def completedReductionCompositeCounitNat
    {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E]
    (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LF : DerivedCategory B ⥤ DerivedCategory C)
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (εF : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ (LF ⋙ LG ⋙ H.mapDerivedCategory) ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙
        H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

def completedReductionPulledModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj
      ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj
        (DerivedCategory.Q.obj P))) ⟶
    DerivedCategory.Q.obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
            (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex
              (.up ℤ)).obj P)))

def completedReductionFiniteModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)

def HasCompletedReductionFiniteEvaluationNormalization (n : ℕ)
    (e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n)) : Prop

theorem completedReductionFiniteEvaluation_exists (n : ℕ) :
    ∃! e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n),
      HasCompletedReductionFiniteEvaluationNormalization g d n e

def completedReductionFiniteEvaluation (n : ℕ) :
    completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n)

def completedPullbackReductionArrow
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (n : ℕ) :
    (reductionDerivedChange X (completedReductionProjection X d n)).obj
        (completedPullbackObject g d K) ⟶ (completedReductionFiniteTarget g d n).obj K

def HasCompletedReductionOrdinaryTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h))) : Prop

theorem completedReductionOrdinaryTransition_exists (a b : ℕ) (h : a ≤ b) :
    ∃! τ : reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h)),
      HasCompletedReductionOrdinaryTransitionNormalization g d a b h τ

def completedReductionOrdinaryTransition (a b : ℕ) (h : a ≤ b) :
    reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h))

def HasCompletedReductionTargetTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h)) : Prop

theorem completedReductionTargetTransition_exists (a b : ℕ) (h : a ≤ b) :
    ∃! τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h),
      HasCompletedReductionTargetTransitionNormalization g d a b h τ

def completedReductionTargetTransition (a b : ℕ) (h : a ≤ b) :
    completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h)

def completedReductionTargetNormalization
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (a b : ℕ) (h : a ≤ b)

theorem completedReductionOrdinaryRestrictionUnit_exists (T : Scheme.{u}) (a : ℕ) :
    ∃! e : SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget T).map (reductionCoefficientMap T d a a (le_refl a))) ≅ 𝟭 _,
      ∀ (M : pbcModules T (reductionCoefficient T d a))
        (U : T.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x

def completedReductionRestrictionUnit (T : Scheme.{u}) (a : ℕ) :
    pbcDerivedRestrict (reductionCoefficientMap T d a a (le_refl a)) ≅ 𝟭 _

def completedReductionUnit (T : Scheme.{u}) (a : ℕ)
    (M : DerivedCategory
      (pbcModules T (reductionCoefficient T d a)))
```

The lower modules imported the parent:

```lean
public import Sheaf.Paper.CompletedPullbackReduction
```

CompletedReductionFiniteEvaluationNormalization additionally used
`import all Sheaf.Paper.CompletedPullbackReduction` for its private normalization API.

## New

All signatures above except the generic composite-counit helper are unchanged,
in Sheaf.Paper.CompletedPullbackReductionData. The original parent now says:

```lean
public import Sheaf.Paper.CompletedPullbackReductionData
```

The parent also keeps a private copy of `projection_surjective` (same statement and
proof as the moved private lemma in Data): Sheaf.Paper.IntegralAugmentedQuotientTowers
(unclaimed) reads it through `import all Sheaf.Paper.CompletedPullbackReduction` and
failed with `Unknown identifier projection_surjective` once the lemma lived only in
Data (reviewer correction, 2026-10-26).

The three adapted lower consumers import that same data module; the normalization
consumer's `import all` is redirected to the data module as well. The parent theorem
has its original signature, and its completed proof uses a single strictly smaller
finite-arrow invertibility lemma and the proved conditional coherence theorem.

The existing ordinary-comparison, derived-transition and finite-interface DAG
attachments now name the data module. A definition node records the formerly
bundled completedPullbackFunctor and remaining auxiliary declarations. No old
mathematical statement or statement dependency changes.

The original repository had no external users of the generalized helper. This
packet uses it in Data for model maps and their naturality package, and in the
compatibility consumer's proved private component formula.
Its new signature, and the three new proved constructions, are:

```lean
def completedReductionCompositeCounitNat
    {B C D E B' C' D' E' : Type*}
    [Category* B] [Category* C] [Category* D] [Category* E]
    [Category* B'] [Category* C'] [Category* D'] [Category* E']
    (QB : B ⥤ B') (QC : C ⥤ C') (QD : D ⥤ D') (QE : E ⥤ E')
    (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
    (LF : B' ⥤ C') (LG : C' ⥤ D') (LH : D' ⥤ E')
    (α : QB ⋙ LF ⟶ F ⋙ QC) (β : QC ⋙ LG ⟶ G ⋙ QD)
    (γ : QD ⋙ LH ≅ H ⋙ QE) :
    QB ⋙ (LF ⋙ LG ⋙ LH) ⟶ F ⋙ G ⋙ H ⋙ QE

def completedReductionTowerComplexNat (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ completedReductionTower T d ⟶
      completedReductionComplexTowerFunctor T d ⋙ DerivedCategory.Q

def completedReductionComplexCounitNat
    {B D : Type*} [Category* B] [Abelian B] [Category* D] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (F : B ⥤ D) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

def completedReductionPullbackComplexNat :
    DerivedCategory.Q ⋙ completedTowerPullback g d ⟶
      (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q

```

The native first component is completedReductionTowerComplexCounit. Unfolding
it and reductionComplexCounit gives the original Functor.leftDerivedCounitOnComplex
formula; coherenceReductionTowerCounit and completedReductionTowerCounit choose
the same counit from completedReductionTower_exists. The native second component
is completedTowerPullbackComplexCounit, whose definition is the original second
Functor.leftDerivedCounitOnComplex. The generic constructor's component is
LH.map (LG.map (α.app P) ≫ β.app (F.obj P)) ≫ γ.hom.app ((F ⋙ G).obj P).
Thus the published model map still consists of the same two universal counits,
followed by the same exact evaluation comparison. No coefficient object, limit projection, scalar action or normalization equation
is changed. The two derived normalization predicate bodies now instantiate the
generic predicates below; their public signatures stay unchanged.

The new helpers are recorded as auxiliary declarations of
 def-weil-pbc-completed-pullback-reduction-functor. No additional proof hole is added.

The two model natural transformations and generic normalization predicates are
also now public. Their declarations are recorded below. For the finite model,
the component of the composite is the unchanged completedReductionFiniteModelMap;
Functor.leftDerivedCounitOnComplex expands to the same four factors as
pbcComplexCounit. For the pulled model it is the unchanged
completedReductionPulledModelMap. Thus instantiating the generic predicates
unfolds to precisely the old predicates, including the same universal quantifier
over K-flat independent-coefficient complexes.

```lean
def completedReductionFiniteModelNat (n : ℕ) :
    DerivedCategory.Q ⋙ completedReductionFiniteTarget g d n ⟶
      (reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex (.up ℤ) ⋙
        (completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q :=
  Functor.whiskerRight
    (completedReductionComplexCounitNat (pbcExtend (completedReductionProjection Y d n))
      (pbcDerivedExtend (completedReductionProjection Y d n))
      (pbcExtensionCounit (completedReductionProjection Y d n)))
    (completedReductionFiniteDerived g d n) ≫
      Functor.whiskerLeft
        ((reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex
          (.up ℤ))
        (completedReductionFiniteModules g d n).mapDerivedCategoryFactors.hom

def completedReductionPulledModelNat (n : ℕ) :=
  letI := completedReductionModuleTowerFunctor_additive Y d
  letI := completedTowerModulePullback_additive g d
  (completedReductionCompositeCounitNat
    _ _ _ _ _ _ _
    (completedReductionTower Y d) (completedTowerPullback g d)
    (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op n)).mapDerivedCategory)
    (completedReductionTowerComplexNat d Y)
    (completedReductionPullbackComplexNat g d)
    (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op n)).mapDerivedCategoryFactors))

def completedReductionComparisonNormalized
    {B C D E C' D' : Type*}
    [Category* B] [Category* C] [Category* D] [Category* E]
    [Category* C'] [Category* D']
    [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian C'] [Abelian D']
    [HasDerivedCategory B] [HasDerivedCategory E] [HasDerivedCategory D']
    (good : CochainComplex B ℤ → Prop)
    (F : B ⥤ C) (G : C ⥤ D) (T : D ⥤ E)
    (F' : B ⥤ C') (G' : C' ⥤ D') (R : D' ⥤ E)
    [F.Additive] [G.Additive] [T.Additive] [F'.Additive] [G'.Additive] [R.Additive]
    (H : DerivedCategory B ⥤ DerivedCategory E)
    (J : DerivedCategory B ⥤ DerivedCategory D')
    (S : DerivedCategory D' ⥤ DerivedCategory E)
    (α : DerivedCategory.Q ⋙ H ⟶ F.mapHomologicalComplex (.up ℤ) ⋙
      G.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (γ : DerivedCategory.Q ⋙ J ⟶
      F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ S ≅ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (t : F ⋙ G ⋙ T ≅ F' ⋙ G' ⋙ R)
    (e : H ≅ J ⋙ S) : Prop :=
  ∀ P, good P →
      α.app P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫ S.map (γ.app P) ≫
          δ.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj
            ((F'.mapHomologicalComplex (.up ℤ)).obj P))

def completedReductionTransitionNormalized
    {B C C' D' D : Type*}
    [Category* B] [Category* C] [Category* C'] [Category* D'] [Category* D]
    [Abelian B] [Abelian C] [Abelian C'] [Abelian D'] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D'] [HasDerivedCategory D]
    (good : CochainComplex B ℤ → Prop)
    (F : B ⥤ C) (G : C ⥤ D) (F' : B ⥤ C') (G' : C' ⥤ D') (R : D' ⥤ D)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] [R.Additive]
    (H : DerivedCategory B ⥤ DerivedCategory D)
    (J : DerivedCategory B ⥤ DerivedCategory D')
    (S : DerivedCategory D' ⥤ DerivedCategory D)
    (α : DerivedCategory.Q ⋙ H ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (γ : DerivedCategory.Q ⋙ J ⟶
      F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ S ≅ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (t : F ⋙ G ⟶ F' ⋙ G' ⋙ R)
    (τ : H ⟶ J ⋙ S) : Prop :=
  ∀ P, good P →
      α.app P ≫ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P) =
        τ.app (DerivedCategory.Q.obj P) ≫ S.map (γ.app P) ≫
          δ.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj
            ((F'.mapHomologicalComplex (.up ℤ)).obj P))
```

Original normalization definitions (verbatim):

```lean
def HasCompletedReductionFiniteEvaluationNormalization (n : ℕ)
    (e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n)) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        completedReductionPulledModelMap g d n P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (completedReductionOrdinaryComparison g d n).hom (.up ℤ)).app P) =
          e.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (completedReductionProjection X d n)).map
              (completedReductionFiniteModelMap g d n P) ≫
            (completedReductionRestrictionFactors X (completedReductionProjection X d n)).hom.app
                (((completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ)).obj
                  (((reductionChange Y
                    (completedReductionProjection Y d n)).mapHomologicalComplex
                      (.up ℤ)).obj P))

def HasCompletedReductionTargetTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h)) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        completedReductionFiniteModelMap g d b P ≫ DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (completedReductionOrdinaryTransition g d a b h) (.up ℤ)).app P) =
          τ.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedReductionFiniteModelMap g d a P) ≫
            (completedReductionRestrictionFactors X
              (reductionCoefficientMap X d b a h)).hom.app
                  (((completedReductionFiniteModules g d a).mapHomologicalComplex (.up ℤ)).obj
                    (((reductionChange Y
                      (completedReductionProjection Y d a)).mapHomologicalComplex
                        (.up ℤ)).obj P))
```

Repackaged normalization definitions (verbatim):

```lean
def HasCompletedReductionFiniteEvaluationNormalization (n : ℕ)
    (e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n)) : Prop :=
  letI := completedReductionModuleTowerFunctor_additive Y d
  letI := completedTowerModulePullback_additive g d
  completedReductionComparisonNormalized
    (fun P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ ↦
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P)
    (completedReductionModuleTowerFunctor Y d) (completedTowerModulePullback g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
    (reductionChange Y (completedReductionProjection Y d n))
    (completedReductionFiniteModules g d n)
    (pbcRestrict (completedReductionProjection X d n)) _ _ _
    (completedReductionPulledModelNat g d n) (completedReductionFiniteModelNat g d n)
    (completedReductionRestrictionFactors X (completedReductionProjection X d n))
    (completedReductionOrdinaryComparison g d n) e

def HasCompletedReductionTargetTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h)) : Prop :=
  completedReductionTransitionNormalized
    (fun P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ ↦
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P)
    (reductionChange Y (completedReductionProjection Y d b))
    (completedReductionFiniteModules g d b)
    (reductionChange Y (completedReductionProjection Y d a))
    (completedReductionFiniteModules g d a)
    (pbcRestrict (reductionCoefficientMap X d b a h))
    (completedReductionFiniteTarget g d b) (completedReductionFiniteTarget g d a)
    (pbcDerivedRestrict (reductionCoefficientMap X d b a h))
    (completedReductionFiniteModelNat g d b) (completedReductionFiniteModelNat g d a)
    (completedReductionRestrictionFactors X (reductionCoefficientMap X d b a h))
    (completedReductionOrdinaryTransition g d a b h) τ
```

The extracted declarations retain the original source module's instance choices.
The compatibility consumer has three proved private component lemmas. They identify
natural-transformation components with the unchanged model maps, and compute the
generic composite by its displayed whiskering formula. Its transition proof uses
the native completedReductionTowerComplexCounit component directly. Its main square uses the native model natural transformations directly, so the
normalization hypotheses apply without rewriting their universally quantified
equations. These proof changes avoid unfolding all derived data.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPullbackReductionData | K7 (new) | Contains the moved interface and its new native naturality packages. |
| Sheaf.Paper.CompletedPullbackReductionCoherence | K7 (new) | Uses the moved finite interfaces in the proved coherence step. |
| Sheaf.Paper.CompletedPullbackReductionArrowIsIso | K7 (new) | States the remaining finite-arrow invertibility clause using Data. |
| Sheaf.Paper.CompletedPullbackReduction | K7 | Publicly re-export Data; prove the original parent theorem. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.CompletedPullbackUniverseTransportData | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.CompletedReductionFiniteEvaluationNormalization | unclaimed | Import the extracted data module; all signatures and proofs are retained. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.FiniteQuotientOrdinaryComparison | unclaimed | Import the extracted data module; all signatures and proofs are retained. |
| Sheaf.Paper.FiniteQuotientTransitionCompatibility | unclaimed | Import Data; use native model transformations, proved component lemmas, and native counits in the transition proof; signatures unchanged. |
| Sheaf.Paper.IntegralPullbackCompletedComparisonData | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.IntegralPullbackShiftCoordinates | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.IntegralStratumChartRestrictionsData | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.IntegralStratumChartRestrictions | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Unchanged: original parent publicly re-exports the identical declarations. |

Any target whose statement uses an affected definition must be reviewed again
under the stage-2 semantic review rule. This packet preserves the concrete
coefficient objects, specified arrows and normalization equations.

## Status

landed 20261026T070212-L-3457743 2026-10-26 (merge of deliver/K7/Sheaf.Paper.CompletedPullbackReduction)
