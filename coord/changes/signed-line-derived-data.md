# SignedLineDerivedBaseChange interface relocation and constraint API

## Reason

The proof needs its statement data in modules that it imports. Move the existing data to SignedLineDerivedBaseChangeData, keeping fully qualified names and the public re-export. Pin derived-tensor universe arguments to the existing module universe, and name the termwise tensor functor complexLine. DerivedActionData has named fst and snd projections for exactly the same nested-product comparison data. OrdinaryLineConstraints factors the three original pure-section formulas. DerivedActionSquare and DerivedActionUnique factor the existing action clauses without changing their formulas.

The original normalization predicates repeatedly unfold the sheaf tensor and its additive instances when checking dependent witnesses. LocalizedLineConstraints and LocalizedLineFamily now state those same localization equations for arbitrary categories, with the ordinary and derived constraint predicates as parameters. DerivedLineConstraints and DerivedFamilyCoherence specialize these one-constructor propositions to the same sheaf-module functors. Constructor application and elimination give both directions of the previous existence/conjunction predicates. All ordinary witnesses, all six normalization equations, both site constraints and all three derived coherence equations are retained. The generic constructor proofs are checked before specialization, avoiding repeated reduction of large tensor constructions. No target signature or mathematical hypothesis is changed.

## Old

```lean
/-- The existing module pullback; its unit is insertion into the sheafified relative tensor.
Source: Stacks 03D7 and 03EL (blueprint: lem-pur-signed-line-derived-base-change). -/
abbrev pull
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
  ringedSitePullbackFunctor a (module_pushforward_isRightAdjoint_of_universes a)

/-- Signed functoriality in a line isomorphism, using the recorded powers and internal Hom.
The negative map is precomposition with the inverse positive map.
Source: Stacks 03EL, 0GMX (blueprint: lem-pur-signed-line-derived-base-change). -/
def signedIsoHom {A : Sheaf J CommRingCat.{max u v w}}
    {P Q : KFlatFixedTensor.Modules A} (b : P ≅ Q) :
    ∀ d : ℤ, signedLinePower.{u, v, w} P d ⟶ signedLinePower.{u, v, w} Q d
  | .ofNat n => scalarTensorPowerMap A b.hom n
  | .negSucc n => homObjMap (scalarTensorPowerMap A b.inv (n + 1)) (𝟙 (unit _))

/-- The published derived tensor with the line in degree zero.
Source: Stacks 06YU (blueprint: lem-pur-signed-line-derived-base-change). -/
def derivedLine (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A) :
    DerivedCategory (KFlatFixedTensor.Modules A) ⥤ DerivedCategory (KFlatFixedTensor.Modules A) :=
  (KFlatFixedTensor.derivedTensor A).flip.obj
    (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))

attribute [local irreducible] derivedLine Functor.mapDerivedCategory

/-- The actual total-complex collapse, followed by the existing comparison with site tensor.
Source: Stacks 06YU (blueprint: lem-pur-signed-line-derived-base-change). -/
def collapse (A : Sheaf J CommRingCat.{max u v w})
    (L : KFlatFixedTensor.Modules A) :
    (KFlatFixedTensor.totalTensor A).flip.obj
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L) ≅
      (siteSheafTensorRight (A := A) L).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (KFlatFixedTensor.ordinaryTensor A) L ≪≫
    NatIso.mapHomologicalComplex ((siteSheafTensorRightIso A L).symm) (.up ℤ)

/-- Agreement with the actual K-flat total-tensor comparison on resolving complexes.
Source: Stacks 06YU (blueprint: lem-pur-signed-line-derived-base-change). -/
def ResolvingNormalization (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))
    (hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A)
      (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L).X i))
    (c : DerivedCategory.Q ⋙ derivedLine A L ≅
      (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : Prop :=
  ∀ (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ)
    (hE : CochainComplex.IsKFlatIndependentCoefficients E)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A) (E.X i)),
    HEq (c.hom.app E ≫ DerivedCategory.Q.map ((collapse A L).inv.app E))
      (KFlatFixedTensor.representativeIso A E
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L)
          hE hL hf hLf).inv

/-- The two localization comparisons and the derived action isomorphism, as ordinary
product data. Their canonicity is specified by DerivedAction, never chosen from existence.
Source: Stacks 06YU, 07A4 (blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedActionData
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S) :=
  (DerivedCategory.Q ⋙ derivedLine R L ≅
    (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ×
  (DerivedCategory.Q ⋙ derivedLine S M ≅
    (siteSheafTensorRight M).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ×
  (derivedLine R L ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ derivedLine S M)

/-- A derived action pinned on every complex by the ordinary tensor comparison.
The resolving comparisons are the published ones, including their collapse to one-term
line factors. Source: Stacks 06YU, 07A4 and 015F
(blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedAction
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData F L M) : Prop :=
  ∃ hL : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L),
  ∃ hM : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M),
  ∃ hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L).X i),
  ∃ hMf : ∀ i : ℤ, IsFlatOnSite (J := K) (R := S)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M).X i),
    ResolvingNormalization R L hL hLf b.1 ∧
    ResolvingNormalization S M hM hMf b.2.1 ∧
    (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
      HEq (b.2.2.hom.app (DerivedCategory.Q.obj E) ≫
          (derivedLine S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
          b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
        (F.mapDerivedCategory.map (b.1.hom.app E) ≫
          F.mapDerivedCategoryFactors.hom.app
            (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))) ∧
    (∀ η : derivedLine R L ⋙ F.mapDerivedCategory ≅
        F.mapDerivedCategory ⋙ derivedLine S M,
      (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
        HEq (η.hom.app (DerivedCategory.Q.obj E) ≫
            (derivedLine S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
            b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
          (F.mapDerivedCategory.map (b.1.hom.app E) ≫
            F.mapDerivedCategoryFactors.hom.app
              (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))) →
        η = b.2.2)

/-- Right unit, positive-power associator and negative-positive evaluation constraints.
The ordinary constraints are specified on all local pure tensors. The derived constraints
are specified after localization using c; c itself is fixed by representativeIso and
collapse in DerivedAction. Thus these are the canonical constraints, with no arbitrary
monoidal structure or map selected. The positive constraint is the associator followed
by the one-term identification of the next power, and evaluation contracts the last two
factors. Source: Stacks 03EK, 04TT, 06YU and 07A4
(blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedLineConstraints (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (P : KFlatFixedTensor.Modules A)
    (c : ∀ d : ℤ, DerivedCategory.Q ⋙ derivedLine A (signedLinePower.{u, v, w} P d) ≅
      (siteSheafTensorRight (signedLinePower.{u, v, w} P d)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
    (rightUnitor : derivedLine A (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (product : ∀ n : ℕ,
      derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
          derivedLine A (signedLinePower.{u, v, w} P 1) ≅
        derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (evaluation : ∀ n : ℕ,
      derivedLine A (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _) : Prop :=
  ∃ ordinaryUnit : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _,
  ∃ ordinaryProduct : ∀ n : ℕ,
    siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))),
  ∃ ordinaryEvaluation : ∀ n : ℕ,
    siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _,
    (∀ (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (r : A.obj.obj V),
      (ordinaryUnit.hom.app N).val.app V
        (siteSheafTensorTmul N (signedLinePower.{u, v, w} P 0) V x r) =
          @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
            (N.val.obj V) inferInstance r x) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (y : (scalarTensorPower A P (n + 1)).val.obj V)
      (q : P.val.obj V),
      ((ordinaryProduct n).hom.app N).val.app V
        (siteSheafTensorTmul _ P V
          (siteSheafTensorTmul N (scalarTensorPower A P (n + 1)) V x y) q) =
        siteSheafTensorTmul N (scalarTensorPower A P (n + 2)) V x
          (siteSheafTensorTmul (scalarTensorPower A P (n + 1)) P V y q)) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (φ : (signedLinePower.{u, v, w} P (.negSucc n)).val.obj V)
      (y : (scalarTensorPower A P (n + 1)).val.obj V),
      ((ordinaryEvaluation n).app N).val.app V
        (siteSheafTensorTmul _ (scalarTensorPower A P (n + 1)) V
          (siteSheafTensorTmul N (signedLinePower.{u, v, w} P (.negSucc n)) V x φ) y) =
        @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
          (N.val.obj V) inferInstance (φ.app (op (Over.mk (𝟙 V.unop))) y) x) ∧
    (∀ E : CochainComplex (KFlatFixedTensor.Modules A) ℤ,
      HEq (rightUnitor.hom.app (DerivedCategory.Q.obj E))
        ((c 0).hom.app E ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinaryUnit (.up ℤ)).hom.app E))) ∧
    (∀ (n : ℕ) (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ),
      HEq ((product n).hom.app (DerivedCategory.Q.obj E) ≫
          (c (.ofNat (n + 2))).hom.app E)
        ((derivedLine A (signedLinePower.{u, v, w} P 1)).map
            ((c (.ofNat (n + 1))).hom.app E) ≫
          (c 1).hom.app
            ((Functor.mapHomologicalComplex
              (siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))))
                (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (ordinaryProduct n) (.up ℤ)).hom.app E))) ∧
    (∀ (n : ℕ) (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ),
      HEq ((evaluation n).app (DerivedCategory.Q.obj E))
        ((derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).map
            ((c (.negSucc n)).hom.app E) ≫
          (c (.ofNat (n + 1))).hom.app
            ((Functor.mapHomologicalComplex
              (siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)))
                (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (ordinaryEvaluation n) (.up ℤ)).app E)))

/-- The simultaneous unit, positive-power and evaluation equations for the same eta family
whose components are fixed in DerivedAction. Source: Stacks 07A4; blueprint Powers and duals
(blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedFamilyCoherence
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
    (b : ∀ d : ℤ, DerivedActionData F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d)) : Prop :=
  ∃ unitR : derivedLine R (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _,
  ∃ unitS : derivedLine S (signedLinePower.{u, v, w} Q 0) ≅ 𝟭 _,
  ∃ productR : ∀ n : ℕ,
    derivedLine R (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        derivedLine R (signedLinePower.{u, v, w} P 1) ≅
      derivedLine R (signedLinePower.{u, v, w} P (.ofNat (n + 2))),
  ∃ productS : ∀ n : ℕ,
    derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⋙
        derivedLine S (signedLinePower.{u, v, w} Q 1) ≅
      derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 2))),
  ∃ evaluationR : ∀ n : ℕ,
    derivedLine R (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
      derivedLine R (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _,
  ∃ evaluationS : ∀ n : ℕ,
    derivedLine S (signedLinePower.{u, v, w} Q (.negSucc n)) ⋙
      derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⟶ 𝟭 _,
    DerivedLineConstraints R P (fun d ↦ (b d).1) unitR productR evaluationR ∧
    DerivedLineConstraints S Q (fun d ↦ (b d).2.1) unitS productS evaluationS ∧
    (∀ X : DerivedCategory (KFlatFixedTensor.Modules R),
      (b 0).2.2.hom.app X ≫ unitS.hom.app (F.mapDerivedCategory.obj X) =
        F.mapDerivedCategory.map (unitR.hom.app X)) ∧
    (∀ (n : ℕ) (X : DerivedCategory (KFlatFixedTensor.Modules R)),
      F.mapDerivedCategory.map ((productR n).hom.app X) ≫
          (b (.ofNat (n + 2))).2.2.hom.app X =
        (b 1).2.2.hom.app ((derivedLine R
            (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).obj X) ≫
          (derivedLine S (signedLinePower.{u, v, w} Q 1)).map
            ((b (.ofNat (n + 1))).2.2.hom.app X) ≫
          (productS n).hom.app (F.mapDerivedCategory.obj X)) ∧
    (∀ (n : ℕ) (X : DerivedCategory (KFlatFixedTensor.Modules R)),
      F.mapDerivedCategory.map ((evaluationR n).app X) =
        (b (.ofNat (n + 1))).2.2.hom.app
            ((derivedLine R (signedLinePower.{u, v, w} P (.negSucc n))).obj X) ≫
          (derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 1)))).map
            ((b (.negSucc n)).2.2.hom.app X) ≫
          (evaluationS n).app (F.mapDerivedCategory.obj X))

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

/-- Naturality in isomorphisms of the two line data. Negative powers use inverse dual maps.
Source: Stacks 03EL, 0GMX (blueprint: lem-pur-signed-line-derived-base-change). -/
def IsoNaturality
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (P' : KFlatFixedTensor.Modules R) (Q' : KFlatFixedTensor.Modules S)
    (b : P ≅ P') (c : Q ≅ Q') (t' : (pull a).obj P' ≅ Q')
    (T' : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P' d) ≅
      signedLinePower.{u, v, w} Q' d),
    (pull a).map b.hom ≫ t'.hom = t.hom ≫ c.hom →
    SignedLinePullbackNormalized a P' Q' t' T' →
    ∀ d : ℤ, (pull a).map (signedIsoHom b d) ≫ (T' d).hom =
      (T d).hom ≫ signedIsoHom c d

/-- Naturality in arbitrary coefficient extensions compatible with the structural isomorphism.
The existing scalar-power identifications and scalar/pullback square specify the canonical
balanced-tensor comparison; no arbitrary comparison is assumed. Degree-one compatibility
is exactly the assertion that t' is induced from t. No flatness of either ring map occurs.
Source: Stacks 03EL, 0GMX, 0FNY
(blueprint: lem-pur-signed-line-derived-base-change). -/
def ScalarNaturality
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (R' : Sheaf J CommRingCat.{max u v w})
    (S' : Sheaf K CommRingCat.{max u v w}) (α : R ⟶ R') (β : S ⟶ S')
    (a' : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R' ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S')),
    IsIso ((rAdj.homEquiv _ _).symm a') →
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α ≫ a' =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map β) →
    ∀ (t' : (pull a').obj (changeOfRingsOfUniverses α P) ≅ changeOfRingsOfUniverses β Q)
      (T' : ∀ d : ℤ,
        (pull a').obj (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d) ≅
          signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
      (B : ∀ d : ℤ, changeOfRingsOfUniverses α (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
      (E : ∀ d : ℤ, changeOfRingsOfUniverses β (signedLinePower.{u, v, w} Q d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d),
      SignedLinePullbackNormalized a' _ _ t' T' →
      SignedLineComparisonNormalized α P _ (Iso.refl _) B →
      SignedLineComparisonNormalized β Q _ (Iso.refl _) E →
      SignedLineScalarPullbackSquare α β a a' P _ Q _
        (Iso.refl _) (Iso.refl _) t t' →
      ∀ d : ℤ, SignedLineScalarPullbackSquare α β a a'
        (signedLinePower.{u, v, w} P d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
        (signedLinePower.{u, v, w} Q d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
        (B d) (E d) (T d) (T' d)
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SignedLineScalarPullbackSquare
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Sites.Pullback

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

public import Sheaf.CategoryTheory.RingedToposMorphism

public import Sheaf.CategoryTheory.RingedSiteModules

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Signed line comparisons on unbounded derived categories

Source: Stacks Project, Tags 03EL, 0GMX, 0FNY and 07A4; the current blueprint,
Powers and duals in det-prop-sfb-cartesian-coefficients-twists.
(blueprint: def-pur-signed-line-derived-action-data)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option Elab.async false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace SheafOfModules.SignedLineDerivedBaseChange

attribute [local irreducible] siteDerivedTensorIndependentCoefficients
  KFlatFixedTensor.representativeIso siteSheafTensorRight
  siteSheafTensorSecondMap siteSheafTensorTmul
  monoidalCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] KFlatFixedTensor.derivedTensor
  KFlatFixedTensor.selectedTensorPresentation
  KFlatFixedTensor.selectedResolvingTensorPresentation

attribute [local instance 2000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

/-- The existing module pullback; its unit is insertion into the sheafified relative tensor.
Source: Stacks 03D7 and 03EL (blueprint: def-pur-signed-line-derived-action-data). -/
abbrev pull
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
  ringedSitePullbackFunctor a (module_pushforward_isRightAdjoint_of_universes a)

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint

/-- Signed functoriality in a line isomorphism, using the recorded powers and internal Hom.
The negative map is precomposition with the inverse positive map.
Source: Stacks 03EL, 0GMX (blueprint: def-pur-signed-line-derived-action-data). -/
def signedIsoHom {A : Sheaf J CommRingCat.{max u v w}}
    {P Q : KFlatFixedTensor.Modules A} (b : P ≅ Q) :
    ∀ d : ℤ, signedLinePower.{u, v, w} P d ⟶ signedLinePower.{u, v, w} Q d
  | .ofNat n => scalarTensorPowerMap A b.hom n
  | .negSucc n => homObjMap (scalarTensorPowerMap A b.inv (n + 1)) (𝟙 (unit _))

/-- The published derived tensor with the line in degree zero.
Source: Stacks 06YU (blueprint: def-pur-signed-line-derived-action-data). -/
def derivedLine (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A) :
    DerivedCategory (KFlatFixedTensor.Modules A) ⥤ DerivedCategory (KFlatFixedTensor.Modules A) :=
  (KFlatFixedTensor.derivedTensor.{u, v, max u v w, z} A).flip.obj
    (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))

attribute [local irreducible] derivedLine Functor.mapDerivedCategory

/-- Termwise tensor with a fixed sheaf, with its zero-preservation instance fixed once.
Source: Stacks 03EK and 06YU
(blueprint: def-pur-signed-line-derived-action-data). -/
def complexLine (A : Sheaf J CommRingCat.{max u v w})
    (L : KFlatFixedTensor.Modules A) :
    CochainComplex (KFlatFixedTensor.Modules A) ℤ ⥤
      CochainComplex (KFlatFixedTensor.Modules A) ℤ :=
  (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)

/-- The actual total-complex collapse, followed by the existing comparison with site tensor.
Source: Stacks 06YU (blueprint: def-pur-signed-line-derived-action-data). -/
def collapse (A : Sheaf J CommRingCat.{max u v w})
    (L : KFlatFixedTensor.Modules A) :
    (KFlatFixedTensor.totalTensor A).flip.obj
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L) ≅
      (siteSheafTensorRight (A := A) L).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (KFlatFixedTensor.ordinaryTensor A) L ≪≫
    NatIso.mapHomologicalComplex ((siteSheafTensorRightIso A L).symm) (.up ℤ)

attribute [local irreducible] collapse

/-- Agreement with the actual K-flat total-tensor comparison on resolving complexes.
Source: Stacks 06YU (blueprint: def-pur-signed-line-derived-action-data). -/
def ResolvingNormalization (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))
    (hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A)
      (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L).X i))
    (c : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} A L ≅
      (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : Prop :=
  ∀ (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ)
    (hE : CochainComplex.IsKFlatIndependentCoefficients E)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A) (E.X i)),
    HEq (c.hom.app E ≫ DerivedCategory.Q.map ((collapse A L).inv.app E))
      (KFlatFixedTensor.representativeIso A E
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L)
          hE hL hf hLf).inv

attribute [local irreducible] ResolvingNormalization

/-- The two localization comparisons and the derived action isomorphism, as ordinary
product data. Their canonicity is specified by DerivedAction, never chosen from existence.
Source: Stacks 06YU, 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
structure DerivedActionData
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S) where
  fst : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} R L ≅
    (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  snd : (DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} S M ≅
    (siteSheafTensorRight M).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ×
    (derivedLine.{u, v, w, z} R L ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ derivedLine.{u, v, w, z} S M)

/-- The termwise square required of a derived action.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedActionSquare
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData.{u, v, w, z} F L M) : Prop :=
  ∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
    HEq (b.2.2.hom.app (DerivedCategory.Q.obj E) ≫
      (derivedLine.{u, v, w, z} S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
      b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
      (F.mapDerivedCategory.map (b.1.hom.app E) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))

/-- The uniqueness clause for a derived action, with the same displayed type.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedActionUnique
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData.{u, v, w, z} F L M) : Prop :=
  ∀ η : derivedLine.{u, v, w, z} R L ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ derivedLine.{u, v, w, z} S M,
    (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
      HEq (η.hom.app (DerivedCategory.Q.obj E) ≫
          (derivedLine.{u, v, w, z} S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
          b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
        (F.mapDerivedCategory.map (b.1.hom.app E) ≫
          F.mapDerivedCategoryFactors.hom.app
            (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))) →
        η = b.2.2

/-- A derived action pinned on every complex by the ordinary tensor comparison.
The resolving comparisons are the published ones, including their collapse to one-term
line factors. Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedAction
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData F L M) : Prop :=
  ∃ hL : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L),
  ∃ hM : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M),
  ∃ hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L).X i),
  ∃ hMf : ∀ i : ℤ, IsFlatOnSite (J := K) (R := S)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M).X i),
    ResolvingNormalization R L hL hLf b.1 ∧
    ResolvingNormalization S M hM hMf b.2.1 ∧
    DerivedActionSquare F L M γ b ∧
    DerivedActionUnique F L M γ b

attribute [local irreducible] DerivedAction

/-- Canonical ordinary unit, positive associators and evaluations of signed powers.
Source: Stacks 03EL and 0FNY.
(blueprint: def-pur-signed-line-ordinary-constraint-data). -/
def OrdinaryLineConstraints (A : Sheaf J CommRingCat.{max u v w})
    (P : KFlatFixedTensor.Modules A)
    (ordinaryUnit : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (ordinaryProduct : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (ordinaryEvaluation : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _) : Prop :=
    (∀ (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (r : A.obj.obj V),
      (ordinaryUnit.hom.app N).val.app V
        (siteSheafTensorTmul N (signedLinePower.{u, v, w} P 0) V x r) =
          @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
            (N.val.obj V) inferInstance r x) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (y : (scalarTensorPower A P (n + 1)).val.obj V)
      (q : P.val.obj V),
      ((ordinaryProduct n).hom.app N).val.app V
        (siteSheafTensorTmul _ P V
          (siteSheafTensorTmul N (scalarTensorPower A P (n + 1)) V x y) q) =
        siteSheafTensorTmul N (scalarTensorPower A P (n + 2)) V x
          (siteSheafTensorTmul (scalarTensorPower A P (n + 1)) P V y q)) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (φ : (signedLinePower.{u, v, w} P (.negSucc n)).val.obj V)
      (y : (scalarTensorPower A P (n + 1)).val.obj V),
      ((ordinaryEvaluation n).app N).val.app V
        (siteSheafTensorTmul _ (scalarTensorPower A P (n + 1)) V
          (siteSheafTensorTmul N (signedLinePower.{u, v, w} P (.negSucc n)) V x φ) y) =
        @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
          (N.val.obj V) inferInstance (φ.app (op (Over.mk (𝟙 V.unop))) y) x) 

section GenericLineConstraints
universe ga gha gd ghd ge ghe
variable {A₀ : Type ga} [Category.{gha} A₀] [HasZeroMorphisms A₀]
  {D₀ : Type gd} [Category.{ghd} D₀]

/-- Localization-normalized constraints, with the ordinary predicate as a parameter.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
inductive LocalizedLineConstraints
    (Q : CochainComplex A₀ ℤ ⥤ D₀)
    (r : ℤ → A₀ ⥤ A₀) [∀ i, (r i).PreservesZeroMorphisms]
    (d : ℤ → D₀ ⥤ D₀)
    (ordinary : (r 0 ≅ 𝟭 _) →
      (∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ≅ r (.ofNat (n + 2))) →
      (∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop)
    (c : ∀ i, Q ⋙ d i ≅ (r i).mapHomologicalComplex (.up ℤ) ⋙ Q)
    (u : d 0 ≅ 𝟭 _)
    (p : ∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ≅ d (.ofNat (n + 2)))
    (e : ∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _) : Prop
  | mk
    (ou : r 0 ≅ 𝟭 _)
    (op : ∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ≅ r (.ofNat (n + 2)))
    (oe : ∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _)
    (ho : ordinary ou op oe)
    (hu : ∀ E, HEq (u.hom.app (Q.obj E))
      ((c 0).hom.app E ≫ Q.map ((NatIso.mapHomologicalComplex ou (.up ℤ)).hom.app E)))
    (hp : ∀ n E, HEq ((p n).hom.app (Q.obj E) ≫ (c (.ofNat (n + 2))).hom.app E)
      ((d 1).map ((c (.ofNat (n + 1))).hom.app E) ≫
        (c 1).hom.app (((r (.ofNat (n + 1))).mapHomologicalComplex (.up ℤ)).obj E) ≫
        Q.map ((NatIso.mapHomologicalComplex (op n) (.up ℤ)).hom.app E)))
    (he : ∀ n E, HEq ((e n).app (Q.obj E))
      ((d (.ofNat (n + 1))).map ((c (.negSucc n)).hom.app E) ≫
        (c (.ofNat (n + 1))).hom.app
          (((r (.negSucc n)).mapHomologicalComplex (.up ℤ)).obj E) ≫
        Q.map ((NatTrans.mapHomologicalComplex (oe n) (.up ℤ)).app E))) :
    LocalizedLineConstraints Q r d ordinary c u p e

variable {E₀ : Type ge} [Category.{ghe} E₀]

/-- The three comparison equations, with the two constraint predicates as parameters.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
inductive LocalizedLineFamily
    (d : ℤ → D₀ ⥤ D₀) (e : ℤ → E₀ ⥤ E₀) (F : D₀ ⥤ E₀)
    (eta : ∀ i, d i ⋙ F ≅ F ⋙ e i)
    (cr : (d 0 ≅ 𝟭 _) →
      (∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ≅ d (.ofNat (n + 2))) →
      (∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop)
    (cs : (e 0 ≅ 𝟭 _) →
      (∀ n : ℕ, e (.ofNat (n + 1)) ⋙ e 1 ≅ e (.ofNat (n + 2))) →
      (∀ n : ℕ, e (.negSucc n) ⋙ e (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop) : Prop
  | mk
    (uR : d 0 ≅ 𝟭 _) (uS : e 0 ≅ 𝟭 _)
    (pR : ∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ≅ d (.ofNat (n + 2)))
    (pS : ∀ n : ℕ, e (.ofNat (n + 1)) ⋙ e 1 ≅ e (.ofNat (n + 2)))
    (eR : ∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _)
    (eS : ∀ n : ℕ, e (.negSucc n) ⋙ e (.ofNat (n + 1)) ⟶ 𝟭 _)
    (hR : cr uR pR eR) (hS : cs uS pS eS)
    (hu : ∀ X, (eta 0).hom.app X ≫ uS.hom.app (F.obj X) = F.map (uR.hom.app X))
    (hp : ∀ n X, F.map ((pR n).hom.app X) ≫ (eta (.ofNat (n + 2))).hom.app X =
      (eta 1).hom.app ((d (.ofNat (n + 1))).obj X) ≫
        (e 1).map ((eta (.ofNat (n + 1))).hom.app X) ≫ (pS n).hom.app (F.obj X))
    (he : ∀ n X, F.map ((eR n).app X) =
      (eta (.ofNat (n + 1))).hom.app ((d (.negSucc n)).obj X) ≫
        (e (.ofNat (n + 1))).map ((eta (.negSucc n)).hom.app X) ≫ (eS n).app (F.obj X)) :
    LocalizedLineFamily d e F eta cr cs

end GenericLineConstraints

/-- Right unit, positive-power associator and negative-positive evaluation constraints.
The ordinary constraints are specified on all local pure tensors. The derived constraints
are specified after localization using c; c itself is fixed by representativeIso and
collapse in DerivedAction. Thus these are the canonical constraints, with no arbitrary
monoidal structure or map selected. The positive constraint is the associator followed
by the one-term identification of the next power, and evaluation contracts the last two
factors. Source: Stacks 03EK, 04TT, 06YU and 07A4
(blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedLineConstraints (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (P : KFlatFixedTensor.Modules A)
    (c : ∀ d : ℤ, DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P d) ≅
      complexLine A (signedLinePower.{u, v, w} P d) ⋙
        DerivedCategory.Q)
    (rightUnitor : derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (product : ∀ n : ℕ,
      derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
          derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P 1) ≅
        derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (evaluation : ∀ n : ℕ,
      derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _) : Prop :=
  LocalizedLineConstraints DerivedCategory.Q
    (fun i ↦ siteSheafTensorRight (signedLinePower.{u, v, w} P i))
    (fun i ↦ derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P i))
    (OrdinaryLineConstraints A P) c rightUnitor product evaluation


/-- The simultaneous unit, positive-power and evaluation equations for the same eta family
whose components are fixed in DerivedAction. Source: Stacks 07A4; blueprint Powers and duals
(blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedFamilyCoherence
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
    (b : ∀ d : ℤ, DerivedActionData F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d)) : Prop :=
  LocalizedLineFamily
    (fun i ↦ derivedLine.{u, v, w, z} R (signedLinePower.{u, v, w} P i))
    (fun i ↦ derivedLine.{u, v, w, z} S (signedLinePower.{u, v, w} Q i))
    F.mapDerivedCategory (fun i ↦ (b i).2.2)
    (DerivedLineConstraints R P (fun i ↦ (b i).1))
    (DerivedLineConstraints S Q (fun i ↦ (b i).2.1))




variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

/-- Naturality in isomorphisms of the two line data. Negative powers use inverse dual maps.
Source: Stacks 03EL, 0GMX (blueprint: def-pur-signed-line-derived-action-data). -/
def IsoNaturality
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (P' : KFlatFixedTensor.Modules R) (Q' : KFlatFixedTensor.Modules S)
    (b : P ≅ P') (c : Q ≅ Q') (t' : (pull a).obj P' ≅ Q')
    (T' : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P' d) ≅
      signedLinePower.{u, v, w} Q' d),
    (pull a).map b.hom ≫ t'.hom = t.hom ≫ c.hom →
    SignedLinePullbackNormalized a P' Q' t' T' →
    ∀ d : ℤ, (pull a).map (signedIsoHom b d) ≫ (T' d).hom =
      (T d).hom ≫ signedIsoHom c d

attribute [local irreducible] IsoNaturality

/-- Naturality in arbitrary coefficient extensions compatible with the structural isomorphism.
The existing scalar-power identifications and scalar/pullback square specify the canonical
balanced-tensor comparison; no arbitrary comparison is assumed. Degree-one compatibility
is exactly the assertion that t' is induced from t. No flatness of either ring map occurs.
Source: Stacks 03EL, 0GMX, 0FNY
(blueprint: def-pur-signed-line-derived-action-data). -/
def ScalarNaturality
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (R' : Sheaf J CommRingCat.{max u v w})
    (S' : Sheaf K CommRingCat.{max u v w}) (α : R ⟶ R') (β : S ⟶ S')
    (a' : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R' ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S')),
    IsIso ((rAdj.homEquiv _ _).symm a') →
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α ≫ a' =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map β) →
    ∀ (t' : (pull a').obj (changeOfRingsOfUniverses α P) ≅ changeOfRingsOfUniverses β Q)
      (T' : ∀ d : ℤ,
        (pull a').obj (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d) ≅
          signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
      (B : ∀ d : ℤ, changeOfRingsOfUniverses α (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
      (E : ∀ d : ℤ, changeOfRingsOfUniverses β (signedLinePower.{u, v, w} Q d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d),
      SignedLinePullbackNormalized a' _ _ t' T' →
      SignedLineComparisonNormalized α P _ (Iso.refl _) B →
      SignedLineComparisonNormalized β Q _ (Iso.refl _) E →
      SignedLineScalarPullbackSquare α β a a' P _ Q _
        (Iso.refl _) (Iso.refl _) t t' →
      ∀ d : ℤ, SignedLineScalarPullbackSquare α β a a'
        (signedLinePower.{u, v, w} P d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
        (signedLinePower.{u, v, w} Q d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
        (B d) (E d) (T d) (T' d)

attribute [local irreducible] ScalarNaturality

end SheafOfModules.SignedLineDerivedBaseChange
```

## Users

The downstream scan returned 708 transitive modules. Its `--uses` scan returned the following 61 modules (including the item); rows other than CartesianCoefficientTwists and the item are lexical matches to other namespaces. None of the external modules uses DerivedLineConstraints or DerivedFamilyCoherence directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | V1 | Definition owner moved; same names and public re-export; proof filled. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Uses the main theorem, pull, derivedLine, and comparison projections; all retain their meanings. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ContinuousModuleSectionModel | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.EquivariantAdicFibreData | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.EquivariantAdicFibreNaturalityData | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.EquivariantAdicFibreRealization | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.EquivariantAdicFibreRealizationData | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.FiniteStrataCompletionDetection | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | R8 (not adapted) | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | S5 (not adapted) | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.NormalizedInternalSupportScalars | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ParameterRootIntegralNilFibre | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.TowerChernPullback | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.VerdierExchange | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.Paper.WfTateTwist | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | D3 (not adapted) | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Lexical match to an unrelated declaration; no effect. |
| Sheaf.SixFunctors.IntegralRestrictionLine | G2 (not adapted) | Lexical match to an unrelated declaration; no effect. |

No external consumer adaptation is presently necessary. The unchanged CartesianCoefficientTwists was checked twice against the repaired interface; both runs exceeded the time limit without a type error. Its uses are the main theorem, pull, derivedLine and comparison projections, whose mathematical meanings are unchanged. The exact signedComparison_exists consumer argument was checked separately against the repaired interface and compiled in 12.9 seconds. No external constraint-predicate eliminator occurs.

## Status

landed 20261025T124047-L-1930969 2026-10-25 (merge of deliver/V1/Sheaf.Algebra.Homology.SignedLineDerivedBaseChange)
