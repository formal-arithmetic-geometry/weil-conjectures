# WeilConjectures.AdicPurityScalarNaturality.Data

## Reason

Repair the quarantined 60-second timeout recorded in coord/rework.tsv, restoring
its original theorem and mathematical content. The large dependent Data record
caused expensive repeated coefficient-category checks in generated declarations.
Store its fields in OperationData, ComparisonData and Data by record inheritance.
Every original field proposition and normalization equation is retained, and all data
still comes from a real construction. There are no new proof holes.

The original exposed sourceShift and scalarShift implementations also expanded
large inherited full-subcategory structures. They now use no_expose and Mathlib’s canonical lifted-functor instance.
The latter uses liftCompιIso = Iso.refl, the original comparison. All named instances remain public, with the same types. Folding
comparisons locally, honoring transparency for the final records, and explicitly
passing the recorded shift structures avoids redundant instance reconstruction.
No limit is increased, and no module or proof is split to evade the time limit.

## Old

The preserved source is quarantine/Sheaf/Paper/AdicPurityScalarNaturality.lean.
Its complete original record definition is:

```lean
structure Data where
  scalarClosed : ScalarClosed D C X Y
  finiteRightNormalized : FiniteRightNormalized D C f S
  sourceAdditive (E : Field D C) : (source D C f d E).Additive
  sourceExact (E : Field D C) : (source D C f d E).IsTriangulated
  sourceLinear (E : Field D C) :
    (source D C f d E).Linear (Padic.coefficientExtensionIntegers C.l E.val)
  targetLinear (E : Field D C) :
    (target D C f S E).Linear (Padic.coefficientExtensionIntegers C.l E.val)
  targetExact (E : Field D C) : (target D C f S E).IsTriangulated
  scalarAdditive (E F : Field D C) (h : E ≤ F) (side : Bool) :
    (scalar D C scalarClosed E F h side).Additive
  scalarExact (E F : Field D C) (h : E ≤ F) (side : Bool) :
    (scalar D C scalarClosed E F h side).IsTriangulated
  gamma (E : Field D C) : source D C f d E ≅ (target D C f S E)
  targetRealization (E : Field D C) :
    target D C f S E ⋙ (finiteTorConstructibleIntegral C.l E.val X).ι ≅
      (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙
        integralExceptionalInverseImage C.l E.val D C.different f
  targetRealizationReductions : TargetRealizationReductions D C f d S targetRealization
  finiteReductions : FiniteReductions D C f d S gamma targetRealization
  a (E F : Field D C) (h : E ≤ F) :
    source D C f d E ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ source D C f d F
  aCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y) :
    ((a E F h).hom.app K).hom =
      (sourceScalarComponent D C f d scalarClosed E F h K).hom
  c (E F : Field D C) (h : E ≤ F) :
    (operation D C f S E).F ⋙ scalar D C scalarClosed E F h false ≅
      scalar D C scalarClosed E F h true ⋙ (operation D C f S F).F
  cCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E X) :
    (c E F h).hom.app K =
      (scalarBridge D C f S scalarClosed E F h false ((operation D C f S E).F.obj K)).hom ≫
        (compactComparison D C f S E F h).hom.app K ≫
        (operation D C f S F).F.map
          (scalarBridge D C f S scalarClosed E F h true K).inv
  b (E F : Field D C) (h : E ≤ F) :
    (target D C f S E) ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ (target D C f S F)
  bMate : CoefficientMate D C f S scalarClosed c b
  coherence : Coherence D C f d S scalarClosed gamma a b
```

The affected shift instances were:

```lean
instance sourceShift (E : Field D C) : (source D C f d E).CommShift ℤ := by
  letI := (IntegralSystemRealization.integralShifts C.l E.val).pull f
  letI : (ambientSource D C f d E).CommShift ℤ := by
    dsimp [ambientSource, integralComplexTwist]
    infer_instance
  exact Functor.CommShift.ofComp (G := (finiteTorConstructibleIntegral C.l E.val X).ι)
    (H := (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙ ambientSource D C f d E)
    (Iso.refl _) ℤ

/-- Ordinary scalar shifts are the ones inherited from derived tensor.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
instance scalarShift (hC : ScalarClosed D C X Y) (E F : Field D C)
    (h : E ≤ F) (side : Bool) : (scalar D C hC E F h side).CommShift ℤ :=
  Functor.CommShift.ofComp (G := (finiteTorConstructibleIntegral C.l F.val _).ι)
    (H := (finiteTorConstructibleIntegral C.l E.val _).ι ⋙ ordinary D C E F h _)
    (Iso.refl _) ℤ
```

The shift composition and compatibility implementations were:

```lean
@[instance_reducible] def composeShift {A B V : Type (u + 2)} [Category.{u + 2} A]
    [Category.{u + 2} B] [Category.{u + 2} V]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    (F : A ⥤ B) (G : B ⥤ V) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) :
    (F ⋙ G).CommShift ℤ :=
  letI := sF
  letI := sG
  inferInstance

/-- Mathlib's shift compatibility, with the two canonical structures made explicit.
Source: purity transport shift equations
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev ShiftCompatibility {A B : Type (u + 2)} [Category.{u + 2} A]
    [Category.{u + 2} B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) (e : F ≅ G) : Prop :=
  letI := sF
  letI := sG
  e.hom.CommShift ℤ
```

The original local irreducible block followed Coherence, and the two backward
transparency options were false throughout the module.

## New

```lean
structure OperationData where
  scalarClosed : ScalarClosed D C X Y
  finiteRightNormalized : FiniteRightNormalized D C f S
  sourceAdditive (E : Field D C) : SourceAdditiveProperty D C f d E
  sourceExact (E : Field D C) : SourceExactProperty D C f d E
  sourceLinear (E : Field D C) : SourceLinearProperty D C f d E
  targetLinear (E : Field D C) : TargetLinearProperty D C f S E
  targetExact (E : Field D C) : TargetExactProperty D C f S E
  scalarAdditive (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarAdditiveProperty D C (X := X) (Y := Y) scalarClosed E F h side
  scalarExact (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarExactProperty D C (X := X) (Y := Y) scalarClosed E F h side

/-- The normalized comparisons of the same simultaneous purity family.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure ComparisonData extends OperationData D C f d S where
  gamma (E : Field D C) : source D C f d E ≅ (target D C f S E)
  targetRealization (E : Field D C) :
    target D C f S E ⋙ (finiteTorConstructibleIntegral C.l E.val X).ι ≅
      (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙
        integralExceptionalInverseImage C.l E.val D C.different f
  targetRealizationReductions : TargetRealizationReductions D C f d S targetRealization
  finiteReductions : FiniteReductions D C f d S gamma targetRealization
  a (E F : Field D C) (h : E ≤ F) :
    source D C f d E ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ source D C f d F
  aCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y) :
    ((a E F h).hom.app K).hom =
      (sourceScalarComponent D C f d scalarClosed E F h K).hom
  c (E F : Field D C) (h : E ≤ F) :
    (operation D C f S E).F ⋙ scalar D C scalarClosed E F h false ≅
      scalar D C scalarClosed E F h true ⋙ (operation D C f S F).F
  cCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E X) :
    (c E F h).hom.app K =
      (scalarBridge D C f S scalarClosed E F h false ((operation D C f S E).F.obj K)).hom ≫
        (compactComparison D C f S E F h).hom.app K ≫
        (operation D C f S F).F.map
          (scalarBridge D C f S scalarClosed E F h true K).inv
  b (E F : Field D C) (h : E ≤ F) :
    (target D C f S E) ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ (target D C f S F)
  bMate : CoefficientMate D C f S scalarClosed c b

/-- The simultaneous family with all operation, reduction and coefficient equations.
The inherited records store exactly the original fields in three bounded groups.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure Data extends ComparisonData D C f d S where
  coherence : Coherence D C f d S scalarClosed gamma a b
```

Record inheritance gives exactly the same simultaneous family: the first nine
fields form OperationData, the comparisons and their normalization fields form
ComparisonData, and Data adds coherence. Projecting or packing these groups loses
no information and adds no requirement. Inherited field access remains available.
The constructor representation changes; this requires the normal independent
statement review for targets that use Data, although the mathematical predicate
is unchanged.

The seven operation class propositions are named definitions, folded during
record elaboration. Each is exposed, and explicit unfold gives exactly its
original type; irreducibility restricts automatic elaboration, not its meaning.

```lean
/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def SourceAdditiveProperty (E : Field D C) : Prop := (source D C f d E).Additive

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def SourceExactProperty (E : Field D C) : Prop := (source D C f d E).IsTriangulated

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def SourceLinearProperty (E : Field D C) : Prop :=
  (source D C f d E).Linear (Padic.coefficientExtensionIntegers C.l E.val)

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def TargetLinearProperty (E : Field D C) : Prop :=
  (target D C f S E).Linear (Padic.coefficientExtensionIntegers C.l E.val)

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def TargetExactProperty (E : Field D C) : Prop := (target D C f S E).IsTriangulated

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def ScalarAdditiveProperty (scalarClosed : ScalarClosed D C X Y)
    (E F : Field D C) (h : E ≤ F) (side : Bool) : Prop :=
  (scalar D C scalarClosed E F h side).Additive

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def ScalarExactProperty (scalarClosed : ScalarClosed D C X Y)
    (E F : Field D C) (h : E ≤ F) (side : Bool) : Prop :=
  (scalar D C scalarClosed E F h side).IsTriangulated
```

The shift instances now are:

```lean
@[no_expose] instance sourceShift (E : Field D C) : (source D C f d E).CommShift ℤ := by
  letI := (IntegralSystemRealization.integralShifts C.l E.val).pull f
  letI : (ambientSource D C f d E).CommShift ℤ := by
    dsimp [ambientSource, integralComplexTwist]
    infer_instance
  dsimp only [source]
  infer_instance

attribute [local irreducible] sourceShift

/-- Ordinary scalar shifts are the ones inherited from derived tensor.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] instance scalarShift (hC : ScalarClosed D C X Y) (E F : Field D C)
    (h : E ≤ F) (side : Bool) : (scalar D C hC E F h side).CommShift ℤ := by
  dsimp only [scalar]
  infer_instance


attribute [local irreducible] scalarShift
```

The shift API now passes exactly the specified structures to Mathlib:

```lean
@[instance_reducible] def composeShift {A B V : Type (u + 2)} [Category.{u + 2} A]
    [Category.{u + 2} B] [Category.{u + 2} V]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    (F : A ⥤ B) (G : B ⥤ V) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) :
    (F ⋙ G).CommShift ℤ :=
  @Functor.CommShift.comp A B V _ _ _ F G ℤ _ _ _ _ sF sG

/-- Mathlib's shift compatibility, with the two canonical structures made explicit.
Source: purity transport shift equations
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev ShiftCompatibility {A B : Type (u + 2)} [Category.{u + 2} A]
    [Category.{u + 2} B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) (e : F ≅ G) : Prop :=
  @NatTrans.CommShift A B _ _ F G e.hom ℤ _ _ _ sF sG

attribute [local irreducible] rawScalarShift targetShift composeShift
```

The existing comparisons are locally irreducible after their definitions (source,
scalar and target only after the reduction predicates that require unfolding).
The two backward transparency options become true before composeShift. Coherence
is locally irreducible before the records. These are local elaboration settings. 

The public imports SfOpenExceptionalBaseChange and AdicProjectionShiftCoherence
and the unused private import AdicScalarTraceCoherence are removed. The narrower
FiniteTorAmplitudeSites and IntegralOperationShiftData imports supply the actual
statement structures. The lost unbundled closure instance is supplied directly by:

```lean
instance coefficientTriangulated (E : Field D C) (W : Scheme.{u}) :
    (finiteTorConstructibleIntegral C.l E.val W).IsTriangulated :=
  ConstructibleExceptionalCoefficients.integralTriangulated C.l { carrier := E.val } W
```

This is the same existing integralTriangulated theorem used by the removed
projection module; both are proofs of the identical proposition. Proof
irrelevance preserves the inherited shift structures definitionally.

The reduction bridge and source comparison are the same canonical constructions,
with explicit sharing and a direct equality transport. The equality proof hp is
unchanged. Transporting the adjoint comparison is equal to postcomposing with
its eqToIso, by equality induction; no arbitrary automorphism is introduced.
The shared isomorphisms have the original order and parenthesization.

Old bridge:

```lean
@[no_expose] def reductionBridge (E : Field D C) (W : Scheme.{u}) (n : ℕ) :
    scalarReductionDerivedExtension C.l E.val W n ≅
      Scheme.pbcDerivedExtend
        ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W) := by
  let φ := completedIntegralCommRingProjectionUnrestricted C.l E.val W n
  have hp : (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W = φ := by
    dsimp only [PurCompactSupport.reduction, PurCompactSupport.projection, φ]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  exact ((derivedScalarExtensionRestrictionAdjunction C.l E.val W n).choose.leftAdjointUniq
    (Scheme.pbcDerivedScalarAdjunction φ)) ≪≫
    eqToIso (congrArg (fun ψ ↦ Scheme.pbcDerivedExtend ψ) hp.symm)
```

New bridge:

```lean
@[no_expose] def reductionBridge (E : Field D C) (W : Scheme.{u}) (n : ℕ) :
    scalarReductionDerivedExtension C.l E.val W n ≅
      Scheme.pbcDerivedExtend
        ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W) := by
  let φ := completedIntegralCommRingProjectionUnrestricted C.l E.val W n
  have hp : (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W = φ := by
    dsimp only [PurCompactSupport.reduction, PurCompactSupport.projection, φ]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  exact hp.symm ▸
    (derivedScalarExtensionRestrictionAdjunction C.l E.val W n).choose.leftAdjointUniq
      (Scheme.pbcDerivedScalarAdjunction φ)


attribute [local irreducible] reductionBridge
```

Old source comparison:

```lean
@[no_expose] def sourceScalarComponent (hC : ScalarClosed D C X Y) (E F : Field D C)
    (h : E ≤ F) (K : Cat D C E Y) :
    ((scalar D C hC E F h true).obj ((source D C f d E).obj K)).obj ≅
      ((source D C f d F).obj ((scalar D C hC E F h false).obj K)).obj := by
  let P := (constructibleIntegralPullback C.l E.val f).obj ⟨K.obj, K.property.1⟩
  have ht : IsSfDerivedComplete C.l E.val X
      ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj) :=
    ((twist_preserves_finiteness C.l E.val X C.Qbar (d : ℤ)).the project server.the project server.1
      P.obj P.property).1
  exact ((ordinary D C E F h X).commShiftIso (2 * (d : ℤ))).app
      ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) X _ ht ≪≫
        (integralTwistCompletedBeta C.l E.val F.val (IntermediateField.inclusion h) X
          (d : ℤ)).app P ≪≫
        (integralComplexTwist D C.l C.different F.val X (d : ℤ)).mapIso
          (scalarPullbackCompleted C.l E.val F.val (IntermediateField.inclusion h) f
            K.obj K.property.1.1 P.property.1 ≪≫
          (integralDerivedPullback C.l F.val f).mapIso
            (scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) Y
              K.obj K.property.1.1).symm))
```

New source comparison:

```lean
@[no_expose] def sourceScalarComponent (hC : ScalarClosed D C X Y) (E F : Field D C)
    (h : E ≤ F) (K : Cat D C E Y) :
    ((scalar D C hC E F h true).obj ((source D C f d E).obj K)).obj ≅
      ((source D C f d F).obj ((scalar D C hC E F h false).obj K)).obj := by
  let P := (constructibleIntegralPullback C.l E.val f).obj ⟨K.obj, K.property.1⟩
  have ht : IsSfDerivedComplete C.l E.val X
      ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj) :=
    ((twist_preserves_finiteness C.l E.val X C.Qbar (d : ℤ)).the project server.the project server.1
      P.obj P.property).1
  let chiX := scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) X
    ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj) ht
  let beta := (integralTwistCompletedBeta C.l E.val F.val (IntermediateField.inclusion h)
    X (d : ℤ)).app P
  let chiY := scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) Y
    K.obj K.property.1.1
  let pull := scalarPullbackCompleted C.l E.val F.val (IntermediateField.inclusion h) f
    K.obj K.property.1.1 P.property.1
  let pullChi := (integralDerivedPullback C.l F.val f).mapIso chiY.symm
  let twist := (integralComplexTwist D C.l C.different F.val X (d : ℤ)).mapIso
    (pull ≪≫ pullChi)
  let comparison := chiX ≪≫ beta ≪≫ twist
  let shift := ((ordinary D C E F h X).commShiftIso (2 * (d : ℤ))).app
    ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj)
  exact shift ≪≫ (shiftFunctor _ (2 * (d : ℤ))).mapIso comparison


attribute [local irreducible] sourceScalarComponent
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed; quarantined | Sole consumer found in both library and quarantine roots. Uses Data, gamma, targetRealization, finiteReductions, source, target, operation and reductionBridge. Its original text is checked against the repaired module; no adaptation intended. |

The downstream index does not recognize this quarantined absent module. Direct
searches of lean/Sheaf, lean/WeilConjectures and both quarantine roots supply the
inventory instead. No adopted-source declaration, target signature or quarantine
archive is edited. The DAG retains the original statement and proof dependencies;
its Lean attachment also records the helper declarations.

## Status

landed 20261024T190413-L-4045636 2026-10-24 (merge of deliver/N2/Sheaf.Paper.AdicPurityScalarNaturality)
