# CoefficientConstructionFields; CoefficientConstructionCommon

## Reason

The reviewed coherence DAG requires literal rational object and localized-arrow normalization and the action on common representative arrows. The old construction records omit these facts and admit field-label twists on pair-category arrows. Add these construction normalizations, without assuming a coefficient or refinement cocycle. Rebase onto the A3 ConstructionData extraction and retain the proved existence assembly verbatim. The stage existence theorem must construct these same canonical functors. This changes target-reachable definitions and reopens statement review for the affected targets.

## Old

```lean
structure CoefficientConstructionFields (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)) where
  rationalizationComparison (c : Compactification f) (E : FieldStage.{max u v} l) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.integral E)) (R.operation c (.rational E))
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  rationalization_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (rationalizationComparison c E).q.hom.app K ≫
        (R.rationalLeft c E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((R.integralLeft c E).hom.app K)
  rationalComparison (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational E)) (R.operation c (.rational L))
      (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y)
  rational_normalized (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((rationalComparison c E L i).q.hom.app
        ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω L Y).map
        ((Scalar.counitQ.{u, v} l Ω
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (R.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionCommon (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) where
  commonComparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational (commonField.{u, v} l Ω i)))
      (R.operation c .closed)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  common_normalized (c : Compactification f)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((commonComparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K)))

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionRefinements (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) where
  refinement {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (R.operation c s) (R.operation d s)
  refinement_normalized {c d : Compactification f} (r : c.Refinement d)
      (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s) (refinement r (s.stage l))
  refinementRational {c d : Compactification f} (r : c.Refinement d)
      (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((refinement r (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω E Y).map ((refinement r (.integral E)).left.hom.app K))
  refinementCommon {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y i).map
          ((refinement r (.rational (commonField.{u, v} l Ω i))).left.hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (refinement r .closed).left.hom.app
        ((commonInclusion.{u, v} l Ω X i).obj K)

```

## New

```lean
/-- The action of a localized functor on the unchanged objects and integral arrows.
Source: raw coefficient localization
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def localizedAction {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Fi : A ⥤ B) (Fr : C ⥤ D) (LX : A ⥤ C) (LY : B ⥤ D) : Prop :=
  (∀ K : A, Fr.obj (LX.obj K) = LY.obj (Fi.obj K)) ∧
  (∀ (K L : A) (h : K ⟶ L), HEq (Fr.map (LX.map h)) (LY.map (Fi.map h)))

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionFields (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)) where
  rationalizationComparison (c : Compactification f) (E : FieldStage.{max u v} l) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.integral E)) (R.operation c (.rational E))
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  rationalization_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (rationalizationComparison c E).q.hom.app K ≫
        (R.rationalLeft c E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((R.integralLeft c E).hom.app K)
  rationalComparison (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational E)) (R.operation c (.rational L))
      (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y)
  rational_normalized (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((rationalComparison c E L i).q.hom.app
        ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω L Y).map
        ((Scalar.counitQ.{u, v} l Ω
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (R.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))

  rationalAction (c : Compactification f) (E : FieldStage.{max u v} l) :
    localizedAction (R.operation c (.integral E)).F (R.operation c (.rational E)).F
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)

/-- Coefficient squares determine the action on common representatives.
Source: common-stage construction on the colimit Hom groups
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def representativeAction
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Fj : B ⥤ D) (FΩ : E ⥤ H)
    (TX : A ⥤ B) (TY : C ⥤ D) (IXi : A ⥤ E) (IXj : B ⥤ E)
    (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY ≅ TX ⋙ Fj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi) : Prop :=
  ∀ (K : A) (L : B) (a : TX.obj K ⟶ L),
    FΩ.map (tauX.inv.app K ≫ IXj.map a) =
      qi.inv.app K ≫ tauY.inv.app (Fi.obj K) ≫ IYj.map (q.hom.app K) ≫
        IYj.map (Fj.map a) ≫ qj.hom.app L

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionCommon (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) where
  commonComparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational (commonField.{u, v} l Ω i)))
      (R.operation c .closed)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  common_normalized (c : Compactification f)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((commonComparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K)))

  common_morphism_normalized (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j) :
    representativeAction
      (R.operation c (.rational (commonField l Ω i))).F
      (R.operation c (.rational (commonField l Ω j))).F (R.operation c .closed).F
      (rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X)
      (rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y)
      (commonInclusion l Ω X i) (commonInclusion l Ω X j)
      (commonInclusion l Ω Y i) (commonInclusion l Ω Y j)
      (F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q
      (commonComparison c i).q (commonComparison c j).q
      (commonTransition l Ω X i j h) (commonTransition l Ω Y i j h)

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionRefinements (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) where
  refinement {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (R.operation c s) (R.operation d s)
  refinement_normalized {c d : Compactification f} (r : c.Refinement d)
      (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s) (refinement r (s.stage l))
  refinementRational {c d : Compactification f} (r : c.Refinement d)
      (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((refinement r (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω E Y).map ((refinement r (.integral E)).left.hom.app K))
  refinementCommon {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y i).map
          ((refinement r (.rational (commonField.{u, v} l Ω i))).left.hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (refinement r .closed).left.hom.app
        ((commonInclusion.{u, v} l Ω X i).obj K)

```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData | unclaimed | Defines the strengthened normalization records; data and all existing proofs retained. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData | unclaimed | Existing additional normalization remains valid; unchanged and compiled. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientStages | unclaimed | Existing theorem hole must construct the canonical localization and common action; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalLeftRefinements | unclaimed | Additional input fields; statement and proof hole unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Proved assembly preserved verbatim and compiled against the changed data. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | D6 | Uses object normalization for refinement descent and the representative action for common comparisons. |
| Sheaf.Paper.NormalizedRationalLeftLaws | D6 new | Uses literal localization normalization. |
| Sheaf.Paper.NormalizedCommonCoefficientLaws | D6 new | Proves the two common laws from representative action and counits. |
| Sheaf.Paper.NormalizedRingRefinementLaws | D6 new | Statement uses the repaired construction records. |

## Status

landed 20261025T162157-L-343722 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence)
