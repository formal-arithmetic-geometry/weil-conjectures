# AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom

## Reason

Use the canonical `Functor.LaxMonoidal.ihomComparison` of the explicitly constructed
strong derived monoidal comparison functor. The proved theorem
`siteComparisonEvaluationHom_eq_curry` identifies this map with the original evaluation
specification: curry the inverse canonical tensor comparison followed by pullback of
evaluation. The old `derivedTensorHomAdjunction` wrapper has by definition the
`ihom.adjunction` hom-equivalence and the `ihom.ev` counit, so this equation preserves
its mathematical meaning. The old and new expressions are propositionally equal;
this record does not claim they are definitionally equal.

`siteComparisonTensorIso` is constructed from the same transported derived tensorator;
its separate change record and the proved `siteComparisonDerivedMonoidal_δ` formula
explain agreement with the original four-factor formula.
Making the comparison definition irreducible and giving its proved evaluation equation
avoids expensive unfolding when applying the generic internal-Hom comparison criterion.
Signatures, hypotheses, coefficient sites and target statements are unchanged. The
representation repair is submitted for independent review, including targets using the
definition. No data are selected from an unproved existence statement.

## Old

```lean
noncomputable def siteComparisonEvaluationHom
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (comparisonUpperStar A X).mapDerivedCategory.obj
        (((Etale.derivedHom A X).obj (op K)).obj M) ⟶
      ((derivedHom A X).obj
        (op ((comparisonUpperStar A X).mapDerivedCategory.obj K))).obj
          ((comparisonUpperStar A X).mapDerivedCategory.obj M) :=
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let H := ((Etale.derivedHom A X).obj (op K)).obj M
  (derivedTensorHomAdjunction A (F.obj K)).homEquiv (F.obj H) (F.obj M)
    ((siteComparisonTensorIso A X K).inv.app H ≫
      F.map ((Etale.derivedTensorHomAdjunction A K).counit.app M))
```

## New

```lean
/-- The specified comparison is the transpose of pullback of evaluation, using the
canonical tensor comparison. It is defined on all ambient complexes; invertibility
requires hypotheses and is a separate assertion.
Source: Stacks Tags 03EO, 03EL, 08J7
(blueprint: def-sf-evaluation-hom-site-comparison). -/
@[irreducible]
noncomputable def siteComparisonEvaluationHom
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (comparisonUpperStar A X).mapDerivedCategory.obj
        (((Etale.derivedHom A X).obj (op K)).obj M) ⟶
      ((derivedHom A X).obj
        (op ((comparisonUpperStar A X).mapDerivedCategory.obj K))).obj
          ((comparisonUpperStar A X).mapDerivedCategory.obj M) :=
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let : F.Monoidal := siteComparisonDerivedMonoidal A X
  (Functor.LaxMonoidal.ihomComparison F K).natTrans.app M

/-- The canonical comparison is exactly the transpose of pulled-back evaluation.
The monoidal tensorator is the inverse of `siteComparisonTensorIso`, so this is its
original evaluation specification. Source: Stacks Tag 03EO
(blueprint: def-sf-evaluation-hom-site-comparison). -/
theorem siteComparisonEvaluationHom_eq_curry
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let F := (comparisonUpperStar A X).mapDerivedCategory
    let : F.Monoidal := siteComparisonDerivedMonoidal A X
    siteComparisonEvaluationHom A X K M =
      MonoidalClosed.curry ((siteComparisonTensorIso A X K).inv.app ((ihom K).obj M) ≫
        F.map ((ihom.ev K).app M)) := by
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let : F.Monoidal := siteComparisonDerivedMonoidal A X
  unfold siteComparisonEvaluationHom
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry F K M]
  unfold siteComparisonTensorIso
  rfl
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison | unclaimed | Both comparison definitions retain their signatures and evaluation meaning; the proved API exposes the constructed maps. |
| Sheaf.Paper.FiniteFreeHomComparison | Q3 | Proves invertibility through the canonical derived monoidal structure and dualizability. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Its `IsEvaluationComparison` predicate names the Hom comparison. The signature and evaluation specification are preserved; no edit. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | States invertibility of the same Hom arrow for constructible complexes; no edit. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Its `siteHom` definition uses the same Hom arrow; no edit. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Its compatibility predicates use both comparison maps. Their signatures and mathematical maps are preserved; no edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Its mapping-arrow composites use both comparison maps; no edit. |

The five additional users occur in the restored sources listed by `coord/rework.tsv`.
Inspection finds uses in statements and composite-map definitions, with no proof unfolding
of the changed comparison bodies. Their existing interfaces are preserved. No module held
by another group is edited, and no forced adaptation is claimed.

## Status

landed 20261020T211816-L-3504665 2026-10-20 (merge of deliver/Q3/Sheaf.Paper.FiniteFreeHomComparison)
