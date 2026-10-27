# BalancedScalarAssociator representation

## Reason

Specialize a generic structure with explicit ordinary functors, derived functors, localization functors and computation counits. Its four fields are exactly the former ordinary, balanced, derived and computes fields. This shares the site-category instances in kernel conversions. Retain the original type name and all projection names as abbreviations; no mathematical hypothesis, formula or theorem conclusion changes.

## Old

```lean
/-- Normalization of the balanced scalar associator at ordinary and derived levels.
The derived formula uses K-flat representatives and the specified cochain counits.
Source: Stacks 03EK, 06YT and 06YY, DAG proof step 1
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure BalancedScalarAssociator
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)) where
  /-- The ordinary, sheafified balanced associator. -/
  ordinary : Fa.E ⋙ Fb.E ≅ Fba.E
  /-- Its precise formula on local tensor generators. -/
  balanced : ∀ M (U : Cᵒᵖ) (s : S.obj.obj U) (q : V.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (scalarTensorSection Fb (Fa.E.obj M) U q (scalarTensorSection Fa M U s x)) =
        scalarTensorSection Fba M U (b.hom.app U s * q) x
  /-- The natural associator on the unbounded derived categories. -/
  derived : Fa.T ⋙ Fb.T ≅ Fba.T
  /-- Its normalization through the canonical K-flat computation maps. -/
  computes : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ Fba.ε.app P =
      Fb.T.map (Fa.ε.app P) ≫ Fb.ε.app ((extendedComplex Fa).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)

```

## New

```lean
/-- Scalar reassociation with explicit functors and normalization predicates.
Source: Stacks 03EK, 06YY (blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure ScalarAssociatorData
    {A : Type xA₀} [Category.{yA₀} A] [Preadditive A]
    {B : Type xB₀} [Category.{yB₀} B] [Preadditive B]
    {D : Type xD₀} [Category.{yD₀} D] [Preadditive D]
    {DA : Type xA} [Category.{yA} DA] {DB : Type xB} [Category.{yB} DB]
    {DD : Type xD} [Category.{yD} DD]
    (E : A ⥤ B) [E.Additive] (F : B ⥤ D) [F.Additive] (G : A ⥤ D) [G.Additive]
    (T : DA ⥤ DB) (U : DB ⥤ DD) (V : DA ⥤ DD)
    (QA : CochainComplex A ℤ ⥤ DA) (QB : CochainComplex B ℤ ⥤ DB)
    (QD : CochainComplex D ℤ ⥤ DD)
    (ηa : QA ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ QB)
    (ηb : QB ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (ηba : QA ⋙ V ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (balancedFormula : (E ⋙ F ≅ G) → Prop) (good : CochainComplex A ℤ → Prop) where
  /-- The ordinary associator. -/
  ordinary : E ⋙ F ≅ G
  /-- Its prescribed normalization. -/
  balanced : balancedFormula ordinary
  /-- The derived associator. -/
  derived : T ⋙ U ≅ V
  /-- Its computation on resolving objects. -/
  computes : ∀ P, good P → derived.hom.app (QA.obj P) ≫ ηba.app P =
    U.map (ηa.app P) ≫ ηb.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      QD.map ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)

/-- The original balanced scalar associator, specialized from explicit functor data.
Source: Stacks 03EK, 06YT, 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)) :=
  ScalarAssociatorData Fa.E Fb.E Fba.E Fa.T Fb.T Fba.T
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q Fa.ε Fb.ε Fba.ε
    (fun ordinary ↦ ∀ M (U : Cᵒᵖ) (s : S.obj.obj U) (q : V.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (scalarTensorSection Fb (Fa.E.obj M) U q (scalarTensorSection Fa M U s x)) =
          scalarTensorSection Fba M U (b.hom.app U s * q) x)
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))

/-- The original ordinary projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.ordinary
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.ordinary α

/-- The original balanced projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.balanced
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.balanced α

/-- The original derived projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.derived
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.derived α

/-- The original computes projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.computes
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.computes α

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | B4 | Uses the same four data fields and formulas with generic projections. |
| Sheaf.Algebra.Homology.SectionsScalarDerivedTransport | unclaimed | Original names remain publicly visible; unchanged consumer check required. |

No target semantics change. This repairs representation cost, without splitting any proof or changing the time limit.

## Status

landed 20261025T201357-L-2465468 2026-10-25 (merge of deliver/B4/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
