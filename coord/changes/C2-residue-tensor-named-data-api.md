# CategoryTheory.Functor.residueDerivedMonoidal

## Reason

The canonical tensor-route proof needs the defining tensor/counit square and the
ordinary braiding equation. Add fully proved APIs for these equations and a generic
model normalization theorem in their existing construction modules. Retain the
original oplax fields directly in `residueDerivedMonoidal`, avoiding reconstruction
through the inverse tensor isomorphisms of `CoreMonoidal.ofOplaxMonoidal`.
The resulting fields are definitionally equal to the originals; the original
coherence proofs type-check against them. No target statement changes.

The named `tensorModelMapWith` and `tensorModelTargetWith` interfaces, and the
concrete applications with named derived functors and counits, have now landed
independently in the repair base. This delivery retains them. The two concrete
model definitions are written in tactic mode with the same terms. The concrete
construction scopes select the existing `sheafBraidedCategory` data used by the
presentation and model. No data is chosen from an unproved theorem.

Repair of return C-55a79: the current `IntegralResidueScalarCounitModel.lean`
already includes the necessary unfolding adaptation. Its current source is copied
verbatim into the sandbox and makes no change in this delivery. The independently
landed file and named-data API are described in
`coord/changes/A2-residue-tensor-model-named-data.md`.

The anonymous local `EssentiallySmall.{u + 1} Profinite.{u}` proof remains the
canonical `essentiallySmallSelf.{0} _`. The Users table includes the downstream
modules mentioning that signature; none needs an adaptation for this proposition.

## Old

The following bodies are copied verbatim from the current shared repair base.

```lean
@[instance_reducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  letI := residueDerivedOplax F
  haveI := residueDerivedOplax_isIso_δ F
  haveI := residueDerivedOplax_isIso_η F
  exact (CoreMonoidal.ofOplaxMonoidal _).toMonoidal

@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) :=
  Functor.tensorModelTargetWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

/-- The explicit common map for the two routes in the residue square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) :=
  letI := residueExchangeOrdinaryPullMonoidal ℓ E f
  Functor.tensorModelMapWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (residueExchangeTensorCounit ℓ E Y) P
```

## New

The following bodies retain the named functor/counit interface. The monoidal
record keeps its original oplax fields directly.

```lean
@[instance_reducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  letI := residueDerivedOplax F
  haveI := residueDerivedOplax_isIso_δ F
  haveI := residueDerivedOplax_isIso_η F
  -- Retain the original oplax fields directly, rather than reconstructing them
  -- through the inverse tensor isomorphisms of CoreMonoidal.
  exact { (CoreMonoidal.ofOplaxMonoidal _).toMonoidal with
    toOplaxMonoidal := residueDerivedOplax F }

@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  exact Functor.tensorModelTargetWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

/-- The explicit common map for the two routes in the residue square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  let := residueExchangeOrdinaryPullMonoidal ℓ E f
  exact Functor.tensorModelMapWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (residueExchangeTensorCounit ℓ E Y) P
```

- `tensorModelRoute_fac` proves normalization from its tensor/counit and braiding
  hypotheses by naturality and `derivedTensorPresentationIso_fac`.
- `residueOrdinaryUpperStar_braiding` is proved by the relative tensor coequalizer
  epimorphism, ambient pullback braiding and transport along the coefficient iso.
- `residueDerivedMonoidal_counit` is proved by the existing
  `leftDerivedTensorComparison_app_app_comp_tensorHom` equation.
- `IntegralResidueScalarCounitModel` is unchanged from the current upstream source.
- `IntegralResidueScalarGeometryBridge` and `IntegralResidueTensorGeometry` retain
  their statements and receive proof-only adaptations at the model invertibility
  check. Their original `with_unfolding_all` proofs expand the derived and module
  constructions. The adapted proofs select the existing canonical sheaf braidings,
  unfold the named pullback functor and counit, and simplify the generic target
  wrapper before applying the same `tensorModelTarget_isIso` theorem. The local
  irreducibility settings keep those constructions folded. Both are unclaimed.

All existing signatures and mathematical constructions are preserved. Since the
monoidal construction occurs in target definitions, its definitionally equal
presentation remains subject to the independent statement-meaning review.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Named-data interface retained; fully proved normalization API added. |
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | Named-data interface retained; fully proved normalization API added. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorSquare | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | Current upstream file retained verbatim; required unfolding adaptation already landed. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Proof-only unfolding adaptation at the model invertibility check; signature unchanged. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Proof-only unfolding adaptation at the model invertibility check; signature unchanged. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Named-data interface retained; fully proved normalization API added. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| Sheaf.Paper.IntegralResidueTensorRouteDescent | A2 | No edit; obsolete import removed from parent; its independent statement is unchanged. |
| Sheaf.Paper.IntegralResidueTensorRouteKFlat | C2 | Withdrawn; its false arbitrary-monoidal claim has no remaining importer. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | Canonical statement retained; direct normalization proof; arbitrary-m transport removed. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Existing statement and meaning unchanged; defining expressions remain definitionally equal. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | unclaimed | No edit; same canonical derived monoidal fields and signatures. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | The anonymous local EssentiallySmall proof is still canonical; no mathematical statement or proof changes here. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | The anonymous local EssentiallySmall proof is still canonical; no mathematical statement or proof changes here. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | The anonymous local EssentiallySmall proof is still canonical; no mathematical statement or proof changes here. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | The anonymous local EssentiallySmall proof is still canonical; no mathematical statement or proof changes here. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Mentions the same anonymous EssentiallySmall signature; the proposition and its canonical proof are unchanged, and no edit is required. |

## Status

landed 20261018T005637-L-2576920 2026-10-18 (merge of deliver/C2/Sheaf.Paper.IntegralResidueTensorRouteKFlat)
