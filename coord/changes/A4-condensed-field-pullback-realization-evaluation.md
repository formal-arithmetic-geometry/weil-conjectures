# AlgebraicGeometry.ProEtale.condensedFieldPullbackRealization

## Reason

Concrete evaluation of the raw conjugated coefficient forced kernel reduction through the
inverse-image construction in the old definition. Direct unfolding and a generic evaluation
equation reproduced deterministic timeouts. Merely marking the definition irreducible also
failed. The repaired definition is the unique morphism equal to the original explicit
composite. Its existence and uniqueness are proved directly from that composite, and an
explicit equality theorem exposes it when required. The full geometric coefficient theorem
then compiles in about nine seconds, with its statement unchanged.

The module `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix` is unclaimed.
No module held by another group is edited. No new axiom, postponed proof, or unspecified
existential witness is introduced: equality to the displayed construction determines the
chosen morphism exactly. The choice is from a fully proved unique specification.

## Old

```lean
noncomputable def condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ⟶
    (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E) :=
  condensedPullbackHom (Profinite.continuousCoefficientRingObj E) g ≫
    (condensedFieldContinuousMapIso E V).hom.hom
```

## New

```lean
noncomputable def condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ⟶
    (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E) :=
  (existsUnique_condensedFieldPullbackRealization E g).exists.choose
```

The new fully proved theorem `existsUnique_condensedFieldPullbackRealization` says that
there exists exactly one morphism equal to the old displayed composite; its witness is that
composite and its uniqueness proof is the equality hypothesis. The fully proved
`condensedFieldPullbackRealization_eq` identifies the new definition with the old composite.
The existing IsIso and IsMonHom instances rewrite by this equation instead of unfolding.
The item's private `realization_conjugate` uses the same equation before the existing generic
conjugation lemma. Every existing public signature and visibility is unchanged.

## Users

`tools/downstream.py` reports 88 transitive importers and the following seven textual users.
The original six-file textual-user set was compiled in import order against the repaired
definition; all files compile without warnings. The fresh delivery base added the seventh
user. Its sole affected declaration is the private `exists_small_evaluation`; the entire
original proof of that declaration compiles unchanged against the repair. This scratch
check omits the unrelated `IntegralMatrixCoefficientTransport` import, used only later in
the module, because that newly landed module is not yet in the published compiled cache.
The attempted whole-module compile reports precisely the missing import object file.
No change to this consumer is delivered, and its unchanged later statements use the same
private theorem signature. The five unchanged consumers require no adaptation.
The equation proves equality of old and new data for every E, X, V and g, so no downstream
statement is weakened or strengthened. The identity-map, zero-endomorphism and
identity-endomorphism cases retain the same coefficient values. An empty V admits no map
from Spec Ω, so the coefficient theorem has no omitted empty-scheme case.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Definition implementation and equation API; same signature and exact value. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | A4 | Use the equation API in private realization_conjugate; close final hole. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Unchanged source compiled against repaired dependencies; same statement. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Unchanged source compiled against repaired dependencies; same statement. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Unchanged source compiled against repaired dependencies; same statement. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Unchanged source compiled against repaired dependencies; same statement. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Sole affected private theorem compiles unchanged; full module awaits unrelated IntegralMatrixCoefficientTransport cache publication. |

No signature in `lean/Challenge.lean` uses the changed definition. The mathematical meaning
of coefficient constructions is preserved by the proved exact equality above, including
where they occur in downstream definitions. No target signature or target definition changes.

## Status

landed 20261016T102626-L-2294524 2026-10-16 (merge of deliver/A4/Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient)
