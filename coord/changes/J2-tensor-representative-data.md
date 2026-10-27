# WeilConjectures.PurityFiniteSetting.FiniteTensorCoreNormalized

## Reason

The full normalization formula repeatedly specialized four concrete monoidal category
instances in proofs. Profiler runs recorded 43--57 seconds in the final scalar-core
specialization alone; the complete item exceeded 120 seconds. Repair the actual normalization
data interface: store its three source factors, intermediate objects, common target and tail in a
`TensorRepresentativeData` record constructed by `finiteScalarTensorData`. The generic
`source` method composes the recorded factors in abstract categories. Neither cochain
category needs a monoidal instance in the record interface.
The main cancellation proof sees only the derived monoidal categories and these maps.
The record contains actual data, no chosen witness, proof hole or existence theorem.
The scalar representative and its certificate are stored as single-input functions,
then evaluated at the recorded tensor by the generic source method. This avoids
expanding the concrete cochain tensor inside the certificate construction.
The localization tensor has an explicitly typed native map
`cochainLocalizationTensor`, shared by the diagram and its concrete sheaf property
API. Thus merely comparing map types does not expand the lax-monoidal instance.
This is the same original native localization tensorator.
Its three invertibility certificates are proof fields supplied at construction by
`cochainLocalizationTensor_isIso`, `finiteScalarRepresentative_isIso` and
`finiteScalarCochainComparison_isIso`. The certificate proofs supply no object or map.
Public named property APIs are required here because a public definition cannot
refer to private proof helpers.
A separate proved property API `finiteScalarTensorData_source_isIso` gives invertibility
on K-flat pairs. This is a definition repair, not a split of the main proof to evade the
file limit. The entire tensorator, unit and density uniqueness proof stays in the item.

## Old

```lean
def FiniteTensorCoreNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u})
    (h : (P.finiteTensorReduction m hm hmn T).CoreMonoidal) : Prop :=
  ∀ (C D : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat D →
    finiteTensorBinaryRepresentativeSquare _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      ((ProEtale.sheafExtendScalars
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T).mapHomologicalComplex (.up ℤ))
      (P.finiteTensorReduction m hm hmn T) h
      (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T)
      (finiteTensorCochainComparison
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T) C D
```

## New

```lean
def FiniteTensorCoreNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u})
    (h : (P.finiteTensorReduction m hm hmn T).CoreMonoidal) : Prop :=
  (finiteScalarTensorData
    (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T).Normalized h
```

The record's generic predicate is:

```lean
def Normalized (d : TensorRepresentativeData Q R QB S) (h : Q.CoreMonoidal) : Prop :=
  ∀ X Y, S X → S Y →
    d.source X Y = (h.μIso (R.obj X) (R.obj Y)).inv ≫ d.tail X Y
```

The declaration-level profile found 25 seconds in converting the generic scalar-core
result to the finite-level theorem; the clean whole item took 68 seconds. Form this
entire predicate in the abstract categories before finite-level specialization, so
that the conversion compares one shared predicate application. The whole uniqueness
argument remains in the item. This changes no factor or quantifier of the equation.

`finiteScalarTensorData` is constructed from exactly the original native maps:
its source is `Q.map (mu QA C D) ≫ c (C ⊗ D) ≫ QB.map (delta C D)`;
its tail is `(c C ⊗ₘ c D) ≫ mu QB (Fco.obj C) (Fco.obj D)`;
its target is `QB.obj (Fco.obj C ⊗ Fco.obj D)`.
Unfolding the record constructor gives the old entire representative square. There
is no dropped condition, changed arrow, additional hypothesis or weakened conclusion.
This definition is used indirectly by targets, so the target-meaning review is reopened
for this interface change; the equations remain definitionally the same.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | Only direct user of `FiniteTensorCoreNormalized`; prove the original existence/uniqueness assertion using typed projections. All public theorem signatures stay identical. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed (Y7 landed 2026-10-26) | Identify the constructed model with the chosen core by the same normalization and uniqueness; use native braided scalar transport. Public statement unchanged. |
| Sheaf.Paper.TensorRepresentativeData | new, J2 | Generic typed source factorization and tail, with actual common-target and source-composite methods. |
| Sheaf.Paper.FiniteScalarTensorData | new, J2 | Construct the actual scalar diagram with the original composites. |
| Sheaf.Paper.FiniteScalarTensorSource | new, J2 | Combine the recorded certificates generically. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | new, J2 | Named proved scalar representative certificate. |
| Sheaf.Paper.CochainLocalizationTensorIso | new, J2 | Named proved localization tensor certificate. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | new, J2 | Named proved ordinary cochain certificate. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | new, J2 | State the same fixed-candidate counit equation using the typed projections. |

The defining item and the symmetry consumer are the direct or implicit users of
this normalization property. The symmetry proof now explicitly names it when identifying
the constructed model with the chosen core. Other importers retain the original public
theorem signatures. No adopted `WeilConjectures` declaration changes.

## Status

landed 20261026T070008-L-3329438 2026-10-26 (merge of deliver/J2/Sheaf.Paper.FiniteTensorSignedReduction)
