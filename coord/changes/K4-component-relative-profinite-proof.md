# AlgebraicGeometry.ProEtale.component_relative_profinite_site proof elaboration

Group: K4. Item: `Sheaf.Paper.ComponentRelativeProfiniteSite`. Date: 2026-10-21.

## Reason

The existing theorem `AlgebraicGeometry.ProEtale.component_relative_profinite_site`
now has a complete proof. Its signature, all five existing definitions and their
bodies, and every public import are unchanged. No target statement changes.

## Old

The original elaboration settings after `@[expose] public section` were:

```lean
set_option autoImplicit false
```

The existing theorem ended with `:= by sorry`. Its signature and the existing five
real definitions remain verbatim; this record does not change them.

## New

The corresponding settings now are:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

The item module adds private proof helpers and sets
`backward.isDefEq.respectTransparency.types` to `false` and
`backward.defeqAttrib.useBackward` to `true`. Individual proofs also use
`backward.isDefEq.respectTransparency false`. These elaboration options permit the
Mathlib comparison APIs to recognize the concrete morphism-property slice and
forgetful-functor expressions. They affect elaboration of this file, not the
exported statement or definitions. The private helpers establish the mapping
property, finite clopen-stage comparison, limits, coproducts, and finite-test
comparison used in the final proof. They introduce no public signatures.

Three new public, fully proved results are added in new Sheaf modules:

- `Sheaf.AlgebraicGeometry.StalkIsomorphismLifting`:
  `AlgebraicGeometry.Scheme.existsUnique_lift_of_stalkMap_isIso`;
- `Sheaf.Topology.RelativeFiniteProfinitePresentation`:
  `Profinite.exists_relative_finite_presentation`;
- `Sheaf.Topology.ProfiniteFunctorExtension`:
  `Profinite.functor_iso_of_finite`.

Each has its own new DAG node, source, proof in words, and recorded Mathlib
searches. None has a hole, and none changes an existing definition. The item node's
`proof`, `proof_deps`, and `proof_origin` follow the implemented route. Other
existing node fields are preserved.

## Users

`tools/downstream.py ... --uses` lists ten transitive importers, recorded below;
the three direct textual users mention only unchanged declarations. Claim holders
were read from the current coordination records on 2026-10-21.

The item is held by K4. No other existing module is changed, so no consumer
adaptation is necessary. Importers continue to see exactly the existing item
interface. The source library under `WeilConjectures` is untouched.

Validation: all four delivered modules compile through the mandated compile
service without holes or warnings; the final item check took 4.8 seconds. Text
comparison verified the existing theorem signature, definition bodies, and public
imports. The first delivery preflight passed compilation and required this record
for its conservative command-level interface check. Independent review can check
the same unchanged interfaces and the three new proved statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ComponentRelativeProfiniteSite | K4 | Complete proof; elaboration settings and private helpers. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | P2 | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | E3 | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | P4 | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StalkIsomorphismLifting | K4, new | New proved general lifting theorem. |
| Sheaf.Topology.RelativeFiniteProfinitePresentation | K4, new | New proved relative presentation theorem. |
| Sheaf.Topology.ProfiniteFunctorExtension | K4, new | New proved finite-test extension theorem. |

## Status

landed 20261021T140831-L-2759703 2026-10-21 (merge of deliver/K4/Sheaf.Paper.ComponentRelativeProfiniteSite)
