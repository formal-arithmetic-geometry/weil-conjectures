# WeilConjectures.OpenTensorQuotient.openQuotientScalarSectionCompatibility

## Reason

Withdraw the false unused universal normalization claim, rather than assume its
conclusion. Its `finite` argument is an arbitrary natural isomorphism. At an odd
residue characteristic, postcomposing any normalized comparison with the natural
negation automorphism gives another permitted comparison, but changes the image
of every nonzero extension generator to its negative. For example, use the
identity open over a nonempty point and a nonzero constant module at l = 3.
Invertibility and naturality alone do not select the required normalization.

The replacement is a complete normalized existence proof in
`Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData`, already landed and independently reviewed.
The private proved helper `normalizedFinite` specializes the generic
`openScalarComparison` to each completed coefficient projection. The operations'
projection equation supplies its ring square. Its generator equation, cancelled
with the inverse comparison, proves the finite section equation. The public
constructor selects the normalized comparisons and their section equations
together with `choose finite sections`, then packages the two fields. This construction retains the actual
normalized generator equation needed by the scalar-unit proof. It does not choose
a witness from an unproved theorem: `normalizedFinite` is fully proved.

The route was already adopted in reviewed landing 20261028T020709-L-2538604
(change record `open-quotient-finite-scalar-route.md`). This packet reconciles
that route with withdrawal of this remaining obsolete auxiliary statement,
updates the parent proof record, and reconciles the withdrawal with that complete
replacement argument and the current sources. No Lean change to the already
proved constructor is needed, and none is delivered.

A structural scan of all DAG node files found no reference to the withdrawn node
in current `stmt_deps`, `proof_deps` or proof-step `uses`. Its former parent is
`lem-sf-open-quotient-scalar-compatibility-data`; the reference remaining in that
node's `statement_change.old_proof` is historical only. No unit `realized` entry
names it. `coord/rework.tsv` has no quarantined modules or parents. Searching all
Lean sources found no importer or declaration caller; `tools/downstream.py`
reports zero downstream modules and only the declaration's own occurrence.
Thus there is no consumer to weaken or adapt. The unit's statement and steps,
all source-library declarations, and all target signatures and definitions stay
as they are.

## Old

```lean
theorem openQuotientScalarSectionCompatibility
    (o : IntegralOpenReduction.Operations l E j)
    (finite : ∀ n : ℕ,
      IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
        scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o) :
    ∀ (n : ℕ) (M : normalizedDVRModules l E U n) (V : X.ProEt)
      (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      ((finite n).hom.app M).val.app (op V)
          (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
        IntegralOpenReduction.extensionSection l E j o
          ((scalarReductionRestriction l E U n).obj M) V a x
```

## New

The item is withdrawn through `deleted.txt`; the delivery tool leaves an empty
`module` stub with no declarations. Its DAG node is retained unchanged as to its
statement and history, with `lean: null`, no proof steps or proof dependencies,
and a proof-origin explanation of the false claim and the replacement argument.

The existing parent theorem and its proved helper remain unchanged:

```lean
  classical
  choose finite sections using normalizedFinite l E j o
  exact ⟨{ finite := finite, sections := sections }⟩
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility | A2 | Withdraw false unused theorem; preserve its node without a Lean attachment. |
| Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData | unclaimed | Lean unchanged. Its already reviewed complete direct normalized existence proof needs no section helper. Update its existing DAG proof record to reconcile withdrawal with this replacement argument. |

There are no direct or indirect Lean importers of the withdrawn module, and no
external occurrences of its declaration name. No forced adaptations are needed.

## Status

landed 20261028T055559-L-768117 2026-10-28 (merge of deliver/A2/Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility)
