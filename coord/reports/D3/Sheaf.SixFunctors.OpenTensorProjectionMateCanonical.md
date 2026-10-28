## What changed

Replaced the proof hole in
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`
with the resolving-pair calculation specified by the existing node. All public
signatures, definitions and public imports are unchanged.

Private proved helpers establish preservation of flat modules and K-flat
complexes by F, the cochain adjunction identity on each total-tensor summand,
the localized unit and hom-equivalence formulas, and generic cancellation of
the comparison isomorphisms. The main proof combines
the cochain identity with `restrictionModel.derived`, naturality of the fixed
simultaneous tensor comparison, and naturality of the restriction isomorphism.
The two BothModel hypotheses supply the final replacements of the one-flat
comparisons. Exactness and symmetry handle the acyclic tests; no object is
chosen from a postponed existence theorem.

Added private proof imports for the existing flatness/site tensor API and the
complex monoidal instances. Locally irreducible annotations keep the derived
category, factorization, canonical mate and total tensor definitions behind their APIs;
no public attributes
change. Updated the item's proof description to record the implemented steps.

Sources read: Stacks `sites-cohomology.tex`, Tag 0GL1,
`lemma-j-shriek-and-tensor`; `sites-modules.tex`, Tag 0E8I,
`lemma-j-shriek-and-tensor`. The current blueprint unit's route is retained.

The recorded LeanFinder search returned derived adjunction factorization
lemmas, with no matching tensor-model computation. Loogle found
`Adjunction.homEquiv_unit`; Mathlib grep found the localization unit and
hom-equivalence naturality APIs used here. Local searches found specialized
projection formulas on different categories, not this normalization identity.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`
(node `lem-sf-open-tensor-projection-mate-canonical`).

No holes added or split off. No `sorry` remains in the item module.
The conclusion is derived directly from the existing model data.

Validation: the item compiles cleanly through `lcompile.py` in 53.0 seconds
with no errors or warnings. Both existing public signatures were compared with
the current source and are unchanged; all Lean lines fit the 100-column limit.

## No longer needed

None of the existing public imports or declared proof dependencies is removed.
The three steps of the implemented plan are all needed. No module
or node is withdrawn. The added generic flatness and tensor helpers are used
only as tools; they do not replace a step of the unit's route. Specifically,
`lem-weil-pbc-independent-bounded-flat-kflat` supplies the proved `flat_to_cat`
and `tensorPreadditive` API, and
`lem-weil-pbc-independent-sheaf-tensor-colimits` supplies the proved
`siteSheafTensorRightIso` and independent tensor instances. No declaration in
this unit duplicates those general module-sheaf constructions.

## Where the brief, the DAG or earlier work was wrong

No new statement defect found. The recent repair adding the simultaneous-model
agreement and the flat-term K-flat hypotheses on C is used: F(C) is proved to be
a resolving complex before applying `restrictionModel.derived`, and both supplied
comparison families are identified with the fixed models. The former arbitrary-
comparison statement is neither used nor restored.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorProjectionMateCanonical": "97855b060c82e68476f6001bed2fef9c8566baeb"}, "results": {"Sheaf.SixFunctors.OpenTensorProjectionMateResolving": {"hash": "96831495c8feae0ca52458de34567e05caee1771", "status": "OK"}}, "seconds": 91, "time": "2026-10-28T14:56:24+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
