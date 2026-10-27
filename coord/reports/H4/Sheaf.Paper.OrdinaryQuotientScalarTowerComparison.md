## What changed

Proved `WeilConjectures.ordinaryQuotientScalarTowerComparison` with its signature
and public imports unchanged. Six new proof-only modules hold fully proved
private helpers: `OrdinaryQuotientScalarModels`,
`OrdinaryQuotientScalarTowerLevels`, `OrdinaryQuotientScalarTowerConstruction`,
`OrdinaryQuotientScalarSectionCasts`, `OrdinaryQuotientScalarSections`, and
`OrdinaryQuotientScalarNormalization`.

The scalar systems package is built around the prescribed actual sequence scalar
cochain model, rather than comparing an arbitrary chosen model afterward. The
finite evaluation and balanced association isomorphisms then assemble, using the
existing successor theorem, into a natural strict tower isomorphism for all
complexes. The section calculation retains the actual evaluation scalar-action
equation, then uses adjunction-unit naturality and the presentation equation to cancel the presentation inverse against kappa.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ordinaryQuotientScalarTowerComparison`
(`lem-trf-ordinary-quotient-scalar-tower-comparison`).
No holes added, no split-off obligations, and no `sorry` remains in any delivered
Lean file. This is a proof from the existing project declarations, not an
assertion that every transitive dependency is axiom-free already.

## No longer needed

No original import is removed; both original public imports are preserved.
No existing declared proof dependency of the item is discarded.

The proof does not need the good-complex-only wrappers
`CoefficientExtensionRestrictedTower`'s public comparison theorem or
`CoefficientExtensionOrdinaryAssociationChain`. The former module is imported
only to reuse its proved private generic tower assembly and section-cast helpers;
the all-complex isomorphism is assembled directly here.
No use is made of `OrdinaryQuotientPullbackTowerConstruction`, any derived
cocycle/realization statement, or a derived-evaluation faithfulness assertion.
These are avoided routes, not withdrawn library modules or globally pruned nodes.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. Evaluation preserves scalar actions through its
ring-equality cast; this must be proved by rewriting that cast, rather than
asking unification to identify the actions. Small native-carrier lemmas prevent
repeated unfolding of these identifications.

The planned comparison between arbitrary
cochain-model choices is unnecessary: the scalar package can be constructed with
its cochain model equal to the actual prescribed one. The existing finite
successor theorem applies to every complex, whereas the public restricted-tower
wrapper is limited to good complexes. Its proved generic assembly argument
therefore supplies the all-complex construction without extra hypotheses.

The item theorem and target statements are unchanged. No existing definition,
instance, attribute, public import, or declaration signature is changed.

## New nodes

`lem-trf-ordinary-quotient-fixed-scalar-systems` records the fully proved private
construction of scalar systems around the prescribed sequence model, including
the tensor-section/unit identity.

`lem-trf-ordinary-quotient-scalar-tower-construction` records the fully proved
private assembly of the all-complex tower isomorphism and its component equation.

`lem-trf-ordinary-quotient-scalar-presentation-unit` records the fully proved
private presentation cancellation on quotient-unit sections. All six nodes
are implementation steps, with no new unfinished statement.

`def-trf-ordinary-quotient-scalar-tower-levels` records the explicit degreewise
finite comparison, natural in every complex.

`lem-trf-ordinary-quotient-scalar-tensor-normalization` records the forward finite
tensor formula, proved from the existing inverse-coordinate formula.

`lem-trf-ordinary-quotient-scalar-section-casts` records the fully proved
restriction-map section-cast identity. These elementary cast calculations are
kept separate from the presentation-unit calculation for the per-file compile
limit.

No change record is needed: there is no change to an existing statement or
public interface and no adaptation of another existing module.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.OrdinaryQuotientScalarModels": "731e6bf7b0cfceb3e19dc34e5e49b392f5459856", "Sheaf.Paper.OrdinaryQuotientScalarNormalization": "0a5c91d02e64e1470a32b629fe895a8767ee19f2", "Sheaf.Paper.OrdinaryQuotientScalarSectionCasts": "3e6c74e01cccbc5438f16e359e2186b6f869b3bf", "Sheaf.Paper.OrdinaryQuotientScalarSections": "f87ae24681b2f95f7c3abcbb601a771d9f0c73dd", "Sheaf.Paper.OrdinaryQuotientScalarTowerComparison": "7b7dd0e2b75d66514e34e32e773e86388af7ac86", "Sheaf.Paper.OrdinaryQuotientScalarTowerConstruction": "34fd4959a4b885153387891dd8d68a48e375ff98", "Sheaf.Paper.OrdinaryQuotientScalarTowerLevels": "09d2448549aebd289d68bfaf6e7113d5f41c8cde"}, "results": {}, "time": "2026-10-28T07:15:14+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
