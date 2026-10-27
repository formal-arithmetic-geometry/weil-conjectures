## What changed

`Sheaf.Paper.ScalarExtensionTowerCoherence` now assembles `quotientModels` from
`coefficientExtensionReductionModel`, strict association existence, and the existing
`square`. Both reduction-model choices use the given global unit on Y. A new proved
private helper `modelSection_hom_ext` conjugates ordinary finite evaluation by
`directEvaluation` and applies sheafified tensor-generator extensionality. Transposing
through the ordinary scalar adjunction and applying this helper proves uniqueness of
the association from its formula with outer coefficient one.

The new proof imports are `Sheaf.Paper.ScalarExtensionQuotientAssociation` and
`import all Sheaf.Paper.CoefficientExtensionOrdinaryStrictTensor`; the latter exposes
only the proved private tensor-generator lemma used by the proof. No existing
statement, definition, attribute, or public import changes.

## Proved and sorry left

One original hole is closed by decomposition: `WeilConjectures.ScalarExtensionTower.quotientModels`
(node `lem-pur-scalar-extension-tower-coherence`). Its assembly and uniqueness proof
are complete Lean. This is a decomposition, not a net proof of an original hole.

Two original sorries remain unchanged in the item:

- `WeilConjectures.ScalarExtensionTower.realizationModels`
- `WeilConjectures.ScalarExtensionTower.scalarExtensionTowerCoherence`

Both belong to `lem-pur-scalar-extension-tower-coherence`.

One new sorry is added:
`WeilConjectures.ScalarExtensionTower.quotientAssociation_exists`, in the new module
`Sheaf.Paper.ScalarExtensionQuotientAssociation`, node
`stage3-pur-scalar-quotient-association`. It constructs the association on fixed
strict representatives. It does not choose the reduction models, prove uniqueness,
or assert the geometric square or completed comparison equations. The combination
of these separate tasks is proved in the original theorem.

Actual holes: originally three; two in the delivered item and one in the new module.
Holes closed: one; holes added: one; net zero. No sorry occurs in a definition.

Both modules compile through `lcompile.py --all`; each is below the 60-second file
limit. Zero complexes, n=0, identity coefficient extension, and ramified coefficient
extensions use the same balanced association construction: neither the new statement
nor the uniqueness proof assumes flatness of finite quotient inclusions.

## No longer needed

No imports, declarations, nodes, or modules are withdrawn. The quotient-model proof
uses the existing reduction construction directly and does not need
`lem-pur-normalized-scalar-comparison-realization`, K-flat change of rings, or derived
limit descent. Those dependencies stay in the parent node because its other two
original realization/coherence obligations remain unfinished. The strict-association
construction itself is ordinary: it needs no completed or derived-limit comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan bundled strict quotient association with the stronger normalized
realization theorem. The already proved reduction-model construction and square
allow these tasks to be separated. In particular, uniqueness can be proved directly
by scalar adjunction and finite sheaf tensor generators, without waiting for the
completed realization equations.

The node `lem-pur-normalized-scalar-comparison-realization` names
`Sheaf.Paper.NormalizedScalarComparisonRealization`, whose source is absent from the
shared snapshot. This delivery does not assume that absent module exists and does
not remove its node: the remaining realization obligations retain that route.

The current blueprint places `def-weil-derived-pullback-tensor-hom` under
`sk-prop-sf-open-closed-triangle`, rather than the older `sk-def-sf-operations` path.
The new node cites the current `literature/blueprint/latest` location.

## New nodes

`stage3-pur-scalar-quotient-association` records the existence of the strict association
for fixed reduction data, with its finite adjunction construction and transition
gluing proof. It is strictly a constituent of `quotientModels`: model existence,
uniqueness, and the geometric square are outside its conclusion and are supplied by
the completed Lean assembly. The original node's proof and proof dependencies now
record that assembly. No change record is required because all existing signatures
and public definitions are unchanged.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
