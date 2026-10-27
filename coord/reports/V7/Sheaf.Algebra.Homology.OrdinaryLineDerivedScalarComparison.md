## What changed

Proved `SheafOfModules.OrdinaryLineScalar.exists_lineData` in the assigned module.
The proof obtains rank-one charts for all signed powers from the existing proved
signed-basis construction, extracts the normalized exact termwise comparisons from
`line_unbounded_derived_tensor`, and defines evaluation by the uniquely normalized
signed multiplication. It localizes the actual termwise cancellation, with its
component formula, to construct epsilon. Exactness, total associativity and the
single-factor collapse prove preservation of flat-term K-flat models.

Private proof imports expose the existing proved helpers of
`SignedLineScalarTensorTower`, `LineUnboundedDerivedTensor`, and
`ScalarHomOrdinaryTensorComparison`. The last supplies the already proved comparison
between monoidal and explicit site tensors and its pure-section formula. Existing
public imports, signatures and definitions are unchanged. Local proof inference
selection avoids a sheafification universe inference ambiguity in the proof glue;
private irreducibility annotations keep large tensor constructions from unfolding. The node records this
implementation and the additional comparison dependency.

## Proved and sorry left

Closed one of the four original holes:
`SheafOfModules.OrdinaryLineScalar.exists_lineData`.

Added zero holes. Three original holes remain unchanged, all attached to
`lem-pur-ordinary-line-derived-scalar-comparison`:

- `SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison`.
- `SheafOfModules.OrdinaryLineScalar.comparison_tower`.
- `SheafOfModules.OrdinaryLineScalar.comparison_identity_arbitrary`.

The existing proved `exists_presentations` and `comparison_identity` are preserved.
This is a partial proof delivery, with no decomposition.

## No longer needed

None. No existing import or dependency is removed. The other three unfinished
clauses still require their recorded plans. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The shortest implementation of the first three
steps reuses existing proved private local charts and localization helpers instead
of reconstructing them. In particular, the universal signed multiplication fixes
the evaluation uniquely; no arbitrary witness of a mere existence claim is used.
The construction covers zero and negative powers and imposes no bound on complexes.

Searches: LeanFinder returned ordinary module flatness lemmas; Loogle for IsKFlat
returned no hit; msearch grep and direct searches found the signed-basis charts,
line tensor comparison and total tensor associator used here.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
