## What changed

Proved `WeilConjectures.AdicQbarRealization.exists_tensor_reindexing_models` with its
original signature and public imports. The proof constructs the module equivalence,
transports arbitrary acyclic tensor tests through that equivalence, descends the
cochain tensor comparison through the supplied K-flat models, and constructs the
coefficient-unit comparison directly.

Added two proved helper modules, `Sheaf.CategoryTheory.SectionwiseTensorComparison` and
`Sheaf.Paper.AdicCochainTensorReindexing`. The first uses the existing presheaf
scalar-restriction tensorator and restriction/sheafification comparison, proves the
formula on pure sections, and derives naturality by the pure-section extensionality
lemma. The second applies the existing signed total-tensor construction and proves
the homogeneous generator formula by the coproduct summand equations. All new imports
of the item module are private proof imports. The ordinary helper publicly imports
the pure-section definition used in its statement.

No existing signature, definition, instance, public import or source-library module was
changed. The coefficient-sheaf and monoidal-category irreducibility attributes are
local to the proof files. The original node's proof route now matches the Lean argument.

Validation: `lcompile.py --all` passed without diagnostics. The ordinary helper,
cochain helper and item compiled in 12.1 s, 46.3 s and 18.8 s respectively, each
within the 60-second limit. The original item's theorem signature was compared
verbatim with the shared source and is unchanged.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.AdicQbarRealization.exists_tensor_reindexing_models`.

Also proved, with no holes:

- `SheafOfModules.sectionwiseTensorComparison`.
- `WeilConjectures.AdicQbarRealization.exists_cochain_tensor_reindexing`.

Holes closed: 1 of 1. Holes added: 0. Holes left in the delivered modules: 0.
No unfinished obligation has been split off. Existing library declarations are reused
with their current proofs; this report does not claim to close their independent holes.

## No longer needed

The original item had no private proof imports to remove. Its public import of
`Sheaf.Paper.AdicRealizationFamilyData` is preserved.

The following planned dependencies are unnecessary for this proof:

- `lem-pur-isomorphism-inverse-image-tensor-hom`, module
  `Sheaf.Paper.PurInverseImageTensorHom`: the prescribed ordinary tensorator is
  constructed directly from the proved scalar-restriction and sheafification API.
- `lem-sfb-exact-monoidal-equivalence-total-kflat`, module
  `Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat`: K-flatness follows
  directly by transporting each arbitrary acyclic test through the equivalence.
- `lem-pur-cochain-pullback-tensor-coherence`, module
  `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`: the existing generic total
  comparison and its summand equation provide the required chain map and normalization.

These dependencies are removed from this node's proof route, not withdrawn from the
library. Other consumers and all unit routes retain their existing obligations.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The generic monoidal-equivalence route in the DAG is
unnecessary: the sectionwise functor and inverse coefficient isomorphism permit a
more direct normalization proof, and exact equivalence suffices for the K-flat tests.
The actual unit formula uses `B.iso.hom` on coefficient sections, exactly as required
by `reindexUnitSections`; no separate realization-coherence assertion is used.

The zero-ring, empty-scheme and unbounded-complex cases require no extra hypothesis:
the ordinary comparison uses invertibility of the scalar map, totalization uses
coproducts, and acyclicity is transported categorically.

## New nodes

`lem-sf-sectionwise-tensor-comparison` records the proved ordinary tensor comparison,
naturality and pure-section formula. Its Lean module is
`Sheaf.CategoryTheory.SectionwiseTensorComparison`.

`lem-sf-adic-cochain-tensor-reindexing` records the proved total-complex comparison
and homogeneous pure-section formula. Its Lean module is
`Sheaf.Paper.AdicCochainTensorReindexing`.

Both are genuine parts of the original argument and both are proved. No change
record is necessary: this packet changes only the item's proof and its node and adds
these two proved helper modules with their nodes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.SectionwiseTensorComparison": "f4a17c48a968eb505a3ddda73fd1f6f97c3fc8b8", "Sheaf.Paper.AdicCochainTensorReindexing": "929e392d42d9e228219d2baa11a5bec9188da8ce", "Sheaf.Paper.AdicTensorReindexingModels": "25d76073b9a0b65a583b2523e237c442a6660f25"}, "results": {"Sheaf.Paper.AdicReindexingCore": {"hash": "1fbdf722b89e076b82fcc0dc369f866bd650b009", "status": "OK"}}, "seconds": 49, "time": "2026-10-28T05:45:19+0800", "transitive": 0, "version": 1}
```

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
