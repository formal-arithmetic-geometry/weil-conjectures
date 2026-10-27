## What changed

Replaced the proof of `AlgebraicGeometry.Etale.sfGraphSecondSideIso_projection`,
keeping its statement and the existing public import unchanged. Added a proof-only
`import all Sheaf.AlgebraicGeometry.CompactificationProjectionComposition` to reuse
its proved private proper-composition and proper/open projection calculations.
The repair also imports `Sheaf.AlgebraicGeometry.SfGraphProjectionWord` directly
with `import all`, so the endpoint helper explicitly unfolds the imported word
construction before applying functoriality of composition.

The proof first pastes those three constituent squares at the raw pullback
coefficient. Three derived-pullback associativity identities identify the final
coefficient with the canonical coefficient of the second graph presentation.
Naturality then transports the pasted square to the prescribed endpoint.
Private categorical and coefficient-transport helpers are fully proved. The
calculation is generic in the coefficient category and is then specialized to
module sheaves, avoiding expansion of the concrete module-category instances
during kernel checking. A private natural transformation constructs its three
comparison factors explicitly; it is identified with the specified graph-side
isomorphism at the specialization.

Updated the item's existing DAG node in `proof`, `proof_deps`, and `proof_origin`
to record this route, including the explicit graph-word endpoint normalization
and its existing definition node. No definitions, public signatures, consumers, or source
library files were changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.sfGraphSecondSideIso_projection`
(node `lem-sf-graph-second-projection-square`).

Added zero holes and zero split statements. No `sorry` remains in the delivered
Lean module. This is a proof, rather than a decomposition. The final full-file `lcompile.py` check passes without errors or warnings in
31.3 seconds. The proof now refers directly to the real imported
`sfGraphProjectionWord` declaration, rather than a copied local definition.

## No longer needed

The original proof dependencies below are not needed by this proof:

- `lem-sfb-ringed-projection-tensor-composition`
  (`Sheaf.Paper.RingedProjectionTensorComposition`): use the proved concrete
  proper-composition calculation instead of the ringed-site wrapper.
- `lem-sfb-ringed-derived-monoidal-comparisons`
  (`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`): only derived-pullback
  compositor associativity is needed for the coefficient path; the existing
  source-library coherence theorem supplies it directly.
- `lem-sf-etale-proper-open-tensor-square`
  (`Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare`): use the already proved
  mixed projection calculation in `CompactificationProjectionComposition`.

None of these imports was present in the original item module, so no existing
import was removed. No module or declaration is withdrawn. The unit's graph-side
step is preserved.

## Where the brief, the DAG or earlier work was wrong

The previous repair relied on `rfl` across an imported definition, but its scratch
check copied that definition into the same file. That did not reproduce the
module boundary in the global build. The global build therefore exposed the
same failure again. This repair imports the defining module directly with
`import all` and explicitly unfolds `sfGraphProjectionWord`. It removes the
fallback and every obsolete iso-expansion simp argument. The public statement,
canonical coefficient path, and mathematical proof route are unchanged.

No mathematical statement correction, new node, or change record is needed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
