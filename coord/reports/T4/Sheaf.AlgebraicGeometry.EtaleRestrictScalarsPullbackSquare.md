## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare`, without changing its
public statement or definitions.

The proof follows the existing node's two steps. First, adjunction conjugation
identifies the coefficient comparison of a composite with the two individual
comparisons. Applying this identity along both paths of the commutative square
and cancelling a composition isomorphism proves the underived identity. Second,
a generic, fully proved argument transports this identity through the homotopy
category and its derived localization. It uses the existing factorization
identities for exact derived composition and natural isomorphisms.

Added two proof-only imports:
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison` supplies
`pullbackSquareComparison_hom_app_factorsh`, and
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical` supplies the
homotopy-category whiskering identities. Every helper is private and proved;
no public interface was added. Abstracting the homotopy/derived transport avoids
expensive normalization of concrete étale functors. Local compilation stays within the existing 60-second limit. The helper
binders and instance assumptions are local to their declarations; the static
interface comparison reports no changes.

## Proved and sorry left

Closed:
`AlgebraicGeometry.Etale.pullbackSquareComparison_restrictScalars`
(node `lem-sbc-restrict-scalars-pullback-square-comparison`).

One original hole closed. No holes remain in this module, no new holes were
added, and no theorem was split off. Existing imported declarations are used as
provided; this delivery does not claim to discharge their separate obligations.
The theorem's original signature and visibility are unchanged.

## No longer needed

None. No original imports were removed. Both existing proof dependencies,
`lem-sbc-canonical-restrict-scalars-functor-comparisons` and
`sbc-def-base-change-map`, remain necessary. The proof follows the original
DAG route, so no node or module is pruned and no node update is needed.

## Where the brief, the DAG or earlier work was wrong

No statement or mathematical step was wrong. The composition and exact-derivation
steps can both be implemented from existing adjunction and derived-category APIs;
no further split is necessary. One implementation detail matters: mapping a
composite functor to the homotopy category is not definitionally the composite
of the mapped functors. The proof inserts the canonical composition
isomorphisms and uses their identity component equations.

## Second reading by T4

1. **Delivered interfaces.** Compared the delivered module with the repository
version. The public theorem signature and all existing declarations are unchanged
byte for byte; only proof-only imports, private helpers, the theorem proof, and a
clarifying docstring phrase changed. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py` (38.2 seconds),
with no errors or warnings, no `sorry`, and no forbidden declarations. Axiom
printing for `AlgebraicGeometry.Etale.pullbackSquareComparison_restrictScalars`
gives only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Split statements.** The delivery adds no public theorem, no `sorry`, and no
DAG node. The private helper lemmas are proof-local reductions, and searches found
no duplicated library theorem or hidden split-off obligation. Verdict: pass.
4. **Route and pruning.** The proof realizes the node's composition and derived
transport steps. Both added imports are plain proof-only imports and are used by
the proof; no original import or proof dependency is redundant. Verdict: pass.
5. **DAG agreement.** The node's statement, `proof`, `proof_deps`, and
`proof_origin` remain consistent with the implemented argument, and the unit route
is preserved. No unit realization or node metadata needs updating. Verdict: pass.

Changed after this reading: added this review record only; no Lean or DAG repair was
needed.
