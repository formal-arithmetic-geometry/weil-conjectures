## What changed

Replaced the original hole in `AlgebraicGeometry.schemeOrdinaryEvaluation_localization`
by a proof from one explicit component calculation. All existing signatures,
definitions and public imports are unchanged. Added proof-only imports of
`CanonicalTensorHomUncurryLocalizedEvaluation`, `KFlatResolution`, and
`SchemeOrdinaryEvaluationUncurryCalculation`.

Proved three-variable canonical naturality, a private extension of the representative
formula to arbitrary source complexes, and a private generic monoidal transport lemma.
The extension resolves its source by a K-flat complex, identifies the canonical witness
with the explicitly constructed uncurrying map on every tensor summand, applies proved
localized uncurrying naturality, and cancels the localized resolution. The main proof
applies this to the ordinary evaluation and unit maps and combines the resulting
identities by canonical naturality and monoidal transport.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.schemeOrdinaryEvaluation_localization`
(node `lem-pc-scheme-ordinary-evaluation-localization`), 1 of 1.

Added hole: `AlgebraicGeometry.schemeOrdinaryEvaluation_uncurry_calculation`
(node `lem-pc-scheme-ordinary-evaluation-uncurry-calculation`), in its own new module.
This is a decomposition, with one hole closed and one added, not a net decrease.
No sorry remains in the item's module, in a private lemma or in a definition.

Also proved `AlgebraicGeometry.schemeDerivedTensorHomEquiv_naturality`, and the
private `uncurry_representative` and `evaluation_transport` lemmas. The remaining
statement involves only explicit chain maps and the lax tensor comparison; it
contains no canonical derived tensor-Hom equivalence, Hom comparison or arbitrary
representative isomorphism. The nontrivial identification with the canonical family
and transport along the representative isomorphisms are proved in the item.

## No longer needed

No original import, node or module is pruned. The original Hom projection and derived
Hom dependencies remain used through the explicit component calculation and the
canonical model. The original two public imports remain required by signatures.
The abandoned prior base/transport/of_base wrappers are not delivered.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the original localization hole untouched and proved only
naturality, which did not satisfy the stage-3 delivery requirement. This delivery
closes that hole by implementing the representative-extension and categorical
transport steps, isolating only the actual component calculation. No new claim of
flatness or invertibility of an ordinary comparison is made. The unit record has
no realized nodes, and its route is unchanged.

## New nodes

`lem-pc-scheme-ordinary-evaluation-uncurry-calculation` records the single remaining
component calculation, its source, full proof plan, edge cases and actual Lean
statement. Its explicit uncurrying maps are constructed by the existing library,
with no choice of arbitrary data from an existence theorem.

`lem-pc-scheme-derived-tensor-hom-naturality` records the proved naturality consequence
of the canonical family's characterizing predicate, with its Lean statement verbatim.
No definition or interface change, forced adaptation or change record is needed.

## Second reading by K3

1. Compared the delivered localization module with the repository version. Existing
   declarations and signatures are unchanged; the only added declaration is the
   explicitly documented naturality theorem and the proof-only imports.
   **Verdict: pass.**
2. Compiled both delivered modules with `lcompile.py`. The localization target has no
   remaining `sorry`; the sole remaining hole is the named component calculation in
   `SchemeOrdinaryEvaluationUncurryCalculation`, with its matching node and proof
   docstring. No forbidden declarations or hollow definitions occur. **Verdict: pass.**
3. Checked the split statement against its component-map formulation and edge cases
   (zero complexes and the single-unit component). It is a strict, needed reduction
   and does not restate the target. **Verdict: pass.**
4. The proof uses the explicit canonical naturality, K-flat resolution cancellation,
   and localized uncurrying lemmas; all imports are used and no old proof dependency
   is pruned. The unit route and realized-node data are unchanged. **Verdict: pass.**
5. The target and split node metadata agree with the Lean declarations, including
   statement, proof dependencies, source, and blueprint. **Verdict: pass.**

Changed the private transport proof to use right-unitor naturality with the correct
associativity grouping; this repairs the original compiler failure without changing
   any public statement.
