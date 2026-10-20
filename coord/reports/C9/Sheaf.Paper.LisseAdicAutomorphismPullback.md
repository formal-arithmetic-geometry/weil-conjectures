## What changed

Proved nine well-definedness and transport theorems in
`Sheaf.Paper.LisseAdicAutomorphismPullback`, preserving every public statement and
construction. Added a proof-only import of
`WeilConjectures.ConstructibleSheaf.Pullback` for preservation of finite local
constancy and its restriction comparison.

Private proved helpers construct the equivalence of pointed-neighbourhood categories,
prove naturality of the prescribed stalk isomorphisms, and transport a surjective
linear map with kernel `I • ⊤` through a commutative square of linear isomorphisms.
These give the integral lisse criterion and inverse-limit fibre comparison.
The coefficient-pair and algebraic object/fibre proofs use the existing specifications
and the localization construction directly.

Updated the existing definition node's proof, proof dependencies, and proof origin to
record the implemented argument and the four original unfinished existence clauses.
No public signature, definition body, target, or source-library file changes.

## Proved and sorry left

Closed 9 of the original 13 holes; added 0 holes and split off 0 statements.
All names below are in `AlgebraicGeometry.Scheme`.

Proved:

- `automorphismEtaleReindex_isSheaf`
- `automorphismModuleSheafPullback_isFiniteLocallyConstant`
- `automorphismModuleStalkIso_exists`
- `adicIntegralAutomorphismPullback_isLisse`
- `lisseRationalAutomorphismPullbackObjEq`
- `lisseIntegralAutomorphismFiberIso_exists`
- `lisseCoefficientPairAutomorphismPullback_inverts`
- `lisseAlgebraicAutomorphismPullback_obj`
- `lisseAlgebraicAutomorphismFiberAtStage_eq`

Original holes retained unchanged, all attached to
`def-wf-lisse-adic-automorphism-pullback`:

- `lisseRationalAutomorphismPullback_exists`
- `lisseIntegralAutomorphismScalarIso_exists`
- `lisseRationalAutomorphismScalarIso_exists`
- `automorphismLisseCoefficientTransformation_exists`

The retained holes have their original sources and natural-language proofs. This is
proof progress, not a decomposition into new holes. Single-file compilation is checked
with the required remote compiler; delivery also runs its independent preflight.

## No longer needed

No original import, DAG dependency, node, or module is pruned. The three public imports
remain verbatim. No additional scalar-comparison or coefficient-coherence dependencies
are introduced: the corresponding original holes remain in place. The explicit proof
import of the sites continuity module was removed because the retained pullback proof
import already exposes that API.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair. The original node was a definition with an
empty proof and proof-dependency list, while its Lean realization included thirteen
well-definedness theorems with holes. Its updated proof now distinguishes the nine
implemented clauses from the four original unfinished existence clauses.
The unit `sk-d-geometry` has no realized statement or proof steps to bypass.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
