## What changed

Proved `AlgebraicGeometry.exists_cover_nested_cartier_preparation` in
`Sheaf.AlgebraicGeometry.CoverNestedCartierPreparation`, with its statement and the canonical
`Scheme.coverGenericResidueAlgebra` instance unchanged. Six private proved helpers establish
finite residue fields over a field, the normalization lift on an open, dominance and the generic
field comparison for an isomorphism over a nonempty open, and the two-boundary blowup model.
No new public declarations, definitions, modules, or nodes are introduced.

The proof takes the prescribed normalization, uses normalization's normal-stalk and generic-field
APIs directly, and makes the boundaries Cartier by the two successive blowups in the plan.
The locally Noetherian complement-ideal theorem constructs both centers without separate
compact-open bookkeeping. Principalization and Cartier total transform give the two ideals;
comap support equations give their exact supports. Naturality of generic stalks supplies the
specified field-spectrum isomorphism, and normalizationDesc after open base change supplies the
map to the cover. Composition supplies the remaining morphism properties and factorization.
The item's DAG proof and proof dependencies now describe this argument.

Added private proof imports for the etale residue-field tool, open-immersion function-field
isomorphisms, and local Noetherianity. Removed the three unused private proof imports listed below.
No other module needs adaptation and no public interface changes.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.exists_cover_nested_cartier_preparation`
(node `lem-sfb-cover-nested-cartier-preparation`). Added zero holes; the item has zero remaining
`sorry`s. All six private helpers are completely proved. No split-off statements.

The proof uses the existing declaration
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`
(node `lem-sfb-integral-blowup-projective-geometry`) for both blowups; that dependency retains its
existing `sorry`, unchanged by this delivery. This is an item proof from the stated dependencies,
not a claim that its whole dependency closure is already axiom-free.

## No longer needed

Removed private imports:

- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`: only finiteness of the
  residue extension is required; the etale residue-field map and the unramified field theorem
  prove it directly. The discrete-topology and singleton-open conclusions are unnecessary.
- `WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension`: the item
  specifies the actual normalizationIn. Its integrality, normal stalks and prescribed generic-field
  isomorphism follow directly from the existing normalization APIs.
- `Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier`: the proof needs principalization and
  Cartier total transform, not the additional scheme-theoretic density and admissibility package.

Removed the obsolete `det-nagata-boundary-divisor-cartier` entry from `tool_uses`.
Corresponding dependencies removed from this node:
`lem-weil-pbc-etale-fibre-discrete-separable-points`,
`lem-weil-pbc-normalization-in-residue-field-extension`,
`det-nagata-boundary-divisor-cartier`. Also unnecessary here are
`lem-weil-pbc-qcqs-over-affine`,
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, and
`lem-sfb-noetherian-space-compact-subsets`: the locally Noetherian complement-ideal theorem
avoids the compactness/DCC detour. These nodes and modules are not withdrawn, since other parents
may use them. The two-blowup route and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or required interface repair was found. The plan's residue-field-normalization
lemma provides an existential normal model rather than the particular canonical normalization
required by this item; the library's normal-stalk and generic-field APIs handle that model directly.
The plan's compactness argument is unnecessary for the existing locally Noetherian complement-ideal
API. The proof works when either complement is empty (the complement center is the unit ideal),
when S = Tcirc, in dimension zero, and for nonnormal S and disconnected covers: no normality of S
or H or connectedness of H is used.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
