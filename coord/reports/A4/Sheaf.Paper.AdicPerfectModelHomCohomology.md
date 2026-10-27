## What changed

The original statement of AlgebraicGeometry.Scheme.adicPerfectModelHomCohomology
is unchanged. Its proof now constructs the homotopy/cohomology equivalences and
proves their successor equation. The new proof import AdicPerfectHomCochains isolates
the evaluation of ordinary Hom cochains, before taking cycles or boundaries.

The private scalarHomMap applies ordinary scalar change to each cochain and
conjugates by the actual source and target balancing isomorphisms. Its chain-map
law follows from the signed Hom differential identities. The private
homologyHomEquiv removes the zero shift in Mathlib's homAddEquiv. Its class formula
and scalar naturality are proved explicitly using the kernel inclusion and the
homology projection. The final proof applies homology to the cochain comparison
square and uses the naturality of the exact-functor homology isomorphism.

ConstantModuleSectionProperties is imported privately with `import all` to use its
already proved general exactness helpers. The public theorem there also states
tensor and flatness properties under Noetherianity; its private exactness proofs
work for arbitrary commutative rings and any small site. No source-library file
or existing definition is changed, and no consumer adaptation is needed.

Validation: lcompile.py --all compiled both delivered modules without errors or
warnings: AdicPerfectHomCochains in 11.0 seconds and
AdicPerfectModelHomCohomology in 16.2 seconds. The original theorem's signature
matches its existing node attachment verbatim; both delivered modules satisfy
the 100-character line limit.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.adicPerfectModelHomCohomology
(node lem-sfb-adic-perfect-model-hom-cohomology), by the complete assembly proof.
The assigned module has zero remaining holes.

Added one hole, exactly the whole proof of the public theorem
AlgebraicGeometry.Scheme.adicPerfectHomCochains
(node lem-sfb-adic-perfect-hom-cochains), in its own new module. This is a
decomposition: one original hole closed, one chain-level hole added, net zero.

The remaining assertion is strictly the evaluation step: a comparison of ordinary
abelian-group complexes, with its equation on all cochains. It involves neither
homotopy-category morphisms nor cohomology and assumes no weak contractibility,
no bounds on Q, and no projectivity of Q. It does not rename the original
homotopy/cohomology assertion. The assembly separately proves descent through
cycles and boundaries, removes the zero shift, applies exactness of constant
sections and proves that the resulting equivalences respect the actual successor.
All definitions and private helpers are proved; no data is chosen from an
unproved existence theorem in a definition.

## No longer needed

No existing public import is removed, and no module is withdrawn or claimed
pruned from the targets' import closure.

The direct proof dependency
lem-weil-pbc-proetale-weakly-contractible-evaluation-exact is not needed: the proof
only evaluates constant module sheaves, whose sections are already exact on
arbitrary small sites. The original weak-contractibility hypothesis is preserved
verbatim. The supplied bounds and finite-projectivity of Q are also unnecessary
for the calculation; its signature is preserved.

The dependencies lem-pur-site-constant-module-hom,
lem-weil-pbc-site-constant-restriction,
lem-sfb-adic-constructible-finite-reductions,
def-sc-module-total-hom-complex and
def-sfb-adic-perfect-reduction-model-complexes now occur in the lower cochain
calculation. They remain needed there; none is claimed globally pruned. The main node records only the cochain comparison,
the existing constant-section properties and exact-functor homology comparison as
direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement was weakened or disputed. The DAG's exact-evaluation step was more
general than necessary: exactness on constant module sheaves suffices, and its
existing proof has no Noetherian hypothesis. The lower comparison has been checked
on P=0, empty degree intervals, arbitrary unbounded Q, J=0, J=top, the zero ring
and the empty slice. Its degreewise Hom product has finite support because P is
bounded, regardless of the size or boundedness of Q. Scalar-change conjugation
uses the actual adicPerfectQuotientStep maps throughout.

The source read is proetale.tex, Tag 09C6, especially the displayed total-Hom
calculation, together with Tag 09C5 and the existing constant-module Hom and scalar
balancing declarations. The current blueprint integral-model unit route is kept.

## New nodes

lem-sfb-adic-perfect-hom-cochains states the ordinary cochain evaluation comparison
with successor compatibility in every degree. Its source, natural-language proof,
three kinds of Mathlib search and verbatim Lean attachment are recorded. It is the
evaluation step of the existing node, with cohomology and homotopy-category descent
removed. The existing node changes only in proof, proof_deps and proof_origin.
There is no change record because no existing statement, definition or public
import changes.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
