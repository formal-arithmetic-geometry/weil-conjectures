## What changed

The proof of AlgebraicGeometry.Scheme.adicPerfectHomCohomologyComparison is assembled
from explicit ordinary quotient complexes, K-projective localization, and an ordinary
homotopy/cohomology calculation. Its statement and the existing tower definition are
unchanged. Its new proof import is Sheaf.Paper.AdicPerfectModelHomCohomology. Calls in the new
calculations and proof explicitly instantiate the scheme and coefficient universes;
this prevents inference through the noninjective maximum universe expression.

Sheaf.Paper.AdicPerfectReductionModels constructs the local completed complex, each
ordinary quotient complex, the actual successor scalar map and its ordinary balancing
isomorphism. An explicitly typed wrapper of the existing derived balancing
isomorphism prevents expansion of its inferred functor type. These definitions use actual functors and the proved cone equation; none
chooses an arbitrary object from an unproved existence assertion. A statement about
one complex records its K-projective quotient models and the compatible derived
computation counits.

Sheaf.Paper.AdicPerfectModelHomCohomology records the separate ordinary calculation:
homotopy-category Hom of those complexes is quotient algebraic Hom cohomology sections,
with compatibility on actual chain maps. It involves no derived Hom. The main proof
uses localization bijectivity and fullness of the homotopy quotient to represent an
arbitrary derived map, and proves that the counit squares transport the actual derived
successor to the ordinary scalar-balancing successor.

This is a decomposition, not a net hole reduction. Neither new statement alone
restates the assigned comparison: the first concerns one object and no Hom groups;
the second concerns ordinary homotopy classes and no derived localization. Their
combination uses a proved localization equivalence and a proved conjugation identity.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Scheme.adicPerfectHomCohomologyComparison
(node lem-sfb-adic-perfect-hom-cohomology-comparison), by a complete assembly proof.
The original module has zero remaining holes. Added exactly two holes:

- AlgebraicGeometry.Scheme.adicPerfectReductionModels,
  node lem-sfb-adic-perfect-reduction-models.
- AlgebraicGeometry.Scheme.adicPerfectModelHomCohomology,
  node lem-sfb-adic-perfect-model-hom-cohomology.

The scalar-step cone equation and all new definitions are complete. The existing
derived balancing isomorphism has a typed abbreviation; its value is unchanged. The private
modelHomEquiv, modelHomEquiv_map, and reduction_conjugation helpers are complete.
No axiom, hollow definition, or theorem-signature weakening is introduced.

Validation: all three modules compiled together in import order (12.4 s, 10.8 s,
16.6 s before removing development profiling and temporary inference helpers).
The delivery command recompiles the final files and runs the required preflight.
The sheafification instance adjustment is scoped to each theorem, following the
existing adic modules; it introduces no hypothesis or exported instance change.

## No longer needed

No existing public import is removed and no module is withdrawn. No node or module
is claimed globally pruned. The original eleven direct proof dependencies are now
organized under the two smaller intermediate calculations; they remain mathematical
dependencies of those calculations. The main node directly uses only
lem-sfb-adic-perfect-reduction-models, lem-sfb-adic-perfect-model-hom-cohomology and
the existing Mathlib leaf lem-coef-kprojective-derived-hom-bijection.

The existing IsPerfectRingComplex definition is not needed in the proof because the
statement already supplies the bounded finite-projective representative explicitly.
Its existing statement dependency is preserved. CompletedConstantSheafReduction,
AdicPerfectModelCompleteReduction, ConstantModuleKFlat and
PerfectConstantLocalChainRepresentative were searched but are not imported: the
available public comparison statements either impose extra hypotheses or only give
local representatives on a covering. The new local complex follows the target's strictPerfectConstantSheaf presentation;
the other completed-model API uses a different constant realization and would
require a further canonical comparison. No additional Noetherianity, completeness,
maximality or finite-residue-set assumption is made.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG described the ordinary
model computation and the ordinary Hom calculation in prose, but its existing
public dependencies did not already state their combined slice and successor
normalizations. These are now explicit smaller obligations, rather than treating
an arbitrary derived isomorphism as canonical.

The source checked is proetale.tex, Tags 09C5 and 09C6 (the displayed H_n calculation
and exact sections); the current blueprint integral-model unit route is preserved.
The new assertions were checked on zero complexes, a>b, the zero ring, the unit
ideal and the empty slice: all resulting Hom/cohomology sets are singleton, with
the unique maps. The construction also permits J=0 and non-Noetherian A.

## New nodes

- def-sfb-adic-perfect-reduction-model-complexes: actual termwise local and quotient
  complexes, the restricted coefficient transition, its proved cone equation and
  the uniquely normalized ordinary balancing isomorphism.
- lem-sfb-adic-perfect-reduction-models: one-complex K-projectivity and compatible
  derived computation counits, with source and full natural-language proof.
- lem-sfb-adic-perfect-model-hom-cohomology: ordinary homotopy Hom/cohomology sections
  and successor compatibility on chain maps, with source and full proof in words.

The item node is updated only in proof, proof_deps and proof_origin. No existing
statement or definition changes, so no change record or consumer adaptation is needed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
