## What changed

Constructed the ordinary scalar tensor comparison in
`Sheaf.CategoryTheory.RingedScalarTensorComparison`: symmetry, inverse of the
existing normalized tensor cancellation, and the scalar ring's left unitor give
the module comparison. Its naturality is proved. The existing single-factor
bifunctor comparison lifts it to an isomorphism of unbounded complexes, without
flatness or K-flatness assumptions.

`Sheaf.CategoryTheory.RingedScalarTensorUnit` proves that this explicit comparison
preserves insertion of one. The proof checks the ordinary sheaf maps on pure
sections and the single nonzero tensor summand in each degree.

`Sheaf.Paper.AdicResidueQuotientTensorSuccessor` constructs the derived level
isomorphisms explicitly from the ordinary comparison, exact restriction's
`resFactors`, the inverse universal comparison on the K-flat complex, and scalar
extension of `eP`. Only the equality for one successor is left as a named theorem.

The assigned theorem now constructs the natural transformation using
`NatTrans.ofOpSequence`, makes it an isomorphism using the constructed component
isomorphisms, and proves its unit equations by the ordinary unit identity, the
normalization of `adicFiniteUnit`, inverse cancellation, and naturality along
`eP`. Its statement, universes, hypotheses, public import, and docstring are
unchanged. No existing module other than the assigned module is changed.

Validation: `lcompile.py --all` compiled all five files successfully. Individual
times were 26.5 seconds (ordinary comparison), 34.8 (pure sections),
19.7 (ordinary unit), 36.2 (successor statement and level construction), and
54.9 (assigned module). All are below the unchanged 60-second limit. Profiling
options and trace tactics were removed. The only hole is the named successor
theorem below.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Scheme.adicResidue_quotient_tensor_model` is reduced to one
strictly smaller successor identity. This is a decomposition, not a net hole
closure: one original hole removed, one new hole added.

Proved without new holes:
`CategoryTheory.ConstantCompletion.scalarTensorModuleIso_naturality`, the
construction `scalarTensorComplexIso`,
`CategoryTheory.ConstantCompletion.scalarTensorComplexIso_unit`, and the
construction `AlgebraicGeometry.Scheme.adicResidueQuotientTensorLevelIso`.
The assigned module contains zero `sorry`.

The only `sorry` in this delivery is
`AlgebraicGeometry.Scheme.adicResidueQuotientTensorLevelIso_successor`, node
`lem-sfb-adic-residue-quotient-tensor-successor`. It asserts an equality between
specified maps for a single successor. It neither postulates an isomorphism nor
asserts any unit identity. In particular, the proved ordinary comparison and
ordinary and derived unit calculations are not moved into this hole.

The constructions use an already proved tensor cancellation theorem with its
pure-section normalization. No data is selected from a new unproved existence
theorem, and there is no hole in any definition.

## No longer needed

The planned use of
`AlgebraicGeometry.Scheme.adic_constructible_finite_reductions` (node
`lem-sfb-adic-constructible-finite-reductions`) is unnecessary. Its theorem concerns
complete objects with Noetherian and constructibility hypotheses, whereas this
calculation needs the general scalar-comparison API in
`Sheaf.Paper.AdicFiniteReductionData` (node
`lem-sfb-adic-finite-reduction-data`). The item's proof dependencies now name the
latter API explicitly.

No original public import is removed. In particular,
`AdicConstructibleFiniteReductions` remains in the existing public import closure
through `AdicResidueLiftComparisons`; this delivery does not claim that the module
itself has been pruned. No existing module or node is withdrawn. No global module
pruning is claimed.

The specialized `QuotientTensorScalarTowerComparison`,
`PrincipalTensorScalarExtension`, `CompletedFiniteReductionTensorComparison`,
and `RingedKFlatSingleTensorComparison` were inspected. Their stated interfaces
use different coefficient packages or do not express the required scalar
adjunction normalization. They are not imported. The reusable generic
pure-section calculations come directly from `RingedTensorComplexConstraints`.
The proved formulas for the constructed comparison are in the new
`RingedScalarTensorSections` module, separating the expensive module-level
calculation from the complex-level unit proof to keep each file below 60 seconds.

## Where the brief, the DAG or earlier work was wrong

The original proof plan compressed three distinct calculations into one prose
step: ordinary tensor contraction, localization and unit normalization, and the
successor/counit comparison. Its declared finite-reduction theorem does not
supply them. This delivery implements the contraction and unit normalization and
isolates precisely the remaining successor equation with the explicit maps in
its statement. No statement is disputed or weakened.

The edge cases require no additional hypotheses: the ordinary proof uses the
same pure-section identities for zero rings and zero modules, and only the
(q,0) summand for every degree of an unbounded complex. The derived construction
uses K-flatness solely to invert the universal scalar comparison; it never
assumes a quotient is flat or perfect. The unit's integral-model route is kept.

## New nodes

`lem-sfb-ringed-scalar-tensor-comparison` records the constructed ordinary chain
comparison and its module naturality. It uses existing normalized cancellation
and the adopted single-factor totalization API.

`lem-sfb-ringed-scalar-tensor-sections` records the two proved pure-section
formulas used by the unit proof; it introduces no hole.

`lem-sfb-ringed-scalar-tensor-unit` records the proved ordinary insertion identity.
It has no derived category, K-flatness assumption, tower, or inverse limit.

`lem-sfb-adic-residue-quotient-tensor-successor` records the explicit K-flat level
comparisons and the remaining one-successor equality. Its docstring and node give
the balancing, restriction, scalar-counit and pure-tensor calculation to perform.

The searches were run through `msearch.py` with LeanFinder, Loogle, grep and
LeanSearch; their actual queries and results are recorded in each new node.
No shared interface was changed, so no change record or forced consumer
adaptation is needed.

The new source references were checked against the local Stacks tag table:
03EK is `sites-modules`, section-tensor-product; 03CZ is
lemma-adjointness-tensor-restrict; 06YY is `sites-cohomology`,
lemma-derived-base-change; and 099M is `proetale`, lemma-naive-completion.
The latest blueprint proof's clause that the reductions of K and Res(K)
coincide is the recorded ancestor place. Searching the current blueprint and
the library found no duplicate with the ordinary comparison and its specified
normalization.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
