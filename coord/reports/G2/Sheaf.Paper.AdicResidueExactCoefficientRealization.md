## What changed

Proved `AlgebraicGeometry.Scheme.adicResidue_exact_coefficient_realization` with its
statement unchanged. The exact functor is constant module realization, ordinary
extension along `coefficientMap`, and slice restriction. All additional declarations
are proved private helpers in the item module; no other existing module is changed.
Removed this file's local irreducibility mark on `adicResidueQuotientModule` to
compare the slice objects by definitional equality.

The regular-module comparison is proved invertible using the tensor and
sheafification adjunctions and the coyoneda criterion. Its scalar equation follows
from naturality and linearity of those units. The quotient comparison has an
explicit inverse: the map sending b to b times the realized quotient generator
annihilates the projection kernel, and therefore descends through the projection.
The two inverse equations and the requested projection normalization are proved in
Lean. No Koszul or derived comparison is used for the coefficient calculation.

Read the current integral-model unit, Stacks `proetale.tex`
`lemma-naive-completion` (099M), and `sites-modules.tex`
`lemma-adjointness-tensor-restrict` (03EK) and
`lemma-sheafification-tensor`. Inspected the existing regular comparison in
`WeilCompletedRealizationRegular` and the descending inverse in
`CompletedConstantAlgebraFlatQuotients`; their scheme-specific signatures do not
specialize to the arbitrary coefficient-model universe here. The same ordinary
adjunction and kernel argument works on that small site and then restricts to U.
The zero ring, zero and unit ideals, and empty sites require no additional hypotheses.

Searches: LeanFinder returned module-flatness and sheaf-category facts, without
this normalized comparison; Loogle for `"extendScalars", "quotient"` returned no
hits; msearch grep and local ripgrep located the proved constructions above.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Scheme.adicResidue_exact_coefficient_realization`
(node `lem-sfb-adic-residue-exact-coefficient-realization`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The proof uses existing declared dependencies, including `flat_and_quotients`;
it does not claim to close their remaining transitive holes.

Validation: `lcompile.py` compiled the complete module in 28.2 seconds, with no
errors or warnings. The existing theorem statement was checked byte for byte
against the repository. There are no profiling options or lines over 100 characters.
The newly reached helper-import closure contains no additional `sorry` statements.

## No longer needed

Dropped `lem-route-ringed-internal-hom-restriction` from this node's proof
dependencies. Derived internal Hom restriction is unnecessary: the ordinary exact
slice restriction theorem `ringedOverFunctor_exactGeneral` is sufficient.
No direct proof import of the derived internal Hom restriction module is needed.
No existing import was removed, and no module is withdrawn.

Kept the statement import `AdicResidueQuotientTensorTower`. The proof imports are
`ConstantCompletionEquivalence` (including its private proved `change_exact`),
`ConstantRealizationDerivedScalarExtension` (constant-section identities), and
`RingedDerivedRestrictionGeneral` (ordinary exact restriction).

## Where the brief, the DAG or earlier work was wrong

The original DAG cited derived internal Hom restriction for a calculation entirely
in ordinary module sheaves. Replaced it by the existing exact slice restriction
API. The quotient comparison needs its actual normalization, so an abstract
existence of isomorphisms would be insufficient. The explicit descending inverse
proves that normalization directly. No statement or definition repair was needed,
and the unit route is preserved.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
