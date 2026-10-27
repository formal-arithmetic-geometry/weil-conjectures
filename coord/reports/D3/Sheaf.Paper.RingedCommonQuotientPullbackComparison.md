## What changed

Proved `SheafOfModules.CommonQuotientPullback.nonempty_comparison`, preserving its
signature and all existing comparison, normalization, composition and identity data.
The ordinary insertion comes from the coefficient-restriction comparison and the
scalar-extension unit. Fully faithful whiskering along flat-term K-flat localization
constructs its derived insertion with the required representative square.

Moved the 32 existing data declarations verbatim into the publicly re-exported
`Sheaf.Paper.CommonQuotientPullbackData`. This lets independent ordinary, finite,
composition and identity lemmas use those data without importing their consumer.
This is a dependency-graph extraction, not a compilation-time workaround. No
WeilConjectures source or target statement is changed, and no existing consumer
requires adaptation. The change record is
`coord/changes/D3-common-quotient-pullback-data.md`.

The ordinary quotient lemma uses the already-stated ordinary common-quotient tower
comparison on both sites, transported through the proved coefficient comparison.
Adjunction units identify reduced insertion with the composite isomorphism. The
finite lemma transfers this through the normalized K-flat computation counits.
The two coherence lemmas prove the unreduced laws first; functoriality gives their
finite reductions. Unit and transition compatibility are naturality equations.

## Proved and sorry left

Closed the item's one hole:
`SheafOfModules.CommonQuotientPullback.nonempty_comparison`.

Also proved the new public lemmas:

- `SheafOfModules.CommonQuotientPullback.ordinary_insertion_reduction_isIso`;
- `SheafOfModules.CommonQuotientPullback.insertion_finite_isIso`;
- `SheafOfModules.CommonQuotientPullback.insertion_composition`;
- `SheafOfModules.CommonQuotientPullback.insertion_identity`.

There are zero `sorry`s in the delivery, including the extracted definitions and
all private helpers. Holes closed: one. Holes added: zero. No unfinished statement
is split off. This proves the item from the existing declared dependencies; it
uses the existing ordinary quotient-tower theorem rather than reproving that item.
No claim is made that all transitive dependencies are axiom-free yet.
The six-file packet is checked with lcompile in import order; every file has
zero holes, and the source-to-data relocation was compared verbatim apart from
blueprint docstring ownership. Each file stays within the 60-second compile limit.

## No longer needed

Removed these original direct proof imports from the item module:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`;
- `Sheaf.Paper.KFlatRingedToposPullback`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`;
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`;
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`;
- `Sheaf.Paper.RingedTopoiTensorComparisonData`;
- `Sheaf.Paper.FlatCommonQuotientReductionTower`;
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.

Their required K-flat and localization content is used through the coefficient
comparison and the independent finite/coherence lemmas. The proof does not use the
canonical ringed tensor-comparison construction/data or the general ringed derived
monoidal comparisons: scalar adjunction units supply insertion directly, and the
specified ModelIso computation squares suffice for coherence.

Removed the unused public imports
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` and
`Sheaf.Paper.RingedTopoiTensorSections`. The other three original public imports
are re-exported through the extracted data module rather than repeated in the item.
All 32 existing data declarations retain their names, signatures and bodies.

The new proof route does not use these original planned proof dependencies:
`lem-weil-pbc-canonical-ringed-tensor-comparison-construction`,
`def-weil-pbc-canonical-ringed-tensor-comparison`, and
`lem-sfb-ringed-derived-monoidal-comparisons`. No separate site-derived-tensor
descent theorem or geometric exactness presentation is used. Removed the obsolete
`tool_uses` entries for `lem-sfb-ringed-derived-monoidal-comparisons` and
`lem-trf-geometric-inverse-image-exact`. Original statement citations and all unit-level routes remain.
Flat-term K-flat localization also supplies representatives directly, so the derived
flat common-quotient tower theorem is unnecessary; only its already separate ordinary
quotient-tower dependency is used. This prunes
`lem-weil-pbc-flat-common-quotient-reduction-tower` from the proof route.

Comparing old and new transitive Lean imports of this item removes six modules:

- `Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation`;
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`;
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`;
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`;
- `Sheaf.Paper.FlatCommonQuotientReductionTower`;
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`.

The unit record `dag/units/sk-thm-properbasechange.json` realizes its statement
by torsion assembly and bounded-below base change, and its steps by projective-line
base change, reduction, prime base change and torsion assembly. The removed flat
common-quotient tower module is not one of those realized statements or steps.
Thus this change does not bypass a UNIT statement or step.

The original statement still cites the existing K-flat pullback construction and
section calculus, so those DAG statement citations are retained. No module is
withdrawn. Global target reachability remains the maintainer's ledger calculation.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The original plan describes local ideal and tensor
calculations that are already encapsulated by the ordinary quotient-tower statement.
Using that declaration and the coefficient comparison avoids repeating those
calculations. Unit/transition naturality and scalar extension of unreduced coherence
also avoid separate quotient-level diagram chases.

Edge checks for the ordinary lemma: it requires local surjectivity only, handles
zero quotient rings and zero modules, requires no flatness, and retains the actual
quotient-module action. Flatness is used solely for the two K-flat restriction
steps in the derived finite lemma. No coherence is assumed to prove finite
invertibility, and neither coherence lemma uses quotient invertibility.

## New nodes

`def-weil-pbc-common-quotient-pullback-data`: relocated definitions and computation
records, with no new mathematical assumption or existence assertion.

`lem-weil-pbc-common-quotient-ordinary-insertion`: the proved ordinary quotient
insertion isomorphism; no complex, derived or flatness hypotheses.

`lem-weil-pbc-common-quotient-insertion-finite`: the proved passage from ordinary
quotient insertion to invertibility of the specified derived reduction.

`lem-weil-pbc-common-quotient-insertion-composition`: the proved unreduced composition
law from ordinary section formulas, K-flat representative squares and localization.

`lem-weil-pbc-common-quotient-insertion-identity`: the proved unreduced identity law
from ordinary unitors and the same representative normalization.

All five have source references, proof steps, Mathlib search records and Lean
attachments. The existing item's node now records the actual construction and
these dependencies. Definition relocation is recorded in
`coord/changes/D3-common-quotient-pullback-data.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
