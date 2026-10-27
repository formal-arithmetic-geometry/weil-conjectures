## What changed

Proved `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization`
in the assigned module. The statement and `internalEtaleRealization` construction are unchanged.
The proof constructs the restricted functor, proves fullness, faithfulness and essential
surjectivity, and identifies its ambient functor by reflexivity. It then explicitly composes
the bounded-below ordinary direct-image comparison with the conjugated derived encoding square.

Three proved private helpers translate etale constructibility/boundedness, resize ordinary
cover indices, and identify ordinary bounded constructibility with the existing fixed-module
etale-origin predicate. The cover-index argument is also used privately in
FiniteLocalizingSmoothLocalFormula and FiniteDiscreteSerreIndConstructible; it is elementary
bookkeeping, not another public mathematical notion.

Proof-only imports use the existing fixed-module descent, Tor comparison, intrinsic
constructibility, etale constructibility comparison, Plus compatibility, and encoding tensor
lemmas. `import all Sheaf.Paper.FiniteDiscreteEncodingCompactification` accesses its already
proved private `encodingDerivedPushforwardIso`, avoiding any new underived or derived square.
The public encoding import is narrowed from FiniteDiscreteOrdinaryEquivalence to
FiniteDiscreteOrdinaryEncoding; other unused public reexports are removed as listed below.
No statements, definitions, source-library modules, consumer modules or targets are changed.

Validation: the complete proof compiled remotely in 7.8 seconds before pruning; the cleaned
module compiled remotely in 9.2 seconds with no errors or warnings. The source import-pruning
consumer check passed (only an advisory about an identical proved private cover-index helper).
The new DAG dependencies were checked for paths back to this item; none forms a cycle.
Zero coefficients, empty schemes, a=b, identity maps and nonconstructible bounded-below inputs
are allowed throughout. No coefficient invertibility assumption was used. Searches through
msearch (LeanFinder, Loogle, grep) and local rg found the existing source route used here.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization`
(node `lem-sfb-finite-ctf-internal-etale-realization`).

Added 0 holes. There are 0 remaining `sorry` occurrences in the delivered Lean module;
all three private helpers are proved. No split-off theorem or new module is added.
Existing dependencies retain their own existing proof obligations.

## No longer needed

Removed proof imports:

- Mathlib.AlgebraicGeometry.Noetherian
- Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
- Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
- Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
- Sheaf.Paper.FiniteDiscreteEncodingNaturality
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- Sheaf.SixFunctors.OrdinaryProEtaleDirectImagePlusComparison
- Mathlib.Algebra.Homology.DerivedCategory.KInjective

Removed unused public reexports:

- Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence (replaced by its definition-only
  FiniteDiscreteOrdinaryEncoding import; the proof uses the individual encoding lemmas)
- Sheaf.Topology.ContinuousMapCondensedRing
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

The direct proof no longer invokes the nodes pqf-lem-locnoeth-lft,
lem-sf-module-object-ordinary-coefficient-equivalence,
lem-sfb-noetherian-global-constructibility, sk-thm-pe-constructible-comparison,
det-pe-finite-tor-comparison-noetherian, sk-def-sfb-module-pushforward-pullback,
def-weil-pbc-internal-abelian-sheaf-module-equivalence,
lem-sf-finite-discrete-encoding-naturality, def-weil-proetale-module-direct-image,
def-weil-pbc-sheafification, sk-def-sfb-module-derived-pushpull,
lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-sfb-ordinary-proetale-direct-image-plus-comparison, or
lem-weil-pbc-kinjective-hom-derived as direct proof dependencies. The underived and
K-injective arguments are already encapsulated in the proved encoding pushforward square.
The original statement dependencies are all retained, and encapsulated dependencies can
remain reachable transitively. No library module or source declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original route was mathematically valid but unnecessarily crossed into the
coefficient-sized site-model API. Existing fixed-scalar source declarations already match
the needed finite-stratification constructibility, all-module Tor tests and bounded-below
direct-image functors. Consequently no Noetherian-global-stratification conversion or
new K-injective argument is needed here. The claim that these dependencies are not yet
imported was historical: the assigned module already contained planned proof imports.

The updated DAG records the actual route. Its additional off-unit citations are generic
tools: fixed-module constructible sheaf descent and bounded derived descent, the derived
Hom bijection, the etale module constructibility comparison, and Plus/full compatibility.
The encoding tensor theorem is the existing all-encodings refinement of the original
coefficient equivalence; the encoding compactification module supplies only its already
proved private pushforward square, not its compactification theorem. These do not replace
any unit-level statement or step; the unit's realization lists are empty, and the finite
coefficient comparison/direct-image route remains the same. The original approved tool
entries no longer directly used were removed; no new maintainer approvals are asserted.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
