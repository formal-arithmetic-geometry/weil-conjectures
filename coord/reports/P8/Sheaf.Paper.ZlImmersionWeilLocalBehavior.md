## What changed

Reduced WeilConjectures.zlImmersionWeilLocalBehavior to the two genuine mathematical
clauses of the original argument: simultaneous normalized immersion restrictions,
and open extension relative to the supplied open restriction package. The Lean
proof combines their existential data and both original conclusion clauses.

Moved the original definitions and clause structures verbatim to the public
Sheaf.Paper.ZlImmersionWeilLocalData module, reexported by the assigned module,
to avoid circular imports of the two new statements. Names, universes, signatures,
visibility, fields and non-theorem constructions remain unchanged. The original
theorem statement remains unchanged. Change record:
coord/changes/P8-immersion-weil-clause-data.md.

## Proved and sorry left

Closed the original hole of WeilConjectures.zlImmersionWeilLocalBehavior by a
complete Lean combination. This is a decomposition, not a sorry-free proof.
The delivery adds two holes, each exactly `:= by sorry` in its own module:

- WeilConjectures.zlImmersionRestrictionAssembly,
  lem-zl-immersion-restriction-assembly: constructs only the two restrictions,
  shared local operators and Frobenius comparison data.
- WeilConjectures.zlOpenExtensionAssembly,
  lem-zl-open-extension-assembly: constructs only the open-extension clause from
  a supplied restriction package and its Frobenius normalization equation.

Both remaining declarations have the source and complete proof plan in their
docstrings and nodes. No sorry remains in the assigned module or a definition.
The source-set hole change is one closed and two added; no net reduction is claimed.

## No longer needed

No original mathematical proof dependency is pruned. The two clauses retain the
fixed-pair cohomology, residue-compatible pullback, open t-exactness and normalized
unit/empty-fibre routes. No module is withdrawn, no unit step is bypassed, and no
source-library declaration is removed. The unused original private imports were
removed from the assigned module and extracted data module:


- Sheaf.Paper.CompactSupportFiniteFieldIndependence
- Sheaf.Paper.IntegralPullbackComposition
- Sheaf.AlgebraicGeometry.ClosedPointField
- Sheaf.Paper.ConstructibleTruncations
- Mathlib.AlgebraicGeometry.ResidueField
- Mathlib.AlgebraicGeometry.Noetherian
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
- WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
- Sheaf.CategoryTheory.LocalizedModuleExactIndependent
- Sheaf.Paper.SfIntegralCompactSupportConstructible
- Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
- Sheaf.Paper.CompletedOpenExchangeTransport
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.Paper.IntegralPullbackCompletedComparison
- Sheaf.Paper.QcqsCompactSupportRealization
- Sheaf.SixFunctors.FrobeniusPointTransportNatural
- Sheaf.SixFunctors.IntegralOpenReductionComparison
- Sheaf.SixFunctors.OpenTensorNormalization


The original public imports remain available through the public data reexport.
The new statement modules import their signature dependencies; the open assembly
also records its existing proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The supporting interfaces use different normalized common-stage composition
presentations. Assembly of shared natural local operators and identification of
the supplied canonical comparisons remain substantial steps. The attempted
open-record assembly exposed a second normalization: coefficientQbarCohomology
has scalar-extended cohomology as its object, whereas the recorded stalk uses
realization followed by homology. These are canonically isomorphic, rather than
definitionally identical. The open assembly proof plan retains this transport.

The current blueprint source is in sec-deligne-laumon-general/sk-prop-wgen-relative-line;
the Restriction and Part 2 text there was read. Identity maps and empty sources
satisfy the stated constructions; no extra nonempty hypothesis was introduced.
There is no arbitrary data chosen from an unproved existence theorem inside a
definition: all existing constructions remain unchanged, and the parent only
eliminates existence in its theorem proof.

## New nodes

- def-zl-immersion-weil-local-data attaches the identical existing definitions
  and clause structures in the new data module.
- lem-zl-immersion-restriction-assembly owns original steps 1--6 and restriction
  exactness, without asserting an open extension.
- lem-zl-open-extension-assembly owns original steps 7--11 for the supplied open
  restriction data, without asserting construction of those restriction data.

The assigned node's proof and proof_deps follow the actual Lean combination;
its lean attachment retains only the theorem. The original statement, statement
dependencies and unit route are unchanged. The relocation change record is
coord/changes/P8-immersion-weil-clause-data.md.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
