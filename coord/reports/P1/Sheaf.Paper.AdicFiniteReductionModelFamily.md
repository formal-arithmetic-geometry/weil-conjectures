## What changed

Replaced the body of
`AlgebraicGeometry.Scheme.adicResidue_finite_reduction_model_family` with algebraic
reconstruction and composition of actual finite-level isomorphisms. Its signature,
existing public import and docstring are unchanged. Added private proof imports of
`AdicResidueStalkTowerFamily`, `AdicResiduePerfectReductionComparison`,
`DerivedLimitExistence` and `DerivedLimitProducts`.

Local coefficient-universe sheafification instances avoid the ambiguous general
sheafification instance in these independent-universe signatures. The comparison
proof specifies the standard slice localizations in both ring-sheaf presentations.
These instance choices are local to the new modules; the assigned module adds no
instance commands.

The private proved helper `adicResidueAlgebraTower_model` constructs a Roos triangle
using the existing countable-product and derived-limit existence theorems, applies
`DerivedCategory.rlim_perfect_complete`, extracts a bounded finite-projective
representative, and composes its marking with the projection-induced reduction
isomorphisms. The main theorem retains the covering and applies exact finite constant
realization to these algebraic isomorphisms, composing with the two geometric comparisons.

Added the actual data interface `AdicResidueAlgebraTower` and the functor
`adicResidueFiniteConstant` in a new module. Algebraic derived categories use the
existing small Grothendieck localization; the sheaf target is the original standard
localization. Neither is selected from an arbitrary existence statement.

The scalar/slice comparison is written from existing proved helpers, rather than
left as a second hole. The remaining geometric extraction is a decomposition. In
particular, the extraction leaf assumes no J-adic completeness of A, returns only
quotient-ring towers, and constructs no bounded projective complex over A. The
comparison leaf concerns a supplied perfect complex, with no M, residue, lissity,
covering or completeness hypothesis. Neither leaf is the original theorem under
another name.

## Proved and sorry left

Original hole closed in the item:
`AlgebraicGeometry.Scheme.adicResidue_finite_reduction_model_family`
(`lem-sfb-adic-finite-reduction-model-family`). The private reconstruction helper and
the proof combining the two leaves are complete. There are zero textual holes left
in the assigned module (one initially).

One hole added as a whole public named theorem proof in a new module:

- `AlgebraicGeometry.Scheme.adicResidue_stalk_tower_family`
  (`lem-sfb-adic-residue-stalk-tower-family`), in
  `Sheaf.Paper.AdicResidueStalkTowerFamily`.

`AlgebraicGeometry.Scheme.adicResidue_perfect_reduction_comparison` is written without
sorry. It compares the strict-perfect constant presentation with exact commutative
constant realization, uses bounded-flat K-flatness on the site and slice, balances
the coefficient map with the n-th projection, and uses uniqueness of the algebraic
scalar left adjoint and its K-flat representative computation.

Count: one upper hole closed, one lower hole added, net zero holes closed.
This is a decomposition and is not reported as net proof progress. The remaining
leaf has a complete proof in words, source and DAG node. The new data module has
zero holes. No definitions or instances contain sorry.

Validation: `lcompile.py --all` compiled all four modules successfully: the data module
in 8.0 s, the proved comparison in 36.1 s, the extraction statement in 11.0 s, and
the assigned module in 15.0 s. The remaining style warning in the assigned helper
was corrected by changing `letI := hprod` to `let := hprod`, and a prophylactic
instance-priority command was removed from the assigned module. Delivery rechecks
the resulting file. The local coefficient-instance priorities remain in the new modules.
The assigned theorem's statement was checked byte-for-byte against the shared source.
All Lean lines are at most 100 characters, each new statement matches its Lean
attachment, and the proof-dependency arrays equal the unions of their proof steps.

## No longer needed

No existing public imports were removed, no module was withdrawn, and no existing
mathematical dependency is claimed pruned. The original plan's completion,
finite-reduction, nilpotent-lissity, connected-constancy, stalk, localization and
weakly contractible-cover dependencies remain needed under the extraction node.
Countable products, derived-limit existence and perfect reconstruction are used
directly by the reconstruction helper.
The original node's immediate proof dependencies are updated to the actual three
steps of the Lean assembly. Neither compatible local markings nor completeness of
the slices is needed for this item.

## Where the brief, the DAG or earlier work was wrong

The general mathematical route is retained. The older
`FinitePerfectAdicAlgebraTower` and `finitePerfectModels_adic_realization` interfaces
use `AdicCoefficientDatum`, which assumes finite quotient sets. That hypothesis is
absent here, so those interfaces cannot directly supply this item for arbitrary
Noetherian A. The new tower uses only an ideal and actual scalar adjunctions; the
existing general `rlim_perfect_complete` supplies reconstruction without finite
quotient sets. No source-library declaration, target, consumer or unit route changes.

Checked the proposed leaves on J = 0, J = top, the zero complex, the zero ring and
empty charts: the scalar comparison remains the same tensor identity; extraction
uses the empty covering when necessary. A need for the independent coefficient-site
and localization transports is retained explicitly in the extraction proof plan,
rather than assuming that the original fixed-universe etale stalk interface is
definitionally equal to these models.

## New nodes

`def-sfb-adic-residue-algebra-tower` records the normalized algebraic quotient-tower
data and exact finite constant realization on an actual slice. Source: Tags 09C6,
09AW, 093J and 03DJ. The algebraic localization is the existing Grothendieck one.

`lem-sfb-adic-residue-stalk-tower-family` isolates the geometric part before
algebraic reconstruction: constant/completed comparison, etale finite reductions,
connected affine charts, perfect normalized stalks and weakly contractible covers.
Source: Tag 09C6, first paragraph, with Tags 09C2, 094I and 09BI.

`lem-sfb-adic-residue-perfect-reduction-comparison` records the proved scalar and
slice comparison for a supplied bounded finite-projective A-complex. Source: Tags 09C6,
06YY and 093J. Existing general constant-realization/scalar-extension results are
retained as dependencies. Mathlib semantic and source searches found no theorem
with these completed coefficient and actual slice interfaces.

No change record is needed: all existing signatures, definitions, public imports
and consumer interfaces are preserved; the added public interfaces are in new
modules with these new nodes.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
