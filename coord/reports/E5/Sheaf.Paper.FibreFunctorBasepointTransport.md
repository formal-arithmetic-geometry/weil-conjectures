## What changed

Proved `AlgebraicGeometry.Scheme.fibre_functor_basepoint_transport` with its original
signature and every original record condition. A direct application of the existing
Galois-category fibre-isomorphism theorem replaces the exact finite-group-set detour.
Conjugation is continuous in the existing evaluation topology; the change-of-path
identity is cancellation of natural isomorphisms.

Moved the sixteen existing interfaces into `FibreFunctorBasepointTransportData`, which
the original module publicly imports. The proved construction proceeds through finite
module linearization, integral inverse limits, rationalization, normalized coefficient
comparisons and localization. It includes the exact integral projection evaluation,
scalar germ and nested tensor formulas, both scalar/path squares, algebraic model
evaluation and all four path laws. The twelve new modules contain complete proofs and
constructions, not deferred statements.

Repaired `Sheaf.Paper.LisseAdicFiberFunctors.lisseAlgebraicFiberFunctor`: construct the
coefficient-pair functor from the uniquely normalized comparison family and lift it
through localization. Retained every original public signature, including the algebraic
existence theorem, now proved from that concrete construction and its restriction
isomorphism. Integral and rational data constructions are unchanged. All new public
helpers of this source module belong to its existing definition node. No
`WeilConjectures` module or target signature is changed.

The named predicates and large scalar comparisons are irreducible with explicit
interfaces, preventing repeated expansion of stalk and scalar expressions. The new
modules separate actual mathematical stages and generic categorical APIs; no slow proof
was divided to evade a compile limit. All compilation used the prescribed server tool.
The three unchanged direct users compiled against the repaired definition. The remaining
direct user, GaloisLisseCorrespondenceData, compiled with artifact emission in 38.5 seconds after local
irreducibility attributes for the rational fibre functor and the record predicates. Its original check hit the
60-second limit; profiling showed repeated module instance inference. All its declaration
headers and bodies are unchanged. The complete packet was then checked together.

Change records: `coord/changes/E5-canonical-algebraic-fibre-functor.md` and
`coord/changes/E5-fibre-path-interface.md`, and
`coord/changes/E5-galois-fibre-transparency.md`. The algebraic definition repair reopens
semantic statement review for every target using it. The original node statements and
all unit-level route data are preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.fibre_functor_basepoint_transport`
(`lem-wf-fibre-functor-basepoint-transport`). Original holes: 1; closed: 1; remaining: 0.
Added holes: 0. Split-off unfinished statements: 0. Every theorem and every data field in
the fifteen delivered Lean modules has a complete proof or concrete construction.
`LisseAdicFiberFunctors` had zero holes and still has zero holes; its definition repair
is additional work, not a hole closure.

The imported existing theorem
`lisseCoefficientFiberEndomorphisms_whisker_bijective` remains a dependency of the
canonical coefficient normalization, as it was of the previous construction. Existing
upstream statement holes are not claimed as proved here. No new axiom, hollow definition
or choice from an undetermined unproved existence statement is introduced. The unique
normalization theorem is fully proved before its determined data is selected.

## No longer needed

- The parent proof no longer needs `lem-wf-exact-finite-gsets-forgetful` or its module
  `Sheaf.CategoryTheory.Galois.ExactFiniteGsetsForgetful`: use
  `PreGaloisCategory.nonempty_iso_of_fiberFunctor` directly on finite etale covers and
  transfer along their existing FLC equivalence. This is dependency pruning, not a
  deletion of another declaration or withdrawal of an unfinished parent's node.
- The parent route no longer uses `thm-galois-fundamental`,
  `lem-galois-equivalence-preserves-limits`, or the separate exactness detour through
  `def-galois-category`. The obsolete `thm-galois-fundamental` tool approval is removed,
  preserving the order of all retained approvals. The finite-etale Galois-category
  and FLC equivalence nodes remain needed. The lisse action and scalar nodes remain
  needed through their interfaces and finite scalar stalk comparisons.
- In `LisseAdicFiberFunctors`, the old private `grothendieckFiberFunctor`,
  `grothendieckFiberFunctor_inverts` and `grothendieckFiberFunctor_restrict` are replaced
  by the proved normalized construction and restriction API. The old private inclusion
  and the category-transport cancellation helpers remain needed for the fixed-model
  interface and its retained existence theorem. No existing public declaration is
  deleted. No adopted-source declaration is removed or replaced by a hole.
- The twelve new modules introduce only the interfaces, construction parts and generic
  APIs used by this proof and definition repair. A duplicate preliminary unnormalized
  Grothendieck construction helper was removed before delivery. Diagnostics are outside
  the delivered Lean tree. The original public interface imports moved to the data
  module; they are not claimed as pruned mathematical dependencies. Proof-only scalar
  square and coefficient-naturality imports are private in the algebraic path module.

## Where the brief, the DAG or earlier work was wrong

The original finite path plan reconstructs a general Galois-category result already
proved in the adopted library. Its exact-functor detour is unnecessary.

The earlier algebraic functor chose an arbitrary coherent comparison family via a mere
existence theorem. Its separate model restrictions did not fix these comparisons, so
one cannot deduce that the chosen functor's scalar comparisons respect geometric paths.
The concrete least-field normalization fixes the relevant data uniquely and makes the
path square provable. The existing definition node's mathematical statement is retained;
its construction and Lean attachment are updated. The repaired algebraic existence
interface also verifies its fixed-model restriction and prescribed pure-tensor formula.

The supplied finite and adic hypotheses and conclusions required no weakening. Edge
cases checked in the proofs include the zero module, identity paths, loops, identity
coefficient inclusions, arbitrary finite noncommutative rings in the finite part, and
ramified integral coefficient extensions with the prescribed ceiling reindexing.

## New nodes

`new-e5-adic-fibre-path-extension`: Assembling adic path transport with scalar compatibility. Its public declarations are in `Sheaf.Paper.AdicFibrePathExtension`; all are proved or concretely constructed.

`new-e5-algebraic-fibre-path-construction`: Descent of rational paths to algebraic coefficient fibres. Its public declarations are in `Sheaf.Paper.AlgebraicFibrePathConstruction`; all are proved or concretely constructed.

`new-e5-coefficient-fibre-comparison-naturality`: Transport of rational scalar path squares to coefficient categories. Its public declarations are in `Sheaf.Paper.CoefficientFibreComparisonNaturality`; all are proved or concretely constructed.

`new-e5-fibre-path-transport-data`: Finite and adic fibre path transport interfaces. Its public declarations are in `Sheaf.Paper.FibreFunctorBasepointTransportData`; all are proved or concretely constructed.

`new-e5-integral-fibre-path-construction`: Inverse-limit transport of integral lisse fibres. Its public declarations are in `Sheaf.Paper.IntegralFibrePathConstruction`; all are proved or concretely constructed.

`new-e5-integral-fibre-scalar-comparison`: Canonical integral scalar comparison respects fibre paths. Its public declarations are in `Sheaf.Paper.IntegralFibreScalarComparison`; all are proved or concretely constructed.

`new-e5-linear-fibre-path-transport`: Linear transport of finite locally constant module stalks. Its public declarations are in `Sheaf.Paper.FibreFunctorLinearTransport`; all are proved or concretely constructed.

`new-e5-localized-fibre-path-transport`: Descent of a natural fibre isomorphism through localization. Its public declarations are in `Sheaf.Paper.LocalizedFibrePathTransport`; all are proved or concretely constructed.

`new-e5-normalized-fibre-comparisons`: Unique normalization of coherent coefficient comparisons. Its public declarations are in `Sheaf.Paper.NormalizedFibreComparisons`; all are proved or concretely constructed.

`new-e5-rational-fibre-path-construction`: Rationalization of integral fibre paths. Its public declarations are in `Sheaf.Paper.RationalFibrePathConstruction`; all are proved or concretely constructed.

`new-e5-rational-fibre-path-scalar-square`: Rational scalar comparison intertwines paths. Its public declarations are in `Sheaf.Paper.RationalFibrePathScalarSquare`; all are proved or concretely constructed.

`new-e5-rational-fibre-scalar-comparison`: Tensor formulas for rational scalar fibre comparisons. Its public declarations are in `Sheaf.Paper.RationalFibreScalarComparison`; all are proved or concretely constructed.


Change records: `coord/changes/E5-canonical-algebraic-fibre-functor.md`,
`coord/changes/E5-fibre-path-interface.md`,
`coord/changes/E5-galois-fibre-transparency.md`.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
