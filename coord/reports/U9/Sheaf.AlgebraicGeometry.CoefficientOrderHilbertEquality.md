## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.HilbertCoefficient.coefficient_order_hilbert_equality` by a complete
Lean combination of three strictly smaller comparison statements. The existing theorem
signature, its docstring, `coefficientDerivativeIdeal`, and all existing public imports
are unchanged. No other existing Lean module is edited.

The proof first identifies the formal low-derivative ideal with transverse variables and
coefficient derivatives. The regular-stratum comparison supplies one degree cutoff before
quantifying over generating lists. Its Taylor-extension identity feeds the coefficient
ideal descent theorem. The proof intersects the two resulting opens, composes their locus
equivalences, and pulls back the actual ideal-sheaf equality to that intersection using
`Scheme.IdealSheafData.comap_comp` and `Scheme.homOfLE_ι`. Characteristic zero of the actual
residue field is obtained from its injective field map from k. The `hcenter` hypothesis
is retained verbatim and supplies the distinguished coefficient-order point to the descent step.

Added proof imports of `FormalLowDerivativeCoefficients`,
`StraightenedRegularStratumComparison`, and `CoefficientDerivativeIdealDescent`, and
`Mathlib.Algebra.CharP.Algebra`. Updated only `proof`, `proof_deps`, and `proof_origin` of
the assigned DAG node. Added one module and one node per remaining comparison step.

Validation: the four sandbox modules compile through `lcompile.py --all`; the final
compile and axiom probes are checked again by the delivery tool. No local Lean/Lake build was run.

## Proved and sorry left

Closed the assigned hole in
`AlgebraicGeometry.HilbertCoefficient.coefficient_order_hilbert_equality`
(node `lem-trf-coefficient-order-hilbert-equality`) by a complete proof from the three
intermediate statements. There are zero textual holes left in the assigned module.

Added exactly three named public theorem holes, each with a full proof in words, source,
and matching DAG node:

- `AlgebraicGeometry.HilbertCoefficient.formal_lowDerivativeIdeal_eq_coefficients`
  (`lem-trf-formal-low-derivative-coefficients`): formal step 3; no schemes, Hilbert
  functions, coherent ideals, regular minor presentations, or generating lists.
- `AlgebraicGeometry.HilbertCoefficient.straightened_regular_stratum_comparison`
  (`lem-trf-straightened-regular-stratum-comparison`): steps 1--2; no regular
  coefficient expansion, coefficient-order locus, or coherent coefficient ideal equality.
- `AlgebraicGeometry.HilbertCoefficient.coefficient_derivative_ideal_descent`
  (`lem-trf-coefficient-derivative-ideal-descent`): steps 4--5; an arbitrary regular
  ideal with a specified formal extension, with no standard basis or Hilbert-function
  conclusion.

This is a decomposition: one upper hole closed, three lower holes added, net minus two
holes of progress before any independent downstream changes. It is not a claim that the
mathematical comparison is now free of `sorry`. No definition contains a hole and no
arbitrary data are chosen from an unproved existence statement.

## No longer needed

Removed the assigned module's direct proof imports of
`Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus`,
`Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`, and
`Sheaf.RingTheory.PresentationFittingIdeal` because its proof now uses the explicit
comparison steps instead. Their mathematics is still needed inside the new nodes;
this delivery does not prune any mathematical module from the overall argument.

All six original proof dependencies remain required through the new nodes:
formal Hilbert-stratum minors, jet-diagram Hilbert control and Fitting independence
through the stratum comparison; implicit Taylor calculus through stratum transport and
ideal descent; etale coordinate derivations and Taylor normal-cone splitting through
ideal descent. The formal identity also cites the existing formal transverse-shift
calculus for its zero-graph factorization. No existing node or module is withdrawn.
No public import was removed, and no source-library declaration was changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The old DAG correctly describes the
argument, but its elementary step 3 and the coordinate/stalk compatibility in steps
1--2 and 4--5 are not direct applications of the exposed theorem signatures.
For example the regular Taylor-minor comparison is expressed in `Fin d` ordinary
coordinates, whereas this item uses `Fin m ⊕ Fin n` and a straightened expansion;
its stratum cutoff must also be independent of the generating list. The implicit
calculus is packaged on its constructed Jacobian-open zero subscheme, whereas the
item supplies an arbitrary closed immersion N and its prescribed global Taylor maps.
The three new statements isolate exactly these compatibility and algebra calculations.

The unit route is unchanged: the assigned node belongs to the inherited local-algebra
branch of `sk-i-curve-zero`; its unit record does not bind this node as a unit statement
or unit proof step. The current blueprint unit was read through `literature/blueprint/latest`.

Edge checks for the new statements: when s=0, essentiality in the formal/stratum claims
forces n=0, the derivative ideals vanish, and supported generation forces the central
Taylor ideal to vanish. For the descent statement an empty coefficient list gives
C=0 and its inverse image is the ideal of N, which is the correct support. When n=0,
setting Z=0 is the identity and there is no transverse Jacobian computation. When
m=0 the tangential derivative tuple is empty but the order-zero test remains whenever
the weight is positive. Degree-zero weights contribute no derivative tests. For one
transverse variable, alpha=d and f=Z^d in characteristic zero give E=(Z), as asserted;
for f=Z^2+W^3 the formal identity gives E=(Z,W^2), consistent with the coefficient test.
These are mathematical checks, not additional claims of formalized proofs.

## New nodes

`lem-trf-formal-low-derivative-coefficients`, in
`Sheaf.AlgebraicGeometry.FormalLowDerivativeCoefficients`, states the formal
coefficient identity using only expansion and the nonsingular derivative blocks.
Its proof allocates monomials to transverse factors, obtains (Z) inside E, and compares
mixed derivatives modulo (Z), where the factors are invertible factorials.

`lem-trf-straightened-regular-stratum-comparison`, in
`Sheaf.AlgebraicGeometry.StraightenedRegularStratumComparison`, states the regular
minor equality germ and its formal extension, uniformly over finite generating lists.
Its proof uses the existing formal-minors, jet-diagram, implicit-Taylor and Fitting
statements; the new work is their coordinate, residue-field and presentation compatibility.

`lem-trf-coefficient-derivative-ideal-descent`, in
`Sheaf.AlgebraicGeometry.CoefficientDerivativeIdealDescent`, states faithful-flat
contraction and spreading for an arbitrary regular ideal with the coefficient formal
extension, together with its actual stalk-order support. It uses the existing
implicit-coordinate, etale-derivation and Taylor normal-cone results.

All three inherit the assigned node's source, chapter, unit and blueprint ancestry.
LeanSearch, LeanFinder/Loogle, local Mathlib and project `rg`, and blueprint searches
were checked and recorded in each node. No exact existing statement supplies these
conclusions. No change record is needed: all existing signatures, definitions, public
imports and attributes are preserved; the only added public declarations are in new
modules privately imported for the assigned proof.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
