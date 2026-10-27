## What changed

Constructed the ordinary completed constant complex, its actual coefficient tensor
complex tower, and its cone in `Sheaf.Paper.FinitePerfectAdicFreeTensorCone`.
The cone is the tensor image of the coefficient cone, extended along the inverse
right unitor. Its chain-map equations follow from tensor-projection naturality.

Proved the finite-free cone normalization: regular constant modules identify with
the constant-ring unit by local bijectivity, and the existing scalar-extension
unit constraint identifies its extension with the completed-ring unit. Finite
product preservation and the tensor unitors give the entire free coefficient
diagram and its cone, including rank zero.

The item's proof now applies Mathlib's finite-projective splitting to every term,
maps both splitting maps into the ordinary tensor diagram, and conjugates the
free diagram and cone by this normalization. It proves both splittings and both
cone compatibility equations. The bounded-flat derived comparison is isolated in
`Sheaf.Paper.FinitePerfectAdicFlatTensorComparison` and applied after projective
terms are recognized as flat. No existing definition, public import, theorem
signature, instance, or target statement changes.

## Proved and sorry left

Original hole removed:
`AlgebraicGeometry.Scheme.finitePerfectAdicCanonical_comparison`.

New fully proved theorem:
`AlgebraicGeometry.Scheme.finitePerfectAdicFreeTensorCone_comparison`, node
`lem-weil-pbc-finite-perfect-adic-free-tensor-cone`.
The explicit tensor-cone definitions and tensor-projection naturality are also
complete. The private termwise retract proof contains no holes.

One new hole remains:
`AlgebraicGeometry.Scheme.finitePerfectAdicFlatTensor_comparison`, node
`lem-weil-pbc-finite-perfect-adic-flat-tensor-comparison`.
This is a decomposition: one upper hole is replaced by one lower hole, net zero,
not a complete proof independent of sorry. The remaining statement concerns the
specified explicit bounded flat model, assumes neither finite generation nor
projectivity, and asserts no finite-free retract existence. The ordinary model,
free normalization, and finite-projective retract construction are now proved;
they have not been moved to this hole. The item's module has zero textual holes.

Validation: the final remote `lcompile.py --all` passed with no errors or
warnings: free tensor cone 23.3 seconds, bounded-flat statement 5.2 seconds,
and original item 13.8 seconds. All files meet the 60-second limit. The existing
node changes only `proof`, `proof_deps` and `proof_origin`; a verbatim comparison
confirms the original theorem signature is unchanged. Each node
`lean.statement` matches its Lean declaration, and each proof dependency list
equals the union of its proof-step uses. The required delivery command performs
the independent mechanical preflight and axiom checks.

## No longer needed

No original public imports are removed. The original direct dependency
`lem-weil-pbc-constant-module-section-properties` is not used for the free or
finite-projective retract construction: unit normalization and additive finite
product preservation suffice. No module is claimed pruned from the target closure;
other remaining comparison proofs can still need the constant-section API. The main node now directly uses the proved
finite-free normalization, the coefficient-retract structure and the bounded-flat
comparison. The scalar-reduction, constant-realization mate, and algebraic derived
adjunction dependencies remain needed by the latter node. The proof needs no Roos
or inverse-limit assertion; the coefficient-limit module supplies its existing
coefficient diagram, projections, cone and retract structure.

The initial use of `completedAdicOrdinaryTower` was replaced during development by
direct postcomposition of the actual coefficient diagram with tensoring. This is
an explicit new construction, not a change of the existing tower functor. It
makes the coefficient cone equations follow directly from mapping a cone.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies do not directly state the required comparison for this
small algebraic localization, its explicit universe lift, and this completed
coefficient tower. The completed constant reduction theorem uses a different
constant coefficient presentation. Its finite-projective clause concerns an
augmented resolution of a quotient, not the natural tensor diagram of an arbitrary
bounded perfect complex. It cannot close the entire item by a direct application.
The remaining derived comparison states this actual gap, with the literature
proof and existing dependencies recorded.

The tower and cone construction themselves do not require the derived quotient
comparison: tensoring the actual coefficient cone suffices. Finite-projective
splittings require no boundedness, Noetherian hypothesis, nonzero coefficient
ring, or positive rank. Boundedness enters only the remaining derived comparison.
All original hypotheses and conclusions are retained, including arbitrary chosen
left adjoints and their actual canonical transitions. The unit route is unchanged.

## New nodes

`lem-weil-pbc-finite-perfect-adic-free-tensor-cone` attaches the explicit ordinary
constructions and the proved finite-free diagram/cone comparison to
`Sheaf.Paper.FinitePerfectAdicFreeTensorCone`. Its generic unit/product argument
is fully written in Lean. The existing scalar-extension unit constraint is used
as a generic algebraic tool, not as a replacement for any unit's geometric route.

`lem-weil-pbc-finite-perfect-adic-flat-tensor-comparison` attaches the one remaining
bounded-flat comparison to `Sheaf.Paper.FinitePerfectAdicFlatTensorComparison`.
It is strictly a part of the argument: the tower and point are fixed explicit
constructions; it contains no existential complex tower, cone, or retract data.
Its proof uses normalized finite reduction, bounded-flat K-flatness, the constant
scalar-extension mate, and uniqueness of left adjoints with its unit equation.
Zero complexes, reversed bounds, rank zero and the zero coefficient ring were
checked in the statements and the constructions. No new change record is needed
because no existing public interface is changed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
