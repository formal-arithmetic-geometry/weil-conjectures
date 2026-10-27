## What changed

Proved both existence-and-uniqueness theorems in
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, preserving every existing
statement, definition body, attribute and public import. Added one proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`.

The underived proof restricts the scalar actions to constants, uses the sheafification
unit isomorphisms, and lifts the comparison through the fully faithful restriction
functor. It proves the exact scalar-section normalization and uniqueness. The derived
proof extends the quotient of two derived units from K-injective representatives,
then cancels the units to obtain precisely the stated normalization and proves uniqueness.
All auxiliary declarations are private and proved. The generic representative helpers
follow the existing proved helpers in `ExactPostcompositionKInjectiveDescent`; its public
square theorem uses a different resolution-based right derived functor, so this proof
works directly with the upstream `rightDerivedFunctor` used by the item.

The node now records these proof steps and attaches the two theorem names and the
existing scalar-unit definition. No unit route changes. No change record is needed:
there is no public interface or definition change.

Validation: the complete file compiles cleanly through lcompile.py in 33.8 seconds.
The generic derived-square helper avoids expensive unfolding in the specialized
calculation without changing definitions or the compile limit. Empty schemes, zero
modules and the zero coefficient ring require no extra hypotheses in either argument;
all section identities and categorical isomorphisms apply unchanged.

## Proved and sorry left

Closed 2 of 2 holes:

- `AlgebraicGeometry.Scheme.sfIntrinsicDirectImageComparison_existsUnique`.
- `AlgebraicGeometry.Scheme.sfIntrinsicDerivedDirectImageComparison_existsUnique`.

Both belong to `def-sp-finite-intrinsic-direct-adjunction`. Zero holes remain in the
item. Zero holes added; zero statements split off. All private helpers are fully proved.
The delivery probe checks the declarations' actual axiom dependencies; this report
counts direct holes, not transitive axioms in imported modules.

## No longer needed

None. All original public imports are retained, since they are part of the published
interface. The single new private import supplies the derived unit on complexes and
its naturality. No node or module is withdrawn, and no unfinished dependency is bypassed.
The continuous-function comparison module was consulted as a construction pattern;
it is not imported because the intrinsic scalar square has its own proof.

## Where the brief, the DAG or earlier work was wrong

The attached definition node had no proof steps and did not list the two normalization
theorems among its declarations. Its proof record and declaration inventory now include
the implemented arguments. No mathematical statement was changed or disputed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
