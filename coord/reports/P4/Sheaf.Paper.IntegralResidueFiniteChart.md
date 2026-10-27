## What changed

Restored the archived item unchanged in statement and public imports, and replaced
its proof hole by a Lean assembly of algebraic descent, finite inverse-image
composition, constant inverse-image compatibility, and two separate presentation
comparisons. No existing declaration signature, definition body, attribute, or
public import was changed.

The private `smallPerfectModel` argument constructs the small bounded complex.
It restricts scalars along a ring equivalence, uses `Module.Finite.small` and
`Shrink.linearEquiv` on each term, and descends the differentials through the
fully faithful universe lift. Faithfulness verifies shape and square-zero;
semilinear equivalences preserve finite generation and projectivity. Fullness of scalar restriction is proved
directly from the inverse ring equivalence, allowing the two coefficient rings
to live in different universes. The proof also transports the strict bounds and constructs the derived model isomorphism.
It does not assume a theorem asserting the desired small perfect model.

Added `IntegralResidueQuotientLift`: the quotient ring equivalence and module
lift are explicit constructions from the existing uniquely normalized quotient
identification, `ULift.ringEquiv`, and equality of the two ideals. The proved
`integralResidueQuotientEquiv_mk` records its action on residue representatives.

Added two independent comparison statements. `IntegralResidueFiniteSlice` takes
arbitrary finite derived objects and an isomorphism after inverse image, and
returns their normalized slice isomorphism; it mentions no constant or perfect
complex. `IntegralResidueFiniteConstants` compares the global realizations of an
arbitrary small complex; it mentions no chart or morphism of schemes. Neither is
the original existential finite-chart statement under a new name.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.integralResidueFiniteChart`
(node `lem-weil-pbc-integral-residue-finite-chart`) by a complete proof from the
comparison statements. The item has zero direct proof holes. Its algebraic
shrinking, pullback composition, preservation of constants by inverse image,
localization comparisons, and final composition are proved.

Added exactly two named proof holes:

- `AlgebraicGeometry.Scheme.integralResidueFiniteSlice`
  (`lem-weil-pbc-integral-residue-finite-slice`).
- `AlgebraicGeometry.Scheme.integralResidueFiniteConstants`
  (`lem-weil-pbc-integral-residue-finite-constants`).

The quotient-lift module has zero holes. This is a decomposition of one original
hole into two independent, strictly partial comparisons, with the entire
bounded finite-projective descent proved. It is not reported as a net reduction
in holes: one closed and two added. No definition contains a proof hole.

Verification: the final `lcompile.py --all` run compiled all four modules without
errors or warnings: slice 36.9 s, quotient lift 27.1 s, constants 32.8 s, and item
43.8 s. Every file is below the 60 s limit.

## No longer needed

No existing module or public import is withdrawn. A redundant direct proof import
of the new quotient-lift module was removed: the constant-comparison module
already exports it. The original public imports are
retained for the unchanged statement and public API. The finite-reduction
module remains needed for `integralResidueFiniteModel`; its theorem
`integralResidueFiniteReduction` is not invoked. The coefficient-model existence
theorem is not invoked either: the supplied model is used.

The following old direct proof dependencies are replaced by the new explicit
construction and two comparison nodes:

- `def-weil-l-adic-coefficient-extension`;
- `lem-weil-pbc-integral-residue-coefficient-model`;
- `lem-weil-pbc-integral-residue-finite-reduction`;
- `def-weil-pbc-integral-stratified-perfect-models`.

This removes no transitive mathematical prerequisite. Their required definitions
and transitive dependencies remain, and the original statement dependencies are
preserved. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies expose coefficient data, perfectness, inverse image and
slice restriction, but do not themselves provide the two normalized presentation
comparisons required by the second proof step. These are now stated independently
without perfectness assumptions. The first step is actually proved, using smallness
of finitely generated modules rather than a new existence lemma for small models.
The unit route and theorem statement remain unchanged.

The item initially existed only in quarantine. Its archived source was restored
in the sandbox, with its attachment and dependencies preserved. During this
session the shared source tree restored the item and its dependencies as well;
the restored item agrees with the archive.

## New nodes

`def-weil-pbc-integral-residue-quotient-lift` records the explicit normalized
quotient equivalence and small-module lift in
`Sheaf.Paper.IntegralResidueQuotientLift`. Its construction has no holes.

`lem-weil-pbc-integral-residue-finite-slice` records the comparison between finite
scheme inverse image and actual normalized ringed slice restriction, for two
arbitrary derived objects, in `Sheaf.Paper.IntegralResidueFiniteSlice`.

`lem-weil-pbc-integral-residue-finite-constants` records the global compatibility
of constant complexes with the normalized quotient coefficient transport in
`Sheaf.Paper.IntegralResidueFiniteConstants`.

All new nodes retain the original chapter, unit and literature source. The item
node records the implemented shrinking and assembly route. No change record is
required: only the item, new modules and their nodes are changed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
