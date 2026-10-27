## What changed

Replaced the sorry in `Sheaf.Paper.DiagonalFiniteIntegralEndpoint` by a proof from
finite-level root scalar comparison and existing declarations. The actual target
statement, coefficient maps, root-limit objects, and public import are unchanged.
All added imports of the item are proof imports, including the ordinary
scalar-unit naturality API in `ExtendScalarsUnit`.

The private proof identifies the bottom coefficient inclusion with the published
condensed ring isomorphism, proves flatness of the restricted base line using
local freeness and signed-line tensor equivalence, and obtains preservation of
the inverse-limit shape from an integral finite basis and internal finite-free
coordinates. The limit universal property then constructs an ordinary scalar
isomorphism with exactly the prescribed root-map projection equations. Finally,
the flat single-complex endpoint and a generic private endpoint transport
construction give the derived isomorphism and its required normalization by
adjunction naturality. The actual root-limit definitions remain locally
irreducible during that calculation; no shared transparency is changed.

Added `Sheaf.Paper.DiagonalIntegralRootLevelScalars`, isolating the finite quotient
balanced-tensor calculation and its compatibility with the root-power transition.
It asserts neither a limit comparison nor a derived comparison. Its docstring
and new DAG node give the quotient, associator, normalization, and naturality
argument, including the bottom-field and empty-scheme cases.

Profiling found no expensive finite-level declaration: its elaboration and
kernel checking together took less than one second. The temporary profiling
options were removed after identifying an unconstrained basis universe and a
missing proof import in the endpoint file.

Validation: `lcompile.py` compiled the final item with no warnings or errors in
37.3 seconds. The unchanged new finite-level statement compiled with no warnings
or errors in 55.6 seconds in the preceding dependency run. No profiling options
remain. The two DAG Lean statement records match their files verbatim.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalFinite_integralEndpoint`
(node `lem-diagonal-finite-integral-endpoint`). There are zero sorries in the
item module. Its complete proof uses the following one newly added sorry:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalIntegral_rootLevelScalars`
  (node `lem-diagonal-integral-root-level-scalars`), in its own new module.

Thus one original hole is closed and one strictly lower finite-level hole is
added. This delivery is a decomposition, not a net reduction in holes or an
axiom-free proof of the endpoint. No definition contains a sorry. The limit
comparison, its root-map normalization, base-line flatness, and derived
adjunction assembly are proved in Lean rather than moved to the new statement.

## No longer needed

No original Lean import is removed, and no module is withdrawn. The original
public import `Sheaf.Paper.DiagonalCoefficientDiagrams` stays verbatim.

The direct proof no longer uses `sk-prop-sfb-qlbar-colimit-x` or the aggregate
`sk-prop-sfb-cartesian-coefficients`: no closure coefficient or colimit argument
is needed for a finite integral endpoint. The finite-free detail
`det-prop-sfb-cartesian-coefficients-finite-free` and the finite-coordinate lemma
are used directly instead. The actual integral root construction
`sk-def-sp-tate-twist`, local-freeness, signed-line equivalence, internal/section
flatness, and generic flat endpoint remain needed. These changes concern this
node's proof dependencies; they do not claim that either aggregate module is
unreachable from all project targets.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no interface repair was required. The original
plan's finite-level balanced-tensor sentence did not come with a declaration
that gives its normalized comparison for these actual coefficient maps. The
bottom finite-root-unit theorem identifies the bottom finite quotient tensor
with roots, but does not itself compare extension along the full Z_l-to-O_E
coefficient map. The existing finite-free theorem supplies coordinates for
scalar extension, not the missing normalized finite-level identification.
The new node isolates precisely that finite algebraic step. The rest of the
original argument is now implemented without any further split.

## New nodes

`lem-diagonal-integral-root-level-scalars` in
`dag/nodes/sec-six-functors-basics/` states the unit-normalized natural
isomorphism of the positive finite root towers after restriction to Z_l and
extension to O_E. It is strictly below the endpoint: it requires no invertibility
of l on X, and contains no inverse limit, flatness, or derived functor. Its
normalization fixes the prescribed finite coefficient inclusion, rather than
allowing an arbitrary isomorphism. No change record is needed: no other existing
module or statement is changed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
