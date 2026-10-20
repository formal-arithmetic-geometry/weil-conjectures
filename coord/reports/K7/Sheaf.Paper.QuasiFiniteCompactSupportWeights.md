## What changed

Proved `WeilConjectures.sfQuasiFiniteCompactSupport` with its original complete
signature and universes. The quasi-finite predicate import follows its upstream
relocation to `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`, matching
the current shared source. Its proof translates point-isolation
quasi-finiteness to Mathlib local quasi-finiteness, constructs a finite
compactification by Zariski Main Theorem, and compares it with the supplied one.
It proves the eigenvalue-power norm calculation for an arbitrary coefficient
embedding and transports the original global mixed filtration, including its
cokernel quotients, through one exact functor.

Also proved three auxiliary results in separate modules:

- `sfFiniteCompactificationWeilExact`: the small Weil-pair presentation is an
  equivalence; the embedding into ind-pairs is exact by Yoneda reflection and
  the Frobenius comparison. Exact open extension and finite ordinary image give
  an exact composite. The specified degree-zero representations lift this
  whole functor through the fully faithful embedding, so exactness reflects
  to the heart. Computing on an injective resolution and reflecting zero gives
  positive vanishing.
- `sfFiniteWeilIndPushExact`: lift the underlying ind-heart adjunction through
  the actual Frobenius square and its invertible mate, then compare right
  adjoints. This categorical argument is complete Lean, including the
  preservation of finite colimits on Frobenius pairs.
- `sfFiniteCompactificationEigenvalues`: take a nonzero eigenvector in its
  specified finite Weil presentation, select a nonzero component using joint
  injectivity of stalk evaluations, and apply the return formula and the
  power-eigenvector identity. The component's finite Weil presentation
  witnesses the required source eigenvalue.

Five auxiliary modules and nodes are added. The two remaining separate source
results concern ordinary finite-image exactness and the geometric finite-stalk
return comparison. Neither mentions weights or mixed filtrations. The latter
contains no eigenvalue hypothesis or conclusion. They isolate source results,
not a copy of the assigned theorem. Existing exported signatures, definitions,
visibility and target statements are unchanged. No existing consumer is adapted.
The new stalk abbreviations are explicit recorded constructions; the evaluation
structure is a type of witnesses, with no chosen global value. Its existence is
used only inside a theorem proof. No data definition selects an arbitrary witness
from an unproved existence theorem.

## Proved and sorry left

Closed the assigned module's only hole:
`WeilConjectures.sfQuasiFiniteCompactSupport`
(node `sk-l-dl-general-quasifinite`).

The following added auxiliary theorems are proved, with no local holes:
`WeilConjectures.sfFiniteCompactificationWeilExact`,
`WeilConjectures.sfFiniteWeilIndPushExact`, and
`WeilConjectures.sfFiniteCompactificationEigenvalues`. Every private helper is proved.

Added holes (two), each the entire proof of a named public theorem:

- `WeilConjectures.sfFiniteIndHeartAdjunction`
  (`lem-zl-finite-ind-heart-adjunction`): finite ordinary direct image on
  underlying ind-hearts is a right adjoint preserving finite colimits. This
  has no category of Weil pairs, compactification, eigenvalue or weight clause.
  Its geometric input is Stacks 09A8 and BS 6.8.14--6.8.15. The Frobenius-pair
  lift from this result is proved in the delivery.
- `WeilConjectures.sfFiniteCompactificationStalkReturn`
  (`lem-zl-finite-compactification-stalk-return`): actual finite-stalk
  evaluations are jointly injective and intertwine a positive power of the
  target operator with source local Frobenius. The finite presentations,
  residue embeddings and cardinality relation are retained. This is the
  finite-stalk formula and return sentence of the source finite-pushforward
  proof, before any eigenvector, complex coefficient embedding or weight argument.

There are zero holes in the assigned module and the other three proved modules,
and two in the delivery. One original hole is closed and two are added: this is
an overall decomposition, with local net -1, not a net proof gain. No claim of an
axiom-free transitive dependency closure is made. The separately stated source
results are true, needed and strictly separate parts of the original argument.

Validation: the complete six-module set compiled through the launcher in import
order. A further check after adding the source modules' planned proof imports
is recorded by the dry run. Compilation uses only lcompile.py; no local Lake
or manual project build was run. Earlier dry runs pushed nothing. The categorical
mate-lift and eigenvector extraction were each compiled as real proofs before
updating their nodes. The remaining geometric comparison requires the prescribed
adjunction and coefficient/Weil normalizations, beyond an arbitrary carrier
isomorphism: the exactness theorem supplies the correct underlying ind adjunction;
the stalk theorem supplies actual evaluation and return operators on every given
finite Weil presentation.

Continuation validation (2026-10-20): the required initial dry run was run
before changing the retained packet. It reported the split-off proof gate (two
holes, 53 minutes on its current reference clock), rather than a source or
compiler error. The entire six-module packet was then recompiled against the
current server library: all six modules passed, in 2.7--7.9 seconds per file.
The parent signature, the unit's finite-fibre route, and all six node copies
were checked again against current sources and the source proof paragraphs.
Additional LeanFinder, Loogle and local searches found no replacement for the
ordinary ind-heart adjunction or the normalized adic stalk-return comparison.

In particular, `ZlFiniteAdicDirectImageData.commonExactness` concerns separated
geometric schemes; it does not directly supply the claimed ind-heart adjunction
on a possibly nonseparated target. Its `rational` adjunctions and `stageMate`
are the normalized inputs needed for affine-chart descent. The existing
`a1FiniteWeilSectionsDecompositionRational` supplies the return identity for
finite sections, but the remaining stalk theorem must transport it to the
specified higher-image presentation, retain the original local operator, and
handle independent scheme and coefficient universes. An arbitrary underlying
vector-space isomorphism does not accomplish that transport. These are the two
separate geometric source results retained by the decomposition; no additional
holes were introduced during this continuation.

Earlier actual delivery attempts failed before pushing: the launcher raised
`subprocess.TimeoutExpired` while creating its temporary worktree, at
`git checkout -q --detach origin/sheaf-dag` after 600 seconds. Historical logs
remain in `scratchpad/deliver-durable-oct20.log` and
`scratchpad/deliver-retry-oct20.log`. The launcher was not edited. Current
delivery status is given by the final deliver3.py result, not those old logs.
The first current push attempt stopped on a 60-second compile of the stalk
module. A profiler compile of that same module completed in 15.7 seconds:
cumulative elaboration 1.97 seconds, kernel type checking 5.99 seconds,
typeclass inference 3.18 seconds, congruence generation 1.71 seconds. No
individual elaboration step approached the limit. The diagnostic profiler
option was removed before the next required checks; no limit was changed.
A subsequent dry run compiled the stalk module in 54.1 seconds and then
reached a timeout in the exactness module. Its direct profiler compile passed
in 14.4 seconds: elaboration 0.6 seconds, tactics 1.1 seconds, kernel checking
0.389 seconds, typeclass inference 9.58 seconds. Again, no proof step was near
the limit. The temporary profiler option was removed.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Paper.LocalFrobeniusTrace`
- `Sheaf.Paper.SfWeilSheafComplex`
- `Sheaf.Paper.ConstructiblePullbackTExact`
- `Sheaf.Paper.DlConstructibleFibresExact`
- `Sheaf.Paper.WeilPullbackLocalFrobenius`
- `Sheaf.AlgebraicGeometry.ClosedPointField`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.ZlFiniteAdicDirectImage`
- `Sheaf.Paper.ZlImmersionWeilLocalBehavior`
- `WeilConjectures.WeilSheaf.LowerShriekFunctoriality`
- `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange`
- `Sheaf.Paper.QbarCompactSupportBaseChange`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Sheaf.Paper.A1FiniteWeilSectionsDecomposition`
- `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison`

The factorization import stays. The parent directly uses the finite-exactness
and eigenvalue nodes, higher-image comparison, punctual-weight definitions and
finite properness. The local comparison, finite-image, immersion and
Frobenius-cycle nodes remain needed below the geometric source results; moving
an import down is not global pruning. The original geometry imports are available
through the auxiliary statements and factorization theorem. No globally
unnecessary module is claimed, and no maintainer tool_uses approval is withdrawn.

Within the new proof route, the equivariant exactness node needs only the
underlying ind adjunction and the existing ind-Frobenius infrastructure. The
eigenvalue node needs only the stalk-return node and punctual eigenvalue
definition. Their nodes no longer directly list the local geometric calculation,
which belongs to the new source nodes.

## Where the brief, the DAG or earlier work was wrong

The source-library quasi-finite and finite-lower-star results use the older
WeilSheaf category. They do not identify the actual common-stage Weil heart or
its prescribed ind-derived higher images. A type synonym or simpa does not
bridge this difference. Finite-adic direct-image data supply exact hearts and
normalized stalk formulas on absolutely separated schemes. Applying them here
requires affine target charts, coefficient descent, and the prescribed
inverse-image adjunction. The new source nodes specify those comparisons.

The original parent already corrects the blueprint's inference of absolute
separatedness from finiteness: the identity of the doubled-origin affine line
is a counterexample. The new statements retain relative hypotheses, and their
source proofs localize to affine target opens. No existing statement is disputed
or weakened. The blueprint unit's finite-fibre, Frobenius-cycle and one-global-
filtration route is retained.

Edge cases checked: empty source and fibre; zero sheaf and zero stalks; identity
and nonreduced finite maps; nonzero orbit degree; negative weights; arbitrary,
possibly nonsurjective coefficient embeddings; length-zero filtrations; and
independent coefficient and scheme universes. For an empty evaluation family,
joint injectivity forces the output vector space to be zero, exactly as needed
by the eigenvector extraction. The source presentation in the return structure
refers to F itself, so the proof cannot manufacture a source eigenvalue from an
unrelated vector space.

The continuation clock appears to have reset. For this same dispatched attempt
(K7, Sheaf.Paper.QuasiFiniteCompactSupportWeights), searches.jsonl starts at
2026-10-19 05:06:17 UTC, and an earlier resumed dry run reported 59 minutes of
proof work. After the provider-429 interruptions, the current .budget start is
2026-10-19 12:51:48 UTC; the dry run at 13:40 UTC reported only 48 minutes.
The launcher was not patched and timing metadata was not edited. Work continued
on the same packet, including complete categorical and eigenvector proofs;
the original session deadline remains in force. The launcher owner should check
the reference-clock lifecycle across dispatcher continuations. A later reset put
the start at 2026-10-19 19:23:30 UTC; the next gate again reported only ten
minutes. The packet was preserved across those resets. The full six-module
compile subsequently passed, before the upstream predicate import relocation.
The first dry run after the split gate passed its timing check detected that
relocation; the sandbox import now matches the shared source.

## New nodes

`lem-zl-finite-compactification-weil-exact`, module
`Sheaf.Paper.FiniteCompactificationWeilExact`: proved exact degree-zero functor
and positive vanishing for finite compactifications, from ordinary finite-image
exactness, exact open extension, Yoneda reflection and the prescribed higher-
image representations. No sorry.

`lem-zl-finite-weil-ind-push-exact`, module
`Sheaf.Paper.FiniteWeilIndPushExact`: proved Frobenius-mate adjunction lifting
and exactness transfer from the underlying ind-heart adjunction. No sorry.

`lem-zl-finite-compactification-eigenvalues`, module
`Sheaf.Paper.FiniteCompactificationEigenvalues`: proved nonzero-component
extraction and positive-power eigenvalue formula, with residue cardinalities.
No sorry.

`lem-zl-finite-ind-heart-adjunction`, module
`Sheaf.Paper.FiniteIndHeartAdjunction`: the underlying exact ordinary finite
image from Stacks 09A8 and BS 6.8.14--6.8.15, extended to ind-hearts with its
inverse-image adjunction; one sorry remains, with source and full proof in words.

`lem-zl-finite-compactification-stalk-return`, module
`Sheaf.Paper.FiniteCompactificationStalkReturn`: the geometric finite-stalk
formula and Frobenius-return identity of the source finite-pushforward proof,
on the actual scalar-extended finite-stage stalks; one sorry remains, with
source and full proof in words. Includes only explicit stalk/operator
abbreviations and the evaluation-data structure.

No change record is required: existing changes follow the upstream import
relocation and are otherwise restricted to the assigned proof, private helpers,
proof imports and proof route; all other declarations
and nodes are new. No forced adaptation or withdrawal occurs.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
