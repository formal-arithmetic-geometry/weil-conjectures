## What changed

Proved WeilConjectures.isomorphismFieldTransportCommonStage without changing its signature.
Added three proved modules for epsilon naturality and normalized shift descent. The item's additional
imports are private proof imports; its public imports are unchanged.

The proof identifies the specified quotient pullback with the coherent StageSystem morphism
by its unique object and representative formulas. Its inclusion comparisons have identity
components. The scalar inverse law, transported across the published transition identifications,
gives a compatible finite transformation; its descent has exactly the prescribed own-stage
epsilon components. Apply this to g and inv g to construct the equivalence. For shifts, invert
the supplied normalized lambdas and apply the already stated isomorphismPullbackScalarShift;
then descend the compatible finite shifts. A common-stage distinguished triangle is isomorphic
to an included finite triangle. The stage comparison commutes with the descended shift, so
finite rational exactness proves exactness, including the connecting arrow. Additivity follows
from triangulatedness. The object and arrow clauses are the existing uniqueness specification.

The generic pair-shift proof is included as proved private helpers, following the calculation
in SfFrameworkCommonStageDescent (Q19), specialized only by its actual input instances. No
private implementation is imported from that module and no additional linearity or unit
hypothesis is introduced. All existing library sources besides the assigned module are unchanged.

Validation: lcompile.py compiled all four modules. The latest successful supporting-module
checks took 42.8 s (normalized descent), 45.5 s (epsilon naturality) and 46.7 s
(shift descent); the final main-module check took 53.3 s. All are below 60 s.
The delivery tool runs the required preflight. No local Lake build was run.

## Proved and sorry left

Closed the single original hole in WeilConjectures.isomorphismFieldTransportCommonStage.
Also proved WeilConjectures.commonStagePullbackNormalizedDescent,
WeilConjectures.isomorphismFieldTransportEpsilonNaturality and
WeilConjectures.isomorphismFieldTransportShiftDescent. Zero holes added and zero holes left
in the delivered Lean modules. Split off with sorry: none. Existing dependency theorems,
including isomorphismPullbackScalarShift and the common-stage coefficient specifications,
may still contain sorry; they are used as the stage-3 brief requires.

## No longer needed

The direct planned application of lem-pod-isomorphism-pullback-texact-coefficients
(Sheaf.Paper.IsomorphismPullbackTExactCoefficients) is unnecessary: the supplied stages
already contain finite rational exactness, and lem-pod-isomorphism-pullback-scalar-shift
accepts their shifts and normalized inverse lambda comparisons directly. The new shift lemma
needs no noetherian or dimension assumption. The original item signature retains all its
hypotheses unchanged.

No existing public import is removed. No existing module is withdrawn or claimed globally
unused. The proof still uses the actual coefficient quotient, the prescribed pullback
construction and coherent pair-functor descent. The source-library boundary is preserved.

## Where the brief, the DAG or earlier work was wrong

The rework row records a quarantine caused by an imported false-tail dependency; the item
source was present in the current shared tree. Its declaration, Lean attachment and dependencies
are preserved, with the proof route updated rather than the module withdrawn. No archived
path is deleted. The remote compiler supplies unpublished dependency overlays when needed.

The previous plan required identifying the supplied shifts with an independently selected
coefficient-exactness family. This comparison is unnecessary: the existing scalar-shift lemma
works directly with arbitrary shifts satisfying precisely the supplied normalization fields.
Neither a new category nor an arbitrary quasi-inverse is selected. The epsilon family is built
from the given S, and its component formula is retained after using Equivalence.mk.

## New nodes

lem-pod-common-stage-pullback-normalized-descent identifies the prescribed quotient
pullback with the normalized coherent stage-system morphism. It assumes neither
isomorphism nor shift data. Factoring this repeated proof into a proved module keeps
compilation within the per-file limit and avoids repeating expensive elaboration.


lem-pod-isomorphism-field-transport-epsilon-naturality records only naturality of the
prescribed own-stage inverse components. It assumes no opposite stage family, equivalence,
or triangle preservation. Its proof transports the finite scalar square, applies compatible
transformation descent, and identifies the prescribed components. Identity extensions, zero
objects, and the empty scheme require no extra assumption: all equations are natural-isomorphism
identities and the same quotient representative calculation applies.

lem-pod-isomorphism-field-transport-shift-descent records only descent of the supplied shifts
and their compatibility with any identity-normalized inclusion comparison. It assumes no
inverse family or exactness of the descended functor. Finite shift normalization, equality
transport of transition shifts, representative naturality, and the zero/addition laws provide
the construction. This includes every integer, including zero and negative integers. All
new nodes have actual Mathlib searches and retain the item's source, chapter and unit. The
unit's realized route is unchanged. The scoped proof-command changes are recorded in
coord/changes/isomorphism-field-transport-common-stage-proof.md; no existing
signature, public import or global instance changes.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
