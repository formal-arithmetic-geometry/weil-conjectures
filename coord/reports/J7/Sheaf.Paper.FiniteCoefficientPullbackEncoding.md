## What changed

Implemented `finiteCoefficientPullbackEncoding` with its original signature and the original
published internal-module and fixed-scalar derived pullback compositors. The proof constructs
its family rather than choosing unrelated comparison isomorphisms.

Added `Sheaf.Paper.FiniteCoefficientHeartPullback`. Restriction of scalars along the inverse
coefficient isomorphism is followed by the concrete normalized section encoding. `heart_eq`
identifies this functor with the two functors specified by the supplied encoding. Its direct
image comparison is explicitly the identity on sections. The proved scalar-action equation
from `FiniteDiscreteEncodingPullbackFixed` supplies linearity. Taking inverse mates under the
two geometric adjunctions constructs `heartPull`; invertibility follows by taking mates again
along the encoding equivalences and reflecting invertibility under conjugation.

Added `Sheaf.Paper.FiniteCoefficientHeartPullbackComposition`. The sectionwise direct-image
comparison commutes with the published direct-image compositors. The mate-pasting identities
and the published conjugation equations give `heartPull_comp`.

The constructed heart functor and its comparisons are irreducible. Their explicit equality and
mate lemmas prevent expensive unfolding in later coherence calculations. The sectionwise data
contains no equality casts from the supplied equivalence functors.

In the assigned module, private categorical helpers transport the composition equation through
exact-functor localization, the coefficient-encoding composition isomorphisms, and the published
total-left-derived-to-termwise isomorphisms. Only proof imports were added to that module.
No adopted source-library module, existing public signature, or existing definition changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback.finiteCoefficientPullbackEncoding`
(node `lem-sfb-finite-coefficient-pullback-encoding`). One original hole closed; zero holes added;
zero holes remain in the delivered modules. The two new modules contain constructed data and
proved theorems, including `inverseMate_isIso`, `heartPull_mate`, and `heartPull_comp`.
This is a proof, not a decomposition into unproved obligations.

The server checked all three modules. Separate checks of the composition module and the
assigned module took 38.8 s and 39.3 s respectively. Profiling options were then removed;
the delivery tool performs the final clean compilation and preflight. The original theorem
keeps its finite-discrete assumptions, with its unused-section-variable linter disabled
locally to retain the original interface.

## No longer needed

No existing import or module is withdrawn. The assigned module's existing public imports stay.
The new composition module imports the coherence APIs privately because only its proofs need
them. The heart module imports the existing normalized pullback module privately with `all`
to reuse its proved scalar-action lemma inside a theorem proof. Public constructions use the
new public scalar-action theorem and do not expose a private helper in their bodies.

The previous plan's `lem-weil-pbc-proetale-derived-pullback-composition` attachment is
`Sheaf.Paper.IntegralFinitePullbackComposition`, which concerns a different ringed-sheaf model.
It is not needed here: the proof uses the actual internal-module and ordinary fixed-scalar
`leftDerivedUpperStarComp` operations already present in the assigned statement. Its old
statement dependency is preserved; the actual proof dependencies and numbered steps are
updated. No claim is made that its module is globally unused.

## Where the brief, the DAG or earlier work was wrong

The plan's sectionwise pushforward helper in `FiniteDiscreteEncodingPullbackFixed` is private.
It cannot be used as data in a new public definition. This delivery constructs the comparison
explicitly, reuses the existing proved scalar-action lemma inside a theorem proof, and leaves
the original module's interface untouched.

Once the normalized encodings are supplied, the new heart construction itself does not need
separate finiteness or discreteness assumptions. The assigned theorem retains both assumptions
and every other part of its statement unchanged. Empty schemes, the zero ring, and identity
scheme morphisms use the same section and adjunction equations. The blueprint unit route is
preserved; no unit statement or realized step is removed.

## New nodes

`lem-sfb-finite-coefficient-heart-pullback` records the explicit sectionwise comparison,
its equivalence property, and its inverse-mate pullback construction. Its Lean attachment is
`Sheaf.Paper.FiniteCoefficientHeartPullback`; all attached declarations are proved or actual
constructions.

`lem-sfb-finite-coefficient-heart-pullback-composition` records the underived compositor
equation and its proof by sectionwise equality followed by mate pasting. Its Lean attachment is
`Sheaf.Paper.FiniteCoefficientHeartPullbackComposition`; its theorem is proved.

The parent node's proof, proof dependencies, and proof origin follow the implemented route.
There are no definition-change records or forced adaptations.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
