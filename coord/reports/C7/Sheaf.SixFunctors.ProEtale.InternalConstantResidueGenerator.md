## What changed

Reduced the singleton-generator obligation to a generic comparison of two actual
coefficient presentations. The item now has a complete Lean proof from the comparison
and the existing constant-coefficient kernel calculation. The proof identifies the
lifted first coefficient ideal, transports its principal kernel through the commuting
quotient square, then constructs the prescribed generating sections on every slice.
No existing statement or definition was changed.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.residue_generator` (1 of 1).
Added one split-off hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_quotient_comparison`.
This is a decomposition, not a net reduction in holes: one closed and one added.
The new statement concerns ring-sheaf isomorphisms and their quotient square only;
it asserts no ideal-kernel formula, epimorphism, or generating sections.
The singleton-generation and ideal-transport arguments are complete in Lean.

## No longer needed

No original public imports, modules, or planned dependency nodes were removed.
The plan's transport of a free-module epimorphism through internal module equivalences
is replaced by transport of the coefficient quotient square and the already proved
sectionwise generation helper. Thus no new exactness or free-module transport theorem
is needed. Proof-development imports of FiniteDiscreteOrdinaryEncoding and
FiniteDiscreteSchemeRing were removed from the delivered comparison statement module;
they supplied useful proof patterns but are not needed by its signature.

## Where the brief, the DAG or earlier work was wrong

The previous source-absence obstruction is resolved: both the assigned module and
InternalCompletionSectionTransport are present in the current shared checkout.
The constant-coefficient theorem applies to standard constant ring sheaves; it does
not directly identify the reconstructed ring and quotient used here. The new node
isolates precisely that coefficient-presentation compatibility, independently of the
uniformizer and of ideal generation. Its proof in words uses the already proved
monoidal constantSchemeIso, naturality of sheafification, section reconstruction,
and the AsSmall equivalence. The generic statement includes the zero ring, I=0,
I=top, and the empty scheme; none requires coefficient finiteness or Noetherianity.
The new lemma's isomorphisms are only eliminated inside a theorem proof, so no data
is defined by choosing an arbitrary witness from an unproved existence theorem.

## New nodes

`lem-sfb-internal-discrete-quotient-comparison`, in
`Sheaf.SixFunctors.ProEtale.InternalDiscreteQuotientComparison`.
It serves the coefficient-presentation step of integral-models proof (1).
The current blueprint was searched for constant-sheaf comparisons; no blueprint
statement states this exact reconstructed quotient square. Existing generic APIs and
proof patterns were read before introducing this statement. The item node's proof
and dependencies were updated to match the Lean argument.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
