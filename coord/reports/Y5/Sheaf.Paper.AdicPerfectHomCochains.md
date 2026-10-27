## What changed

The statement of AlgebraicGeometry.Scheme.adicPerfectHomCochains is unchanged.
Its proof now constructs the comparison in the reverse direction, from realized
algebraic quotient cochains to ordinary sheaf cochains, and then inverts it.
The new proof import Sheaf.Paper.AdicPerfectModuleHom supplies a comparison for
one pair of modules. The module-level comparison has no complexes, differential,
cochain degree, bounds or cohomology.

The assigned module proves the following assembly steps explicitly. Component
projection and single-cochain inclusion are linear. Their finite sum is the
identity for a bounded source. Applying an additive functor preserves that
identity and makes the realized component projections jointly injective.
Two-variable naturality gives a chain map: the proof checks the two summands of
the signed Hom differential separately. Bijectivity on each module Hom, together
with the finite support identity, proves the chain map is an isomorphism.
Naturality of the actual quotient transition and the single-module balancing
identity prove its successor square in every degree. Inverting the chain map
gives precisely the original displayed equation. The generic comparison is kept
irreducible after its component formula and bijectivity are proved, so the
concrete successor argument uses its API rather than expanding scalar-extension
data. The finite assembly is stated for abstract additive functors and successor
maps, and its concrete application supplies the fixed quotient models. The
ordinary balancing equations are proved with an abstract isomorphism parameter,
so category identity laws are checked without expanding scalar-extension data.
Both realization functors have explicit codomains. A small diagram interface
records the quotient objects and their fixed balancing isomorphisms. The
two-stage realization and balancing-component identities are assembled with
abstract categories and functors; transport from the original model then uses
a single proved equality of diagrams. This avoids normalizing concrete
scalar-extension data while comparing mapped complexes.

AdicPerfectModuleHom defines only the actual module realization functors and the
ordinary successor balancing isomorphism. These are explicit compositions of
the existing constant, scalar-extension and slice functors and existing
normalized balancing isomorphisms. There is no data chosen from a mere existence
theorem and no sorry in any definition or private helper.

Validation: both sandbox modules compiled in import order through lcompile.py.
The assigned file took 41.8 seconds with profiling enabled; the module comparison
file also compiled. The delivery removes all profiler options and diagnostic
commands. The import-direction check passes; the original theorem signature is
verbatim unchanged, and every Lean line is at most 100 characters.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.adicPerfectHomCochains
(node lem-sfb-adic-perfect-hom-cochains). The assigned module has zero remaining
holes.

Added one hole, exactly the whole proof of the public theorem
AlgebraicGeometry.Scheme.adicPerfectModuleHom
(node lem-sfb-adic-perfect-module-hom). This is a decomposition: one hole closed,
one single-module hole added, net zero. The remaining theorem is the module
quotient/evaluation calculation, with two-variable naturality and its ordinary
scalar successor identity. The finite cochain product, the signed differential,
the chain isomorphism and the cochain successor equation are all assembled in
Lean in the assigned module, rather than included in the remaining hole.

## No longer needed

No existing public import is removed. No module is withdrawn or claimed pruned
from the targets' import closure.

The original direct proof dependencies
lem-pur-site-constant-module-hom,
lem-weil-pbc-site-constant-restriction and
lem-sfb-adic-constructible-finite-reductions now belong to the lower single-module
calculation. They remain needed there and are not globally pruned. The assigned
node records the module comparison and the existing definitions as its direct
proof dependencies. The proof uses only additivity of constant sections; it
needs no exactness, weak contractibility or Noetherian hypothesis.

## Where the brief, the DAG or earlier work was wrong

No statement was weakened or disputed. The supplied dependencies provide the
constant internal-Hom comparison, slice sheafification and scalar balancing, but
do not state the ordinary quotient Hom comparison with its successor equation.
The new theorem isolates that single-module calculation. In particular it does
not rename the original complex comparison: it has no complexes or degree
bounds, and the finite-support and signed-differential arguments are proved
separately in the assigned module.

The lower statement was checked on a zero source, zero target, the zero ring,
J=0, J=top and empty slices. The cochain assembly includes empty intervals a>b,
zero source terms outside the interval, and arbitrary unbounded Q. A finite
projective source is finitely presented, so the constant internal-Hom theorem
applies after quotient scalar extension. No hypothesis on the target module is
introduced.

The source read is proetale.tex, the connected-adic-lisse proof, Tag 09C6 and its
displayed quotient total-Hom calculation, together with the existing Tag 093T
constant-module Hom interface. The current blueprint integral-model unit and its
realized steps remain unchanged. The ancestor helper cannot follow the inherited
created.item field, which names a Lean module; the new node retains the item's
explicit blueprint ancestor and extends its recorded via path.

## New nodes

lem-sfb-adic-perfect-module-hom states the natural ordinary quotient Hom
comparison for a single pair of modules, invertible for a finite projective
source and compatible with the actual successor scalar balancing. Its source,
complete proof in words, executed Mathlib searches and verbatim Lean attachment
are recorded. Its module contains that one public theorem and the explicit
module realization functors used to state it. The existing node changes only in
proof, proof_deps and proof_origin. No existing statement, definition, signature
or public import changes, so no change record or consumer adaptation is needed.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
