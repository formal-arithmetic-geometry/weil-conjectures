## What changed

Strengthened the existing proved private specialization
`CategoryTheory.brownHypotheses_finiteIntermediateField` in
`Sheaf.SixFunctorsBasics.BrownHypotheses`: it now establishes the full Brown bundle
for all six coefficient alternatives supported by the finite-field compactness and
smallness declarations, rather than only the canonical ring of a finite extension
of Q_l. The geometric base is still the algebraic closure in a FiniteFieldDatum.

The proof explicitly constructs `finiteCoefficientLiftIso` by postcomposition with
the ULift ring equivalence. This handles the finite-ring universe mismatch: the
compactness declaration uses a carrier in Type 0 whereas the smallness declaration
expects one in Type u. The other five cases use the zero finite ring and the specified
finite intermediate field, or the bottom intermediate field for an unused parameter.
The proof then constructs a small skeleton, applies internal compactness, transports
compactness to arbitrary representatives by isomorphism, and uses the existing
orthogonal/minimality argument for generation.

The original public theorem `CategoryTheory.brownHypotheses`, the definition
`CategoryTheory.BrownHypothesesFor`, every public import and all existing visibility
are unchanged. No source-library module is edited. The node's proof and proof_origin
now describe the six-case supported assembly. The private-helper signature extension
is documented in `coord/changes/N1-brown-six-coefficient-specialization.md`.

Validation: the delivered module compiles cleanly through the required lcompile.py.
The specialization has no new sorry. This is additional proved specialization of an
already disputed theorem, not a proof of its arbitrary-field assertion.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split off: 0.

`CategoryTheory.brownHypotheses` (node `sk-lem-brown-hypotheses`) remains the sole
sorry, with exactly its original signature and proof body. It is still
STATEMENT-DISPUTED. It is neither renamed nor reduced to a new unsupported theorem.

`CategoryTheory.brownHypotheses_finiteIntermediateField` now has a complete Lean
proof for all six supported coefficient cases. The new private
`CategoryTheory.finiteCoefficientLiftIso` is completely proved by explicit maps.
The other existing private helpers remain proved, including localizing closure,
orthogonal zero detection, generation, formal Brown assembly and compactness
transport along isomorphisms. These proofs use existing named declarations, some
of which retain their own separate holes; no transitive axiom-closure claim is made.

## No longer needed

No imports, nodes or modules are removed. The existing smallness, structural and
finite-field compactness dependencies remain needed. The generation detail remains
needed transitively through finite-field compactness. No source declaration is
withdrawn, and no unit route is bypassed.

The finite-rational-only specialization has been strengthened in place: every former
instance is covered by choosing the fifth coefficient alternative with the identity
coefficient isomorphism. The old specialization is not a pruned module or a closed hole.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the final theorem is not a consequence of the listed compactness
declarations under its actual hypotheses. Its field k is arbitrary of characteristic
p > 0, while `brownHypothesesFiniteFieldCompactness` and
`WeilConjectures.brownHypothesesGeneration` require the algebraic closure of a finite
field carried by a FiniteFieldDatum. There is no way to construct such a datum from
these field hypotheses. The original source's standing setting explicitly imposes
no further field condition. Its finite-coefficient proof silently needs absolute
finite ell-cohomological dimension in order to commute unbounded derived sections
with sums. Finite type only gives a relative bound, not a bound on the base field.
The previously reviewed generation node records the same issue and the field
restriction; the existing U1, H1 and A4 deliveries already report it. This packet
preserves the disputed theorem rather than silently restricting its public statement.

There is a separate coefficient mismatch. The public admissibility predicate has
seven alternatives: it includes all continuous maps into PadicAlgCl as well as the
finite-subextension-valued condensed object. The smallness and compactness declarations
cover the latter algebraic-closure coefficient, not the former. The proof never asserts
an isomorphism between these different objects. In particular the newly constructed
ULift isomorphism only changes the universe of a discrete finite ring; it does not
resolve the all-continuous-map algebraic-closure case.

The actual repair completed here is the full six-case assembly and finite-ring
universe conversion left out of the previous finite-extension specialization. It
is useful proved work, but does not close the arbitrary-field hole. Closing that
hole requires a mathematically reviewed correction of the field/coefficient range
and its parents, rather than additional proof search for the invalid implication.

Consumer audit: downstream.py reports zero live downstream modules. Searching the
preserved quarantine finds LocalizingExceptionalAdjoint (two calls),
ExceptionalInverseImageExistence (one call), BrownExceptionalAdjoint and
MateOpenRestriction. Their statements and calls are preserved unchanged and no
quarantined module or node is withdrawn. Existing arbitrary-field parent proofs
therefore continue to expose the original dispute. No public statement or definition
has changed, so no consumer adaptation or target review is triggered by this packet.

Searches run in this session: LeanFinder returned derived-category infrastructure
without a compact-generation match; Loogle for IsCompactObject returned no hits;
the launcher grep returned no hits. Direct rg searches read the project Brown,
compactness, smallness and coefficient APIs. Their signatures supply exactly the
six cases proved here and do not supply the missing arbitrary-field implication.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
