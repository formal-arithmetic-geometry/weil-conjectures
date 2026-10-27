## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralResidueProperFormulas`
from the finite proper formulas and the normalized quotient comparison rectangles.
A private generic adapter supplies the finite theorem's bundled constructibility
inputs and translates the scheme morphism to the over-category before specializing
to the residue coefficients. The exchange proof evaluates its comparison rectangle
and cancels the invertible comparisons. The projection proof cancels the tensor,
pullback and direct-image comparisons in the projection equation.

Private coefficient glue identifies the absolute-value and spectral-norm metrics,
their integer-ring topologies, and the quotient and discrete topologies. A record
contains the coefficient rings, their structures and the actual reduction map;
scalar extension is derived canonically from that map. Equality of this data
transports the entire assertion while preserving its canonical maps. The residue
ring is finite and killed by l, using the coefficient finiteness and DVR theorems.

Exported the existing proved `finiteProperBaseChange_of_coefficientIso` helper in
`Sheaf.Paper.FiniteProperBaseChange`, with its projection clause stated using
`moduleObjectProjectionMap`. Its existing proof unfolds that map, and the public
finite theorem unfolds it when applying the helper. The public finite theorem
statement is unchanged. Public imports expose the encoding and projection APIs
needed by the exported signature; the original private encoding import remains.
See `coord/changes/P6-finite-proper-coefficient-iso-public.md`.

Three proved public local instances supply the existing canonical module closed,
symmetric and flat-resolution structures with the pulled commutativity proof
explicit. They register no additional search rules for importers and have exactly
the canonical data. See `coord/changes/P6-residue-canonical-instances.md`.

Every original public statement and import is retained. Proof imports supply the
finite theorem, quotient comparisons and topology APIs. No `WeilConjectures`
module is edited. The unit's finite-reduction route is preserved. Transparency
checks remain enabled.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidueProperFormulas`
(blueprint `lem-sfb-integral-residue-proper-formulas`). Holes closed: 1 of 1.
Remaining holes in the item: 0. Holes added: none. Split-off statements: none.
Neither submitted Lean module contains a sorry. The finite helper was already
proved; exporting it closes no additional hole.

The complete item compiled in 49.8 seconds with no Lean errors in the final timing
check. Profiling options were removed for delivery. The finite helper module and
its four direct consumers also compiled. The delivery command performs the final
compilation and packet checks.

## No longer needed

The item does not need a separate coefficient-isomorphism transport proof:
`lem-sfb-condensed-coefficient-iso-constructible` and
`Sheaf.Paper.CondensedCoefficientIsoConstructible` are removed from its direct
proof dependencies because equality of coefficient data transports the assertion.
They remain dependencies of the finite theorem, so this delivery does not withdraw
them or claim global pruning.

`lem-sf-finite-discrete-normalized-encoding` and
`Sheaf.Paper.FiniteDiscreteOrdinaryEncoding` need no separate import in the item:
the finite helper exports the encoding API it already uses. They remain transitive
dependencies. The tentative direct import of
`Sheaf.NumberTheory.Padics.IntegersCosetBasis` was removed because continuity of
reduction is already the proved API of `def-sfb-integral-quotient-coefficients`.
No existing module is withdrawn. Global modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The original plan described transport by coefficient equivalences. These two
specific presentations agree after equality of their topology structures, so
equality transport is shorter and fixes the actual quotient map. The finite
coefficient-isomorphism helper already proves the required finite formulas; its
private visibility prevented reuse. The delivery exports it with a change record
instead of duplicating its proof.

The original statement requires neither completeness nor bounds on the integral
inputs. The proof uses neither: comparisons are ambient, and only the stated
first reductions must satisfy the finite theorem's constructibility conditions.
Arbitrary base-changed schemes, empty schemes and zero inputs are covered by the
same functorial identities.

The private transport builds kernel-checked heterogeneous congruences. It caches
congruence lemmas by function head and arity using
`Lean.Meta.mkHCongrWithArityForConst?`; Lean generates and checks those lemmas.
Cached equalities respect binder scope. The construction uses proof irrelevance,
structure projection reduction, arithmetic index normalization and function
extensionality for the quantified predicates. It uses no unchecked kernel option.
Map equalities are transported directly to isomorphism propositions to avoid
repeated rewriting through the large derived-functor expressions. No debug module,
profiling option or checkpoint logging is included in the packet.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
