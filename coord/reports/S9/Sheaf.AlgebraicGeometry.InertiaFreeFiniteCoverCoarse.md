## What changed

Proved AlgebraicGeometry.inertiaFreeFiniteCoverCoarse with its signature unchanged.
The proof follows the six geometric steps already recorded in its node: finite
representable stack properties, trivial geometric inertia, coarse properness and
local quasi-finiteness, composition and equivalence invariance, separated locally
quasi-finite space representability, and proper locally quasi-finite finiteness.
Imported the existing modules supplying the three stack-property inputs and their
composition/compatibility theorem. Private proved helpers supply the categorical
glue: maps between discrete moduli categories, their cartesian lifts, scheme stack
descent and DM presentations, presheaf pullbacks as 2-fibre products, based
quasi-inverses, and equivalence of 2-fibre products after replacing the right factor.
The last helper preserves the first projection strictly, so the final finite
scheme tests refer to the specified composite, not an unrelated morphism.

Added proof imports for scheme algebraic spaces, representable etale scheme tests,
Yoneda density, connected limits in over categories, and the existing comparison
between the project's and Mathlib's local quasi-finiteness. All imports are private
except the unchanged public statement import. Updated the item's DAG proof and
proof dependencies to describe the actual Lean argument, including the scheme-test
conclusion. No interfaces, definitions, consumers or target statements changed.

Verification: lcompile.py compiled the complete file without warnings, with no
textual sorry. Delivery preflight also checks every declaration's axioms. The
geometric dependencies remain existing named theorems, some with their own sorry;
this delivery closes the item's proof from those statements, without claiming
those dependencies have been proved here. No surjectivity or reductivity hypothesis
was added. The constructions allow empty schemes and nonreduced scheme tests.

## Proved and sorry left

Closed 1 of 1 original holes: AlgebraicGeometry.inertiaFreeFiniteCoverCoarse
(lem-sfb-inertia-free-finite-cover-coarse). Added 0 holes; split off 0 statements.
Every private helper is proved. No sorry remains in any delivered Lean file.

## No longer needed

Removed the proof import
WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf.
Its node lem-weil-pbc-small-etale-representable-presheaf-sheaf is unnecessary for
this proof: big-etale subcanonicity directly supplies the covering-sieve colimit
used to prove descent of the discrete scheme stack. Removed that dependency and
its obsolete tool-use entry from this item's node. This is pruning of this item's
route only; other consumers of that module are unaffected.

All other original imports and geometric dependencies remain needed. No module
is withdrawn. The added imports Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
and Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests provide
the existing scheme-space construction and etale scheme-map comparison, used as
tools rather than replacing any unit route. No unneeded imported theorem is
proved or restated. The exploratory direct Whiskering import was removed because
its declarations are already available through the proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original scheme-stack step cited a small-etale sheaf theorem, while the
actual IsModuliStack interface uses covering sieves of the big etale over-site.
Mathlib's existing subcanonical topology instance provides the exact gluing
needed; the node and declaration proof description now say this explicitly.
The original plan also left implicit the representable-finite conclusion after
constructing g:Z→Q. The proof now constructs every finite scheme test by pulling
back g and proves the necessary equivalence and first-projection compatibility.
The existing geometric dependency statements fit without any repair.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
