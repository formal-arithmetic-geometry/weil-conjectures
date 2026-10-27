## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etale_relation_quotient` in
`Sheaf.AlgebraicGeometry.EtaleRelationQuotient`, with its statement and
`relationQuotientMap` unchanged. The proof follows the current five-step DAG plan:
affine chart quotients, affine representability and atlas properties, coproduct and
open gluing, global presentation properties, then the coequalizer universal property.

Added six fully proved private helpers. In particular, the quotient kernel-pair
identity proves injectivity of the presheaf quotient unit. Restricted quotient
presheaves embed into it, so their sheafifications are constructed as subsheaf
closures inside the supplied sheaf. This supplies the sheaves required as inputs
by the affine-cover lemma without a large-site sheafification instance or arbitrary
object chosen from a mere existence hole. All selected quotient sheaves have their
universal property; the sheaf coproduct is characterized by its colimit property.
The proof of scheme-source representability is a direct diagonal pullback argument.

Updated the existing node's proof, proof dependencies and proof origin. Added only
private proof imports. No public signature, definition, target, or other module changed.
The module-level universe command adds `v` and `w` for the generic private helpers;
this elaboration-context change is recorded in
`coord/changes/J7-etale-relation-quotient-proof-universes.md`.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.AlgebraicSpace.etale_relation_quotient`
(node `lem-trf-etale-relation-quotient`). Added 0 holes; split off 0 statements.
There are no remaining `sorry`s in the delivered module. Its imported statement
lemmas retain their existing holes; this is a proof from those declarations,
not a claim that the entire transitive argument is axiom-free yet.

Verification: server single-file compilation through lcompile.py; final delivery
preflight also compiles and checks the packet. No local Lake command was run.

## No longer needed

Removed direct proof imports `WeilConjectures.AlgebraicGeometry.FpqcDescentEtale`
and `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens`: the current affine-cover
and representable-presentation declarations encapsulate those arguments. Their
nodes `lem-galois-fpqc-descend-etale` and
`lem-trf-etale-relation-finding-opens` remain needed by those dependencies; no
whole-library pruning or withdrawal is claimed. The restriction module remains
needed for its actual restricted-relation definitions, but its theorem is not
used directly here. Likewise no separate import or direct use of
`lem-weil-pbc-scheme-coproduct-family` is needed: the affine-cover interface already
uses the categorical coproduct, whose universal property Mathlib provides.

No node or module is withdrawn. All current unit routes are preserved. Added the
existing pullback-relation-presheaf and sheaf-coproduct-partition nodes to the
item's proof dependencies because the Lean assembly explicitly needs their
injectivity and coproduct-existence clauses. Avoided importing the broader
`AlgebraicSpaceRepresentableEtaleSchemeTests` theorem by proving the required
diagonal test directly.

## Where the brief, the DAG or earlier work was wrong

The module's original docstring and imports predated the current DAG's two new
assembly lemmas. Updated the docstring to match the proof. The affine-open-cover
lemma quantifies over quotient sheaves; it does not assert their existence. The
proof now fills that interface gap using the concrete subsheaf construction,
rather than assuming general Type-u sheafification on the big scheme site.

Checked empty affine index sets, empty test schemes, the diagonal relation, and
overlapping affine charts: no nonemptiness, disjoint chart-image, affine overlap,
or separated-base assumption is introduced. Private helper statements are
unconditional consequences of their stated kernel-pair or representability
hypotheses. The unit record has no realized node requiring a different route.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
