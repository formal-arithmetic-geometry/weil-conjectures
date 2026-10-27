## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_separated_lqf_affine_relation_cover`
with its exact original statement. All work is in its original module, using fully proved
private helpers. The proof constructs the affine atlas open cover over target affine opens,
checks coverage on every scheme test by residue-field lifts, constructs the effective
kernel relation and its fppf sheaf quotient, proves its closed immersion into the relative
scheme product and hence affineness, and constructs all arbitrary-base-change witnesses.
Updated the existing node's proof and proof dependencies to match the Lean proof.

The final file compiles as one module. There are no definition, signature, public-import,
attribute, or consumer changes, and no new public declarations or modules. Initial sandbox
supporting files have been incorporated as proved private helpers in this one module.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.exists_separated_lqf_affine_relation_cover`
(node `lem-a1-separated-lqf-affine-relation-cover`).

Holes added: 0. Sorries left: 0. Split off: 0. Every private helper is fully proved.
Single-file lcompile validation succeeded; the delivery preflight checks all declaration axioms.
Existing imported affine-atlas-cover, permanence and fibre-product results remain dependencies.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`
and `Sheaf.AlgebraicGeometry.EtaleAtlasPresentation`. Their nodes
`lem-a1-space-etale-open-image` and `lem-a1-etale-atlas-presentation` are not used by
this proof: open inclusions are identified with their ranges directly, and quotient
existence and its universal property are proved by fppf local surjectivity and Mathlib's
range/subsheaf closure construction. Also removed the explicit proof import
`Mathlib.AlgebraicGeometry.Restrict`, which the final proof does not need explicitly.
No source-library declaration or module is withdrawn. These dependencies may still be
needed by other consumers or by the internals of the retained imported lemmas.
All public imports were preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's atlas-presentation citation does not directly supply the scheme kernel pair or
existence of the quotient reflection: its Lean interface takes R, its pullback square,
and a quotient sheaf with its universal property as inputs. The proof constructs the
kernel pair from representable etaleness and establishes the quotient universal property
itself, without a global sheafification instance on the big site. The mathematical
statement and the unit route are unchanged. Empty scheme tests and arbitrary non-affine
base changes are covered by the same pointwise and categorical arguments.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
