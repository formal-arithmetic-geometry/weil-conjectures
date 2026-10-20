## What changed

Proved `AlgebraicGeometry.KummerLine.kummer_affine_line` with its original statement.
The proof uses the existing proved `Scheme.kummer_finite_free_comparison` and the new,
fully proved `KummerLine.kummer_root_line_computation`. It constructs coefficient
restriction by conjugating root restriction tensor the identity, proves uniqueness by
tensor induction, and obtains scalar extension by tensor associativity.

Moved `curve`, `structureMap`, `inclusion`, `scalar`, `coordinateUnit`, `generator`, and
`rootRestriction` unchanged to `KummerLineGeometry`, publicly imported by the item.
This avoids an import cycle between the root computation and its parent. Definition names,
signatures, bodies, and original docstrings are retained. The relocation change record is
`coord/changes/Q4-kummer-line-geometry-relocation.md`; all reported consumers retain the API.

The root theorem proves connected constant-root degree zero with its normalization,
compatibility with restriction, the affine cohomological-dimension bound, and degree one
using the Kummer exact sequence, vanishing Picard groups, and the Laurent unit quotient.
Local irreducibility of `generator` and the Kummer boundary, explicit sheaf arguments,
and generic scheme helpers prevent unintended unfolding. Affine unit divisibility uses
the direct `ΓSpecIso` construction. The single root module retains the full proof.

Validation: all three production modules compiled together (13.3, 40.1, and 27.1 seconds).
After a subsequent timeout, generic restriction/boundary helpers and direct affine units
reduced definition unfolding; the revised full root proof compiled in 50.9 seconds.
The final three-module check passes without warnings (0.7, 55.8, and 33.5 seconds).
The final parent, including the local irreducibility attribute and warning cleanup, also
compiled without warnings in 31.9 seconds. The first delivery preflight requested separate LeanSearch records for the two new nodes;
those queries have now been run and their results recorded. The second dry run passed preflight (CODEX review), commit `be0da16117`. The final
axiom probes for the parent/root hit the compile limit or a busy server; the delivery
tool records that the merge reruns those probes. No forbidden axiom was reported.

## Proved and sorry left

Closed the item's sole original hole:
`AlgebraicGeometry.KummerLine.kummer_affine_line` (node `thm-pur-kummer-affine-line`).
Proved the new theorem `AlgebraicGeometry.KummerLine.kummer_root_line_computation`
(node `lem-pur-kummer-root-line-computation`) and every private helper in that module.
One of one original holes is proved; zero holes are added or split off. No `sorry`
remains in any delivered module, including definitions. The finite-free comparison is
already proved in the shared library and is used unchanged; no copy is delivered.

## No longer needed

The parent directly imports only the root computation, the finite-free comparison, and
Mathlib's tensor finiteness module. Its former public imports are exported unchanged through
`KummerLineGeometry`. `Curve.CohomologicalDimension` and `AffinePuncturedLineAlgebra` move
to the root proof, where they are used. The Kummer API remains used transitively.

The following old direct proof imports are unnecessary and removed:
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`,
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`,
`WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`,
`WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`WeilConjectures.AlgebraicGeometry.Sites.Gm`, and
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`.

The new parent proof-dependency list is precisely the root computation and finite-free
comparison. Its earlier nodes `def-sc-curves`, `lem-sc-affine-cohomological-dimension`,
`lem-sc-kummer-exact`, `def-sc-kummer-sequence`, `def-weil-pbc-sites-and-cohomology`,
`lem-sc-h1-gm-pic`, and `lem-pur-affine-punctured-line-algebra` are retained through the
root calculation. `def-pur-sheaf-tensor-product` and `def-sp-injective-resolutions` are
retained through the existing coefficient comparison. A separate application of
`lem-weil-pbc-derived-functor-long-exact` and `lem-sc-primitive-root` is not needed:
the existing Kummer exactness API already supplies the exact segment, and the primitive
root is a hypothesis, whose existing trivialization is applied directly. No existing
module or node is withdrawn; the unit route is retained.

The unlanded tail/exponent/insertion splits from the earlier sandbox draft are removed.
Neither `kummer_affine_line_tail` nor `kummer_exponent_isUnit` is added; the exponent
transport is a private proved helper, and the coefficient clauses are proved in the item.

## Where the brief, the DAG or earlier work was wrong

The earlier interrupted sandbox report claimed three remaining split holes and contained
a tail package duplicating most of the conclusion. That draft is superseded by complete
proofs. The finite-free comparison has meanwhile been proved and landed by R1, so the
older per-degree sandbox signature was stale. This delivery uses the current bundled
comparison and does not change its module or node.

Compiler timeouts arose from inferred sheaf arguments and unfolding `generator`; explicit
arguments and a local irreducibility attribute resolve them. No compile limit was raised,
no proof file was split for the time limit, and no target meaning was changed. The parent
uses an explicit sheaf argument at its degree-zero evaluation, replacing the inferred `_`
with exactly `((curve k b).rootsOfUnitySheaf (ℓ ^ N))`. This is the same elaborated type;
the preflight flags the textual annotation for independent review.

## New nodes

`def-pur-kummer-line-geometry` records the unchanged geometry definitions in their new
module. `lem-pur-kummer-root-line-computation` records the proved root-coefficient part
of the original argument with canonical generators. Its proof follows the same Kummer,
Picard, unit-quotient and affine-dimension steps. No new node carries a remaining hole.
The change record is `coord/changes/Q4-kummer-line-geometry-relocation.md`.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
