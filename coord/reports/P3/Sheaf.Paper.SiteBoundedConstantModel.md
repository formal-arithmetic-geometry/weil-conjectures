## What changed

The signature and public imports of
`CategoryTheory.exists_site_bounded_constant_model` are unchanged. Its proof now
handles the one-degree case directly, using the existing derived concentration
isomorphism, and otherwise combines a local constant graded model with simultaneous
finite differential descent. It explicitly transports the resulting chain
isomorphism through exact derived restriction and composes precoverage families.

The original module adds proof imports of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful` for the
concentration isomorphism and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` for derived
composition, together with the two new model/descent modules.

Two new modules separate the two parts of the construction:

- `Sheaf.Paper.SiteBoundedConstantGradedModel` states the cohomological induction
  with constant finite graded terms, without coefficient-module differentials.
- `Sheaf.Paper.SiteFiniteConstantComplexDescent` proves that a bounded sheaf complex
  with finite constant terms locally descends to an actual coefficient-module
  complex. This theorem needs neither Noetherianity nor points.

Another new module, `Sheaf.Paper.BoundedTopMorphisms`, proves
`DerivedCategory.exists_chainMap_to_single_of_isStrictlyLE`: a derived map from a
complex strictly bounded above by n to a single object in degree n has an actual
chain representative. This proves the boundary-representative step of the open
induction and removes its fraction argument. The new graded-model node records
this dependency. That module has no unused proof import of the helper: its proof
is still the one named hole, and the proved helper is ready for its next worker.

`Sheaf.Paper.LocalFiniteEpiLifts` proves
`CategoryTheory.exists_local_lift_from_constant_finite_free`, supplying the local
finite-free lift across the cycles-to-cohomology epimorphism. It uses Mathlib's
local-surjectivity characterization and the constant-sheaf adjunction. Thus the
remaining induction can use the epimorphism directly, without separately
identifying a presheaf quotient. The new graded-model node records this second
proved helper as a planned dependency as well.

The descent proof constructs compatible restriction comparisons from the
constant-sheaf units, takes a finite intersection of covering sieves, reflects the
square-zero identity on nonempty slices, and treats empty slices separately.
No existing definition or theorem statement changes, and no consumer adaptations
or change records are necessary.

## Proved and sorry left

Upper hole closed:
`CategoryTheory.exists_site_bounded_constant_model`
(node `lem-weil-pbc-site-bounded-constant-model`). Its new proof contains no sorry.
The case `a = b` is proved directly without the new graded-model theorem.

New theorem proved:
`CategoryTheory.exists_local_constant_complex_of_constant_terms`
(node `lem-weil-pbc-site-finite-constant-complex-descent`). Its entire proof and all
private helpers are complete. A server single-file compile with `#print axioms`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

Also proved:
`DerivedCategory.exists_chainMap_to_single_of_isStrictlyLE`
(node `lem-weil-pbc-bounded-top-chain-representative`). It constructs the top
component using the homology-to-opcycles isomorphism and proves that its
localization is the prescribed morphism using the standard t-structure. Its
source needs no projective terms, and its target needs no injectivity. Its axiom
check also reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

Also proved:
`CategoryTheory.exists_local_lift_from_constant_finite_free`
(node `lem-weil-pbc-local-finite-free-epi-lift`). It lifts the finitely many basis
sections on one common covering and extends linearly; naturality and the
constant-sheaf adjunction prove compatibility with restriction. Its axiom check
also reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

One hole added and left:
`CategoryTheory.exists_site_bounded_constant_graded_model`
(node `lem-weil-pbc-site-bounded-constant-graded-model`), whose proof is exactly
`by sorry`. This is the only sorry in the delivered files. It still needs the
assembly of the induction: using the proved finite-free local lifting to produce
the top-degree chain map, proving that its cone has finite locally constant lower
cohomology, applying induction on slices, and appending the constant free top term
along the now-proved representative of its boundary. Its docstring and node give the
complete argument. The simultaneous descent of all differentials is no longer
part of this obligation: it is proved in the other new module.

This is a decomposition: one upper hole closed, one lower hole added, net zero by
this declaration count, not an unconditional proof of the assigned theorem.
The remaining statement is strictly a part of the argument: its module family has
no module differentials at all, and its sheaf differentials need not come from
module maps. The proved descent theorem supplies those maps and proves their
square-zero relations; the original theorem supplies the derived and covering
composition. All five delivery modules passed the server compile together in import order
(2026-10-18, 13:30 local time).

## No longer needed

Removed direct proof imports from `Sheaf.Paper.SiteBoundedConstantModel`:

- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`;
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`;
- `Sheaf.CategoryTheory.TruncationDescends`;
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`;
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`;
- `Sheaf.CategoryTheory.SiteCoveringAxioms`;
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.

The last import is still used by the proved descent module; its source-level
constant restriction and local section lemmas are necessary. The
truncation, long exact sequence and Serre-property nodes remain in
the planned proof of the open graded-model node; they have been moved out of the
original theorem's immediate proof, not declared mathematically obsolete.
There are no unused proof imports in the open graded-model module. The single-degree
case uses the already proved concentration isomorphism instead of the much larger
`DerivedCategory.truncation_descends` statement. Cover refinement and composition
use Mathlib's precoverage API directly, so no declaration from
`Sheaf.CategoryTheory.SiteCoveringAxioms` is needed.

The original node now cites just concentration, the two new nodes, exact derived
functoriality and the covering axioms. Its obsolete top-level tool approvals for
`lem-pur-site-restriction-module-adjunction-exact`,
`def-weil-derived-cohomology-sheaves`,
`lem-weil-pbc-site-module-presheaf-sheafification-exact`,
`lem-weil-pbc-site-sheafification-sections-local`,
`def-weil-pbc-constant-sheaf`, `lem-sf-derived-homology-long-exact`,
`def-weil-triangulated-category`,
`lem-pc-quasi-isomorphisms-multiplicative-system`, and
`lem-pc-right-fraction-representation` are removed there; any retained uses in the
new graded-model node are recorded separately. The proved top-degree
chain-representative theorem replaces
`lem-pc-right-fraction-representation` and
`lem-pc-quasi-isomorphisms-multiplicative-system` in the new graded-model route;
those two nodes are no longer needed for this argument. The new finite-free
local lifting theorem also removes
`lem-weil-pbc-site-module-presheaf-sheafification-exact`: its quotient-identification
step is replaced by Mathlib's epimorphism/local-surjectivity API. A static comparison
of the item's old and new DAG closures confirms exactly these three removed nodes.
The local-section sheafification node remains reachable through other dependencies
and is not claimed as pruned. No target-wide module
pruning is claimed without the maintainer's closure ledger.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The original proof plan is
mathematically suitable, but its declarations do not by themselves close the
cohomological induction: the finite locally constant Serre theorem is expressed
for ringed module sheaves, whereas this item uses `Sheaf J (ModuleCat B)`, so a
proof must provide the comparison as part of that step. The generic top boundary
also needs a chain representative; projectivity of the finite graded terms cannot
be assumed. That step is now proved without fractions in BoundedTopMorphisms.
Assembly of these local lifts into the induction, and the cone-cohomology steps,
remain open. These issues do not affect
the proved differential-descent theorem.

The source's one-differential descent can be separated from the induction: finite
intersection descends every differential of any bounded constant graded model at
once. This is the route actually formalized. Empty covering members, zero modules,
the zero ring, the endpoint differential into a zero term, and an empty degree
interval are covered by the descent proof. The assigned theorem still has its
original `a ≤ b` hypothesis.

## New nodes

`lem-weil-pbc-site-bounded-constant-graded-model`, in
`dag/nodes/sec-proper-base-change/`, records the remaining positive-width
cohomological construction in
`Sheaf.Paper.SiteBoundedConstantGradedModel`. It has a complete sourced proof plan,
three actual logged Mathlib searches, and a self-contained weaker conclusion with
constant finite terms and arbitrary sheaf differentials. This is the sole new
open obligation.

`lem-weil-pbc-site-finite-constant-complex-descent`, in the same chapter and unit,
records the proved finite simultaneous differential-descent theorem in
`Sheaf.Paper.SiteFiniteConstantComplexDescent`. Its proof works on arbitrary small
Grothendieck sites, using actual module differentials and a chain isomorphism.
Three actual logged Mathlib searches found no existing theorem with that conclusion.

`lem-weil-pbc-bounded-top-chain-representative`, in the same chapter and unit,
records the proved generic boundary-representative theorem in
`Sheaf.Paper.BoundedTopMorphisms`. Its needed dependency is the Mathlib standard
derived t-structure. The node explains the top homology comparison and the
shifted-heart argument, and records three actual logged Mathlib searches.

`lem-weil-pbc-local-finite-free-epi-lift`, in the same chapter and unit,
records the proved finite-free source lifting theorem in
`Sheaf.Paper.LocalFiniteEpiLifts`. It applies on arbitrary small sites, including
rank zero and empty slices. Its proof uses actual linear combinations of chosen
basis preimages and the constant-sheaf adjunction; three actual logged Mathlib
searches found the ingredients but no direct matching theorem.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
