## What changed

Proved `CategoryTheory.exists_cartanEilenberg_rows` without changing its signature or any
existing public import. Added proof imports of `CartanEilenbergObjectResolutionRows` and
`Limits.Preserves.Shapes.Images`; retained the prescribed
horseshoe import because the proof actually applies that theorem to the term rows.

Added two fully proved helper modules. `CartanEilenbergBoundaryProjection` constructs the
image projection with the required integer indexing and the image inclusion into cycles,
with their factorization identities. `CartanEilenbergObjectResolutionRows` resolves only
boundary/cycle/homology rows. The main proof constructs the other rows by horseshoe,
transports cycles/images/homology along explicit canonical isomorphisms, verifies all four
compatibility equations, and obtains injectivity and quasi-isomorphisms from the resolutions.

Choose boundary and homology resolutions independently, then apply prescribed horseshoe to
resolve cycles, and apply it again to resolve terms. Sharing the same boundary and cycle
columns makes recursion unnecessary. No new definition chooses data from an existence
statement: the two definitions are explicit image/kernel constructions; horseshoe witnesses
are eliminated only inside theorem proofs.

Checked boundary cases: boundary columns are zero for p <= 0, homology columns are zero for
p < 0, and short exactness forces the cycle and term columns to be zero in negative degrees.
At p = -1 the next boundary column is the degree-zero zero column. At p = 0 the second row
identifies the cycle and homology resolution complexes. No injectivity of nonzero source
objects or boundedness above is assumed.

All three files compile together through lcompile.py without errors or warnings. The source
was read at [Stacks 015I](https://stacks.math.columbia.edu/tag/015I) and
[Stacks 013T](https://stacks.math.columbia.edu/tag/013T), because the listed local derived.tex
is absent on this machine. The independent-choice rearrangement is an agent-written proof
using the same two source rows and the project's stronger prescribed-end horseshoe theorem.
The unit record has empty realized fields; no unit statement or step was bypassed.

## Proved and sorry left

Closed the original hole in `CategoryTheory.exists_cartanEilenberg_rows`
(node `lem-sp-cartan-eilenberg-rows-exists`). One original hole closed; zero holes added;
zero holes split off. There is no sorry in any delivered module.

Also proved `CategoryTheory.exists_cartanEilenberg_object_resolution_rows`
(node `lem-sp-cartan-eilenberg-object-resolution-rows`) and the two factorization lemmas
`CategoryTheory.cartanEilenbergBoundaryProjection_fac` and
`CategoryTheory.cartanEilenbergBoundaryInclusion_fac`
(node `def-sp-cartan-eilenberg-boundary-projection`). Both new definitions have real data.
The main proof retains the existing prescribed horseshoe theorem and its dependencies;
this delivery does not assert that all downstream library dependencies are sorry-free.

## No longer needed

No existing import removed; no existing node or module pruned. The second reader removed
the redundant newly added proof import `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`
and replaced the boundary helper's broad `Mathlib.Algebra.Homology.QuasiIso` public import
with `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, which its signatures need. The main node's former direct
use of `lem-weil-pbc-left-exact-injective-resolution-degree-zero` moved to the new
object-resolution-row node, where `InjectiveResolution.of` supplies the free resolutions.
It remains needed in the transitive proof dependencies. The sequential recursion and a
prescribed initial cycle resolution from the original plan are unnecessary, but are not
separate modules or nodes to prune.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than necessary: both end resolutions may be chosen
first at every degree, so two independent families of horseshoe applications give all shared
columns. The main node now records this route. The existing theorem docstring still gives
its valid original alternative proof plan; the delivered node and helper docstring explain
the implemented proof.

No statement or definition was disputed or changed, no module held by another group was
adapted, and no tool was bypassed. LeanSearch was unavailable (Internal Server Error);
LeanFinder, Loogle, and searches of the pinned Mathlib and project sources were used.
The blueprint ancestor utility cannot follow this item's created.item chain because it is a
module name. The new nodes record the existing ancestor route through
`lem-sp-cartan-eilenberg-exists` to `thm-sp-grothendieck`, as the existing node records do.

## New nodes

`def-sp-cartan-eilenberg-boundary-projection`: the explicit integer-indexed boundary
factorization maps, in `Sheaf.CategoryTheory.CartanEilenbergBoundaryProjection`, including
both proved factorization identities. No postponed proof.

`lem-sp-cartan-eilenberg-object-resolution-rows`: only the boundary/cycle/homology resolution
rows, in `Sheaf.CategoryTheory.CartanEilenbergObjectResolutionRows`. Proved by the existing
prescribed-end horseshoe theorem, with explicit zero resolutions in the exceptional degrees.
It contains no term resolution or compatibility with the prolonged source complex; those
parts are proved by the main module. No postponed proof and no change record.

## Second reading by M1

1. Compared the existing module with the repository by diff. The sole existing theorem's
   signature and docstring are byte-for-byte unchanged; only proof imports and its proof
   body differ. The other two modules are new, not adaptations. No existing definition,
   hypothesis, conclusion, visibility, or public import changed. Verdict: pass.
2. Read all three modules and compiled the complete set locally with lcompile.py, with no
   errors or warnings. Searched for forbidden declarations and sorry: none occur. Printed
   axioms of both new definitions, both factorization theorems, the object-row theorem and
   the existing theorem in scratch copies. All use only propext, Classical.choice and
   Quot.sound; no sorryAx. The image/kernel definitions construct their data explicitly.
   Choices of horseshoe witnesses occur only inside theorem proofs. Verdict: pass.
3. There are no split-off holes. Read the new helper statements as independent claims:
   the object-row theorem omits all term rows and is strictly a part of the construction.
   Checked the zero complex, negative degrees, p=-1 (next boundary degree zero), and p=0
   (zero boundary, cycle/homology isomorphism). No boundedness above or source injectivity
   is needed. Repeated searches with the different phrases 'resolve the middle of an exact
   sequence with fixed injective resolutions at both ends' (LeanFinder),
   '"InjectiveResolution", "ShortComplex"' (Loogle: no hits), and
   '"HomologicalComplex", "image"' (Loogle: only subobject equalities). Searched Mathlib,
   the upstream source and lean/ for image/cycle factorization and resolution rows.
   Existing primitives supply the factorization proofs and the prescribed horseshoe;
   no existing declaration supplies this compatible row family. Verdict: pass.
4. Followed the proof from the target downward: the source kernel/image exact row and
   the reused boundary/cycle resolutions give term resolutions; canonical mapped cycles,
   images and homology give all four augmentation equations. The route uses the existing
   prescribed horseshoe twice, with no recursive construction or new unproved assertion.
   Checked every import and removed the redundant new ExactFunctor import. Narrowed the
   new boundary helper's QuasiIso import to ShortComplex.HomologicalComplex. The original
   proof dependency for free resolutions moved into the object-row helper and remains
   needed transitively; no old dependency becomes unused in the closure. The unit
   sk-prop-av-pqf-finite has empty realized.statement and realized.steps entries; no
   realized unit route is bypassed. Verdict: pass.
5. Read all three delivered nodes against Lean. The main proof steps and proof_deps
   describe exactly the implemented two-horseshoe route and transport equations;
   proof_origin correctly marks the rearrangement as agent-written. New nodes include
   sources, creation records, blueprint ancestry, search records, chapter/unit and Lean
   declarations. Their proof_deps are exactly the unions of step uses. Updated the two
   new nodes' lean.statement fields to verbatim signatures (the tool records def without its noncomputable modifier) and added
   the independent
   Loogle search to the object-row node. Verdict: pass.

Second reading changed only import minimality, the two new nodes' verbatim signature
records, the object-row search record, and this report. No proof repair was necessary.
One original hole closed, zero holes added, zero split off; no module pruned.
