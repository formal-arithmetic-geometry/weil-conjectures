## What changed

Reduced two of the three original holes of
`Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`, without changing any existing
signature, definition, visibility or public import.

`CategoryTheory.ringHomReplacement_quasiIso` now applies the existing
`CategoryTheory.quasiIso_homComplex_map_of_bounded_exact_terms` to the proved
functorial K-injective resolution quasi-isomorphism. For each source term it supplies
internal-Hom exactness from the new ordinary-module dependency
`SheafOfModules.ringProjectiveInternalHomExact`.

`CategoryTheory.perfectRHomBaseChangeModel_exists` now unpacks the given source
representative, obtains K-flatness and extended projectivity from
`CochainComplex.ringBoundedProjectiveExtension`, and uses the existing
`CochainComplex.exists_isKFlatResolution` on a complex representative of the arbitrary
object K. It constructs targetIso from the localized resolution map and the
representative isomorphism. Both counit proofs unfold the actual counit composite
and combine its isomorphism factors. Extended boundedness is proved directly:
an additive functor preserves the zero terms outside the original interval.

Added three proof-only imports: BoundedExactTermHomQuasiIso,
RingProjectiveInternalHomExact and RingBoundedProjectiveExtension. Each new theorem
has its own module and node. Updated the item's proof, proof_deps and proof_origin.
All three delivered modules compile cleanly with lcompile.py --all. The main
module took 53.1 seconds in the final clean compilation. One earlier compilation
hit the 60-second timeout; repeated single-file compilation and the final ordered
compilation passed within the limit.

## Proved and sorry left

Holes closed in the item:
- `CategoryTheory.ringHomReplacement_quasiIso`.
- `CategoryTheory.perfectRHomBaseChangeModel_exists`.

These are decompositions, not two axiom-free mathematical proofs: two strictly
smaller holes are added below them. Net holes closed minus added is zero before
any subsequent proofs of the dependencies.

Original hole left unchanged:
- `CategoryTheory.ringRHomBaseChangeData_exists`, node
  `def-pc-perfect-rhom-base-change-map`.

New holes:
- `SheafOfModules.ringProjectiveInternalHomExact`, node
  `lem-pc-ring-projective-internal-hom-exact`.
- `CochainComplex.ringBoundedProjectiveExtension`, node
  `lem-pc-ring-bounded-projective-extension`.

The first new theorem has no complexes or derived categories. It supplies ordinary
projective Hom exactness on the unique-object site's slice. The second has no
derived objects, counits, K-flat target resolutions, Hom comparisons or perfect
model data: it supplies the bounded source's K-flatness and termwise projectivity
under scalar extension. Neither is a renamed version of the hole it reduces.
No data is chosen in a definition from a mere unproved existence statement.
The resolution witnesses are used locally to prove an existence theorem, which
introduces no new definition or arbitrary global choice.

## No longer needed

No original imports removed and no entire original proof-dependency module is
pruned: all six original imports are public and provide types or operations in the
existing signatures and definitions. The original item node had no proof_deps.
The new proof-only imports are all used.

For the Hom-replacement argument, no separate conversion to categorical
projectivity, bounded-above K-projectivity theorem, mapping-cone argument or
`lem-sc-bounded-above-projective-kprojective` / Mathlib declaration
`CochainComplex.isKProjective_of_projective` is needed. That node was
not an original dependency of this item, so this is avoided work rather than a
claim that the module leaves the targets' global import closure.
Finite generation is not used for this argument and no finite-projective
scalar-extension Hom isomorphism is imported. For model existence, no
`lem-pc-perfect-ring-hom-kflat`, `lem-pc-perfect-ring-hom-scalar-extension`,
`Sheaf.Algebra.Homology.PerfectRingHomKFlat` or
`Sheaf.Algebra.Homology.PerfectRingHomScalarExtension` is used: those concern the
comparison after model data has been constructed, and importing them here would
be circular. No unit statement or required unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt supplied only the Hom-replacement reduction and
an unrecorded new lemma; it had no node files or report and did not compile.
Its untyped haveI inferred the unreduced predicate's second component rather
than the QuasiIso class needed by the bounded-Hom theorem. Giving that local
proof an explicit QuasiIso type fixes instance synthesis without changing a
statement. The new dependency is now recorded and the model-existence proof is
also written.

The original node was a definition node with an empty proof despite containing
three unproved construction/property theorems. Its proof fields now describe
which two have been reduced and which remains unfinished.

The cited bounded-flat module lemma is stated on ModuleCat, whereas this module
uses SheafOfModules on the one-object bottom site. It cannot be applied directly
without identifying these concrete categories and their tensor constructions.
The new complex-only theorem makes that remaining bridge explicit instead of
pretending the source lemma already has the necessary type. The algebraic source
was read at Stacks Tags 05CE, 064K and 0A6A; the site specialization is spelled out
as an agent argument in the new nodes and their docstrings.

Mathlib searches: the earlier attempt's logged LeanSearch query for projective
internal Hom returned an unavailable-service error; the new search for bounded
projective scalar extension also returned unavailable. This is recorded as
unavailable, not a negative verdict. Loogle for Module.Projective returned module
projectivity basics; LeanFinder for projective internal Hom returned condensed
module and preadditive Coyoneda results, not this sheaf-valued specialization.
LeanFinder for bounded projectives returned ordinary module flatness, notably
Module.Flat.of_projective. The logged grep searches and local rg of the current
library/DAG found no theorem supplying either full new statement. Blueprint
searches for projective Hom and bounded projective found no matching imported
blueprint statement. Existing bounded exact-term Hom and K-flat resolution
modules were read and used instead of restated.

Edge cases checked for the new statements: zero rings, zero source terms,
empty support intervals (b<a), and projectives of infinite rank. Evaluation on
this site remains an equivalence in each case; the ordinary Hom lifting and
free-module-retraction arguments do not require finite rank or a flat ring map.
In particular the model proof adds no boundedness assumption on K.

## New nodes

`lem-pc-ring-projective-internal-hom-exact` states ordinary projective-source
internal Hom exactness on the one-object bottom site. Its complete proof identifies
the slice Hom with linear Hom, factors maps through the kernel and lifts through
the surjection. It supplies exactly the termwise exactness hypothesis of the
existing bounded exact-term Hom theorem. Module:
`Sheaf.Algebra.Homology.RingProjectiveInternalHomExact`.

`lem-pc-ring-bounded-projective-extension` states K-flatness of a bounded
projective source and projectivity of its scalar-extended terms. Its proof
identifies the site tensor with module tensor, uses the existing bounded-flat
module theorem, and tensors free-module retractions. Extended boundedness is
proved in the item and is not left as part of this hole. Module:
`Sheaf.Algebra.Homology.RingBoundedProjectiveExtension`.

No change record is required: no existing interface changed and no forced
adaptation was made. The new nodes inherit the item's chapter and unit and the
nearest blueprint ancestor lem-sc-finite-duality. The existing unit's realization
records are untouched.

## Second reading by C3

1. I compared the delivered item module with the repository version. Existing
declaration signatures, definitions, visibility, and public imports are unchanged;
the two repaired proofs use only added proof-only imports.

2. I compiled all three delivered modules with `lcompile.py --all`; compilation is
clean. The only remaining `sorry`s are the three named theorem holes reported above,
and no forbidden declarations or hollow definitions were introduced.

3. I checked the two added statements against their declarations and docstrings.
They are true one-object-site specializations, strictly smaller than the original
model-existence and Hom-replacement holes, and are not duplicated in the library or
Mathlib. Their DAG nodes, sources, proof dependencies, and Lean records agree with
the modules.

4. I checked the proof routes and imports. The bounded exact-term Hom theorem,
K-flat resolution theorem, and the two new nodes are used as recorded; no unused
proof-only import remains and no unit step is bypassed.

5. I checked the item node's proof, proof dependencies, proof origin, and realized
unit route against the repaired Lean proof. The original remaining existence theorem
is left unchanged, while the two reduced holes and both new nodes are recorded as
decompositions.

I changed only this report after the first reading: I added this second-reading
record. No Lean statements, definitions, or DAG content were changed during review.
