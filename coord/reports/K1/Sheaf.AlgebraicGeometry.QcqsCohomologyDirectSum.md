## What changed

The original module now proves moduleCohomology_directSum_bijective without an inline
sorry. Injectivity is proved in a private helper by coproduct descent to each summand,
then DirectSum.component extensionality. Surjectivity is a finite sum of the cohomology
classes obtained by projecting a finite-stage representative. Functor additivity and
the finite biproduct total identity verify the image of this explicit preimage.

The single new module QcqsCohomologyFiniteSubsumRepresentatives isolates the existence
of a finite partial biproduct representative, precisely original steps 1, 2 and the
representative part of step 5. It does not assert injectivity, finite-sum additivity,
or the direct-sum comparison. Both modules compile without warnings locally.
The original statement and its public imports remain unchanged. The node records
now describe the implemented proof, and the unit route is retained.

## Proved and sorry left

Proved: AlgebraicGeometry.Scheme.moduleCohomology_directSum_bijective (the original
one of one sorry), from the upstream rightDerived additive instance and the
new finite-stage representative statement. Also proved privately:
moduleCohomology_directSum_injective. This is a reduction, not an assertion that the
transitive target closure is sorry-free.

One new sorry remains:
AlgebraicGeometry.Scheme.moduleCohomology_finiteSubsum_representative,
node lem-weil-pbc-qcqs-cohomology-finite-subsum-representatives, in
Sheaf.AlgebraicGeometry.QcqsCohomologyFiniteSubsumRepresentatives.
Its entire proof is by sorry, with its source and full mathematical proof in the docstring.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit (moved to the new lemma).
- Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives.
- Sheaf.CategoryTheory.DeltaFunctor (already exposed by PQFCohomology).
- Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor (already exposed by PQFCohomology).

The original theorem no longer directly needs nodes
lem-weil-pbc-qcqs-scheme-spectral, def-weil-spectral-space,
lem-weil-pbc-qs-scheme-cohomology-directed-colimit, or
lem-weil-pbc-scheme-modules-coproduct-finite-subsums: these are retained as dependencies
of the new finite-stage representative lemma. The zero-at-a-later-stage half of 01FF
is completely unnecessary for injectivity. The node
lem-weil-pbc-scheme-modules-enough-injectives and the direct application of
lem-weil-pbc-right-derived-universal-delta-functor are unnecessary in this argument;
The upstream rightDerived additive instance supplies additivity.
def-weil-pbc-delta-functor is also no longer needed directly after the second reading.
These dependencies may still occur in other transitive closures.
No public import was removed, and no whole module is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The old injectivity plan invokes the harder zero-at-a-later-stage assertion unnecessarily:
projections from the coproduct give a direct proof. The existing original docstring
records that old plan; the updated DAG and implemented proof use the shorter route.

The 01FF Lean statement is restricted to an index type in universe u, while the
original theorem permits I : Type v. In addition, it uses abelian-group-valued open
cohomology, while this theorem uses module-valued global cohomology. These are real
formalization bridges remaining inside the new finite-stage lemma, not changes of
statement. Its future proof must handle both the top-open/forget-scalars comparison
and the larger index universe. The finite-subsum theorem is Mathlib's
CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone, not a Sheaf module.

Read the local Stacks source copy: cohomology.tex, label
lemma-quasi-separated-cohomology-colimit (01FF), and label lemma-perfect-is-compact
(09J7), including its direct-sum application. Edge cases checked mathematically:
empty index set, empty scheme, zero family, p = 0, and an empty finite stage. All are
covered by allowing empty J and the finite biproduct total identity.

## New nodes

lem-weil-pbc-qcqs-cohomology-finite-subsum-representatives: the existence clause for
finite partial sums, strictly part of surjectivity and with no direct-sum conclusion.
Blueprint searches for cohomology direct sum and finite partial returned no matches;
its ancestor and unit are inherited from the original item. LeanFinder, Loogle and
grep searches found no matching theorem; LeanSearch returned Internal Server Error
and is recorded as unavailable. There are no statement or definition change records.

## Second reading by K1

1. Compared the entire delivered original module with the repository using diff.
   The existing theorem signature is byte for byte unchanged, as are all existing
   docstrings and public imports. No existing definition or statement changed;
   no change record is required. The only additional declaration is a private,
   fully proved injectivity helper; the split theorem has its own new module.
2. Compiled both modules locally in import order without errors or warnings.
   Inspected the proof from coproduct projections through direct-sum extensionality,
   then the explicit finite-support preimage and biproduct total identity.
   Checked #print axioms for the main theorem, private helper, and split theorem:
   only propext, Classical.choice, Quot.sound, and sorryAx (open dependencies).
   Exactly one textual sorry remains, the entire proof of the reported split theorem;
   no forbidden declarations or hollow definitions occur.
3. The split theorem is precisely finite-stage existence, strictly part of the
   argument: injectivity and finite-biproduct additivity are proved separately.
   Read Stacks 01FF and the 09J7 application in the local cohomology.tex source.
   Checked empty I, empty X, zero summands, p = 0, and empty finite J; no nonempty
   or quasi-coherence hypothesis is required. Independently searched LeanFinder
   for finite support in derived global sections, Loogle for rightDerived additivity,
   Mathlib grep for colimit preservation, and the repository for coproduct cohomology.
   No existing theorem closes finite-stage existence. The upstream additivity
   instance does close that part and is now used directly. The split lemma's
   source, complete proof docstring, and matching node are present.
4. The shorter projection argument is correct. Replaced the two delta-functor
   additivity extractions with the upstream rightDerived additive instance and
   added its proof-only import. Existing public imports all support the signature;
   new public imports support the split signature. The remaining proof imports
   of the split module record its planned directed-colimit and finite-subsum route.
   No longer needed lists every removed old proof dependency, now also the
   delta-functor node. Inspected sk-thm-p1.json realized: this auxiliary node is
   below the unit's stated steps; no unit realization or route is bypassed.
5. Checked both nodes against their Lean declarations and the implemented proof.
   proof_deps equals the union of proof-step uses. Updated the original node's
   additivity step and dependencies to follow the upstream instance. All required
   new-node fields and the verbatim split signature are present.

Changes in this reading: simplified additivity in both proofs; added one private
upstream import; removed the direct delta-functor dependency from the DAG; expanded
and synchronized the split docstring and node proof to explain the natural
forget-scalars comparison and the concrete small-index reduction using nonzero
sections and coproduct projections. No statement changed and no sorry was added.
