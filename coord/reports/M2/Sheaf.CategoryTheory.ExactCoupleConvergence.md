## What changed

Proved `CategoryTheory.BigradedExactCouple.cycleBoundaryTower_exists` without changing its
signature or any existing public declaration. Private stages record the quotient presentation
at each finite page. The initial stage is top/bottom; natural-number recursion uses the local
homology step to assemble the tower. Added the proof-only import
`Sheaf.CategoryTheory.SubobjectHomologyStep`. Updated the convergence node's proof route.
The new module publicly imports only `Abelian.Basic` and `Subobject.Limits` for its
statement; `Abelian.Exact` and the upstream image lemmas are proof-only imports.

The new module proves `CategoryTheory.subobjectHomology_step` from Mathlib: pullback
stability of epis, exactness of a cokernel sequence, and subobject pullback functoriality.
Its canonical lift is uniquely determined by composition with the monomorphic kernel inclusion.
All subobjects are actual pullbacks/images; no arbitrary existence witness defines data.

## Proved and sorry left

Closed the one remaining original hole:
`CategoryTheory.BigradedExactCouple.cycleBoundaryTower_exists` (def-sp-convergence).
Added no holes. The new `CategoryTheory.subobjectHomology_step`
(lem-sp-subobject-homology-step) and its private pullback-kernel helper are fully proved.
There are no sorries in either delivered module. The dependency
`BigradedExactCouple.derivedMaps_exists` in the existing exact-couple module remains an
upstream obligation; this delivery does not change it.

Both delivered modules compile with lcompile.py in import order. The edge cases of the
local lemma include an identity presentation, zero incoming or outgoing differential,
and zero middle object; none require a nonzero assumption or an infinite limit.

## No longer needed

None of the existing imports, modules or nodes are removed. The local calculation uses
ordinary finite pullbacks, kernels and cokernels, with no complete subobject lattice or
infinite (co)limit assumption. Both existing proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox contained only dispatcher markers, with no prior Lean files or report.
The repository's existing proofs were preserved. No mathematical or interface correction
was necessary. The generic successor result proved here supplies the previously missing
local construction in the convergence node's first step.

## New nodes

`lem-sp-subobject-homology-step`, in
`dag/nodes/sec-abelian-varieties/lem-sp-subobject-homology-step.json`, records the fully proved
single-step quotient calculation, with no grading or tower. It is strictly a part of the
original construction. Its module is `Sheaf.CategoryTheory.SubobjectHomologyStep`.
Searches ran through msearch.py: LeanFinder returned homology epi lemmas, Loogle did not
recognize the queried identifier, grep found pullback/kernel results, and LeanSearch
returned Internal Server Error (recorded unavailable). Library and blueprint searches
found no existing statement of this local presentation. No change record is needed:
all existing signatures and visibility are preserved and the new import is proof-only.


## Second reading by M2

1. PASS. Compared the complete convergence module against the repository with diff and
   the declaration parser. Every existing signature, definition body and visibility is
   unchanged. Only one proof, private construction helpers and a proof-only import are
   added. The node diff changes only proof, proof_deps and proof_origin. No change record
   is required.
2. PASS. Compiled both delivered modules in import order with lcompile.py, without errors
   or warnings. Neither contains sorry or a forbidden declaration. Scratch copies with
   #print axioms show only propext, Classical.choice and Quot.sound for
   CategoryTheory.subobjectHomology_step. The tower existence theorem additionally uses
   sorryAx through the unchanged upstream derivedMaps_exists obligation used by pageCouple;
   no direct hole remains here. All new subobjects are constructed by pullback and image.
   The sole data chosen in stageTransition is a kernel lift, uniquely determined by comm
   and cancellation against kernel.ι; its other fields are proofs.
3. PASS. There are no statements split off with sorry. Read the new local lemma clause by
   clause and its full proof: the old kernel pulls back into every subobject, the lifted
   cycles project epimorphically by pullback stability, and the cokernel's kernel is the
   pulled-back incoming image. For π an identity, this is the usual ker(d)/im(b);
   for b=0 it gives B'=B; for d=0 it gives Z'=Z; for E=0 it gives B=Z and zero homology.
   The zero ambient object causes no exception. Repeated LeanFinder, Loogle and grep
   searches with inverse-image and kernel-composition queries, plus rg on Sheaf and the
   upstream subobject library. Related homology-map epi results do not supply the required
   ambient subobject identities; no duplicate statement or shorter replacement was found.
4. PASS after import repair. The proof directly constructs the initial presentation and
   recursively applies one finite local quotient step; it introduces no new proof holes.
   Existing ExactCouple and Filtration dependencies are both still used, so No longer
   needed is complete. Read sk-prop-av-pqf-finite.json: its realized statement and step
   lists are empty, and the delivery replaces no unit realization or unit-level route.
   Changed the new module's public Abelian.Exact import to a plain proof import, with
   narrower public Abelian.Basic and Subobject.Limits imports for its statement.
5. PASS. The new node's Lean statement matches the complete theorem signature. Its
   source, creation record, chapter/unit, searches and proof steps are present. Its empty
   proof_deps agrees with its Mathlib/upstream-only proof. The convergence node lists the
   local lemma plus the two retained original dependencies and describes the recursion
   actually implemented. Existing node statements and unit records are unchanged.

Second reading changed only import visibility and the narrower statement imports of
SubobjectHomologyStep, plus this report. Closed one original hole; added zero holes.
