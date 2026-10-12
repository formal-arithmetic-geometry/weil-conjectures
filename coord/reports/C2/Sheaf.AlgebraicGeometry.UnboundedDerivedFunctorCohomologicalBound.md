## What changed

Proved `AlgebraicGeometry.isZero_homology_rightDerivedFunctor_of_cohomological_bound`
with its signature unchanged. The proof follows Tag 08D4: reconstruct after RF,
apply Milnor, stabilize, and use the zero upper truncation. Integer induction
propagates the zero cohomology from index `-b-1` to every later integer index.
The ordinary limit of the resulting eventually zero degree-i tower is proved zero
by cone compatibility and limit extensionality.

Added the proof-only import `Sheaf.CategoryTheory.DerivedLimitEventuallyIso`,
containing a proved general tower lemma. Its proof constructs a right inverse to
the Roos map, by upward and downward recursion from the stabilization index,
and uses the existing Roos computation. Added the proof-only import
`Mathlib.Algebra.Category.Grp.AB` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution` for the
Grothendieck and K-injective-resolution instances for abelian groups. Public imports are unchanged.
The new node and the item's proof fields match these Lean proofs.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.isZero_homology_rightDerivedFunctor_of_cohomological_bound`
(node `lem-pc-unbounded-derived-functor-cohomological-bound`).
Also proved `CategoryTheory.isZero_firstDerivedLimit_of_eventually_isIso`
(node `lem-pc-derived-limit-eventually-iso`). No sorry remains in either delivered
module and no new sorry is added. These proofs use the existing stated reconstruction,
Milnor, stabilization, and Roos declarations, whose outstanding proofs remain their
own items; this delivery does not claim their axioms are already closed.

## No longer needed

No original import, dependency node, or module is pruned: reconstruction, Milnor,
stabilization, and the standard t-structure all remain used, preserving the unit route.
The planned stable-term identification is unnecessary; eventual zero plus limit
extensionality suffices. The extra `Mathlib.Algebra.Category.Grp.AB` import was tested for removal;
compilation confirmed it is necessary to supply the Grothendieck instance.
No added import remains unused.

## Where the brief, the DAG or earlier work was wrong

The old final DAG step claims `m=max(0,N-i-1) ≥ -b-1` from
`N-i-1 ≤ -b-1`. This implication is false: take `N=0`, `b=-3`, `i=0`;
then `m=0 < 2=-b-1`. The theorem and source are correct. The replacement uses
integer induction for all indices at least `-b-1` and chooses a sufficiently
large natural index for each limit projection.

The eventually constant first-derived-limit claim, previously called elementary,
had no directly usable stated general theorem. The new helper makes it explicit
and proves it from the existing Roos theorem. The finite-group Mittag--Leffler
blueprint node is not applicable to arbitrary abelian groups; the pro-etale Roos
triangle node is also not this statement. Blueprint searches for `eventually constant`
and `07KW`, library searches, LeanFinder, Loogle, and grep found no exact substitute.
LeanSearch returned Internal Server Error, recorded as unavailable.

Checked edge cases: `N=0`, all integer signs of `b` and `i`, stabilization index
zero, and nonzero finitely many initial tower terms. The recursion has no downward
steps when its stabilization index is zero and handles every finite prefix otherwise.
Both modules compile through the prescribed compiler with no warnings.
The Stacks files were absent locally; source text was read at the official pages
for Tags 08D4, 07KW, and 07KY.

## New nodes

`lem-pc-derived-limit-eventually-iso` states that eventually invertible successor
transitions make the first right derived inverse limit zero. Its Lean module is
`Sheaf.CategoryTheory.DerivedLimitEventuallyIso`; its proof is complete, using the
Roos computation and an explicit split epimorphism. It serves only the left
Milnor endpoint, and is strictly smaller than the item's cohomological bound.
No definition or statement was changed; no change record is needed.

## Second reading by C2

1. **Visibility and statements: pass.** Read the diff of the original module against
   the repository. The sole existing theorem signature is byte-for-byte unchanged;
   no definition is altered and the three original public imports are unchanged.
   The only new declaration is the proved tower helper. No change record is needed.
2. **Proof and axioms: pass relative to existing open dependencies.** Independently
   compiled both delivered modules through `lcompile.py` without errors or warnings.
   Scanned both for sorry and forbidden declarations: none occurs. Scratch copies
   with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. The latter comes from the existing Roos, reconstruction, Milnor and
   stabilization infrastructure, not a sorry added or hidden in this delivery.
   Reviewed the integer induction, its base truncation, the two stabilization
   thresholds, cone compatibility, and the split right inverse of the Roos map.
3. **New statements: pass.** There is no open split-off statement. The new proved
   helper concerns only the first inverse limit of an eventually invertible tower;
   it does not restate the original cohomological bound. Its source and complete
   docstring proof agree with its node. Checked stabilization at zero, arbitrary
   finite noninvertible prefixes, and zero/nonzero constant tails: the upward and
   downward equations meet at the same zero initial map and cover every index.
   Independently searched LeanFinder for "vanishing lim1 tower eventually bijective
   bonding maps", Loogle for `"rightDerived", "IsZero"`, and Mathlib grep for
   MittagLeffler/lim1/eventual isomorphisms; no exact replacement was found. Read
   `SurjectiveTowerLimitAcyclic`: it requires surjectivity at every index, so does
   not apply to this arbitrary finite prefix without an additional argument.
   Checked the official Stacks pages for Tags 08D4 and 07KW against the argument.
4. **Route and pruning: pass.** Reconstruction, Milnor, stabilization and the
   standard t-structure remain used. The unit record `sk-thm-picard-duality` has no
   realized node for this item (its realized arrays are empty); this proof changes
   no unit record or chapter route. All four old proof dependencies remain used,
   so "No longer needed" correctly prunes none. The helper's public Roos import
   is needed by its statement, not merely its proof: a scratch compile replacing
   it with a plain import and public Mathlib imports fails to synthesize
   `HasInjectiveResolutions` in the public theorem signature. The other added
   imports supply the abelian-group K-injective/product infrastructure for the proof.
5. **Nodes: pass.** The original node changes only `proof`, `proof_deps`, and
   `proof_origin`; its new dependency union equals the cited proof steps. The new
   node has the required source, search records, blueprint ancestry, creation and
   Lean records, and its Lean statement matches the file. The Roos split-epimorphism
   recursion and integer-induction/limit-extensionality steps match the actual code.

Second reading changed the original theorem's outdated docstring proof to describe
its actual integer-induction and eventually-zero-limit argument, and removed a
repeated `zero_comp` from one `simpa only` list. No signature, definition, dependency
or mathematical proof route was changed.
