## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.exists_opens_range_subset_iff`
without changing its signature or any definition. Its proof constructs the open as the
residue-cohomology locus, uses the proved openness theorem, and packages the two cohomology
clauses supplied by the residue-detection criterion into `IsFiniteLocallyFreeInDegree`.
Both new imports in the item are proof-only.

The second reading replaced the unused public Sections import in both new modules with
public imports for bounded cochain complexes (including homology), residue fields, and
scheme modules.
The FreeComplex import remains proof-only. No existing public import of the item changed.

Added `Sheaf.AlgebraicGeometry.FiniteFreeResidueLocusOpen`. Its public openness theorem is
completely proved from the existing sorry-free `Modules.FreeComplex` rank and semicontinuity
lemmas. It intersects finitely many upper-semicontinuity neighbourhoods and four basic opens
where adjacent differential ranks cannot decrease. Rank-nullity in degrees i-1 and i+1
forces those ranks to stay fixed, and rank-nullity in degree i gives the exact rank r.
A private basic-open helper is also completely proved. This is a shorter argument for
openness than cancelling the entire complex.

Added `Sheaf.AlgebraicGeometry.FiniteFreePullbackResidueCriterion` for the remaining
universal pullback step. It has no existential open or topological conclusion, so it is
strictly a part of the original argument, not the same theorem under another name.
The parent node records the two steps and retains the general perfect-object chart
reduction, which the existing nonnegative finite-free Lean signature does not require.

Compiled the three-module sandbox in import order. The tests of the new statements include
rank zero, zero complexes, empty schemes and sources, i=0, and i>d. In the actual openness
proof negative degrees vanish by the lower support bound; all q>d vanish by the upper bound.
No witnesses are chosen to define data from unproved existence theorems.

## Proved and sorry left

Original module: 3 holes before; 2 remain.

- Closed by a decomposition:
  `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.exists_opens_range_subset_iff`
  (node `lem-pc-perfect-locus`). Its combining proof has no sorry.
- Completely proved new theorem:
  `AlgebraicGeometry.Scheme.Modules.isOpen_finiteFree_residue_locus`
  (node `lem-pc-finite-free-residue-locus-open`).
- Completely proved private helper:
  `AlgebraicGeometry.Scheme.Modules.exists_residue_rank_le`.
- Original sorry left untouched:
  `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`
  (blueprint unit `sk-thm-picard-coherence`).
- Original sorry left untouched:
  `AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`
  (node `lem-pc-coherent-hi`).
- One new sorry:
  `AlgebraicGeometry.Scheme.Modules.finiteFree_pullback_single_iff_residue`
  (node `lem-pc-finite-free-pullback-residue-criterion`). Its entire proof is `by sorry`;
  the docstring and node contain the complete cancellation, pullback and field-extension
  argument. This is one closed upper hole and one added lower hole: net zero holes,
  a decomposition with a separately completed openness step, not an axiom-free proof
  of the original theorem.

The already-proved `isFinitePresentation_higherDirectImage` is unchanged.

## No longer needed

No existing imports of the item removed and no modules pruned. The two new modules no
longer import `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`; their
statements need only the narrower imports listed above.

Every old proof dependency removed from the parent node is listed here:

- `lem-weil-pbc-free-complex-unit-entry-splits`
- `lem-pc-finrank-field-base-change`
- `lem-pc-flat-complex-derived-pullback`
- `lem-pc-ringed-spaces-derived-pullback-composition`
- `def-pc-derived-pullback`

The first four are now needed under the residue criterion rather than directly by the
combining proof; the derived-pullback definition is a statement dependency of the new
nodes. None is claimed globally unused. The finite-projective standard-free cover is not used by the delivered
Lean proof (P is already finite free), but remains necessary for the parent node's general
perfect-object formulation and is retained in that node's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The parent node's primary lean record points to the semicontinuity module; this item's
perfect-locus declaration appears in its lean audit rather than as its primary declaration.
The source theorem already states only the nonnegative bounded finite-free specialization
of the general perfect-object node. This delivery preserves that existing signature and
keeps the general chart reduction in the node rather than silently changing its statement.
The other two holes have substantially different proper-cohomology arguments and remain
unchanged in this partial delivery. Existing coherent-support and projective higher-image
results cannot be imported here: their modules depend on this item, so that would be circular.

Mathlib searches: LeanFinder found only general free-locus, cochain support and injective
complex results; Loogle had no hit; grep had no matching perfect-locus theorem; LeanSearch
returned an internal-server error and is recorded as unavailable. Repository searches found
no existing statement exactly giving the residue criterion for this raw finite-free complex.

## New nodes

`lem-pc-finite-free-residue-locus-open`: the topological part, in
`lean/Sheaf/AlgebraicGeometry/FiniteFreeResidueLocusOpen.lean`; completely proved using
matrix minors, the existing rank-nullity identity, and finite intersections. It includes
all support and rank-zero edge cases without a reducedness hypothesis.

`lem-pc-finite-free-pullback-residue-criterion`: the universal cohomology detection part, in
`lean/Sheaf/AlgebraicGeometry/FiniteFreePullbackResidueCriterion.lean`; one sorry. Both
directions are required. Its hypotheses permit exactly the complex from the item; it
asserts no open locus and makes no arbitrary choice of a sheaf or complex. It follows
step 4 of `lem-pc-perfect-locus` using the existing cancellation and field-extension nodes.

No statement changes, definition changes, forced adaptations, or change records.

## Second reading by M2

1. Compared the delivered item against the repository with `diff` and checked the raw
   signature slices of every existing declaration. They are byte-for-byte identical.
   Both structures and all definitions are unchanged. The only original proof changed
   is `IsFiniteFreeComplex.exists_opens_range_subset_iff`; its two new imports are private
   to proofs. No forced adaptations or change records are needed. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`, without errors or
   warnings. Searched all delivered sources for prohibited declarations and inspected
   every `sorry`: exactly the two original holes and the named new residue criterion
   remain. No definition contains a hole or chooses arbitrary data from an unproved
   existence theorem. Scratch copies with `#print axioms` show only propext,
   Classical.choice and Quot.sound for the openness theorem and its private helper;
   the combined perfect-locus theorem additionally uses sorryAx through the explicitly
   reported criterion. All other printed declarations use only the allowed axioms and,
   where still open downstream, sorryAx. Verdict: valid decomposition, net zero holes;
   the original perfect-locus theorem is not yet axiom-free.
3. Read the complete new criterion and its cancellation/derived-fibre proof in words.
   It requires bounded nonnegative finite free terms and retains both directions.
   Termwise pullback preserves the explicit contractible summands; conversely the
   flat single cohomology sheaf computes the derived fibre, and field extension detects
   its dimension and vanishing. The criterion asserts neither an open set nor openness,
   so it is strictly the universal-cohomology part of the original argument. Checked
   empty sources and bases, rank zero, the zero complex, degree zero, degrees above d,
   and nonreduced bases. In particular the statement does not incorrectly infer
   local freeness from constant rank over a nonreduced base: cancellation uses exactness
   of every other fibre cohomology degree. New searches used the phrases "single flat
   homology residue field criterion", Loogle `"homology", "pullback"`, and grep for
   homology/flatness. No duplicate was found. The existing constant-rank-complex theorem
   assumes reducedness and open immersions, so it cannot close this arbitrary-pullback
   criterion. The local algebra search results do not supply the sheaf cancellation
   argument in a few minutes. Verdict: true, needed, strictly simpler; one hole remains.
4. Read the rank-nullity openness proof from the target downwards. Its finite intersection
   handles all degrees 0 through d; the support bound handles the rest. The four adjacent
   matrix-rank bounds and rank-nullity in degrees i-1 and i+1 force equality in degree i.
   Its helper uses actual matrix-minor basic opens, including the empty minor for rank
   zero. The proof uses existing proved FreeComplex lemmas instead of adding holes for
   openness. The residue criterion retains the unit's cancellation and base-change route.
   The unit record's realized arrays are empty in the repository and are unchanged;
   no realized node or unit step is bypassed. Enumerated every dependency removed from
   the parent above. Verdict: pass, no modules pruned.
5. Compared the three node records with the Lean. The parent records the open-locus
   construction and criterion application, with the existing general-perfect chart
   reduction distinguished from this Lean specialization. Each new node has all
   required fields, a complete proof, and proof_deps equal to the union of its steps'
   uses. Corrected doubled TeX backslashes in the new nodes, copied the Lean signatures
   verbatim, and recorded the successful second-reader Loogle search. Verdict: pass.

Changes by the second reader: narrowed the two new modules' public imports; corrected
new-node TeX escaping and verbatim signatures; completed the dependency-removal list;
added this independent review. No mathematical statement or proof was changed.
