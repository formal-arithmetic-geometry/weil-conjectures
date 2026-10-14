## What changed

Second-reader repair rebased onto the current repository. The incoming sandbox
was stale: it removed the now-correct restriction helper and replaced the canonical
comparison's existing proof by sorry. Restore that current proof, including its
linear-map and local-bijectivity imports, and inline its final naturality equation.
Retire the restriction helper and prune its empty compatibility module from the
canonical caller. Keep all surviving signatures and visibility exactly unchanged.
Update the three node proof records and remove the two redundant historical
attachments. Change record: coord/changes/DeterminantSplitComparisonLocal-repair.md.

The sandbox encodes both attachment deletions as `lean: null`, the supported
deliver3.py directive that removes the key from each delivered node.

## Proved and sorry left

The current repository item's sole declaration,
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction,
is already proved; it is retired, not counted as a newly proved hole.
Zero of zero current direct holes are newly proved, zero holes added, zero split off.
The second reading closes the stale sandbox's direct hole in
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists
(node lem-sc-determinant-split-comparison) by restoring the current repository's
proof with a shorter last step. Both delivered modules now contain no sorry.
#print axioms of that canonical theorem reports only propext, Classical.choice,
and Quot.sound, with no sorryAx. This is pruning and regression repair, not a
new proof-progress claim against the current repository baseline.

## No longer needed

From the current local module remove the public imports
Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf and
WeilConjectures.AlgebraicGeometry.Modules.TensorSection.
Retain only a private Mathlib.Algebra.Homology.ShortComplex.ShortExact import
for the delivery's declaration-probe command infrastructure.
From the canonical module remove its private
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal import.
That module is pruned from the target closure; the only repository importer is
the adapted canonical caller. Remove new-determinant-split-restriction from the
canonical node's proof_deps, since naturality is used directly. The historical
new-determinant-split-local was already replaced by the canonical theorem in the
current repository; retain its existing statement_change and remove its redundant
attachment. All canonical public imports and both genuine construction dependencies
remain. Its inherited private ExteriorTopDirectSum import is retained because
removing it is not forced by retirement of the local helper.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox report described two old holes and a false restriction
assertion. That assertion has already been corrected upstream to substitution into
an assumed natural linear family, and the canonical construction now has a proof.
The historical sign counterexample does not refute the current statement: it
violates its naturality hypothesis hn. The incoming repair would regress a proved
canonical theorem to sorry; this reading removes that regression.

## Forced adaptations

Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison is unclaimed in the
available snapshot. Its original proof calls the helper removed by this delivery.
Keep its full signature and visibility, its construction, local bijectivity and
wedge formula. Remove only the private local-module import and replace the final
helper application by two lines applying the already retained hn directly.
Compiling the original against the changed dependencies reports at 100:10:
error(lean.unknownIdentifier): Unknown identifier `determinant_split_comparison_restriction`
and at 102:4: error: No goals to be solved. The adapted module compiles cleanly.

## Earlier second reading (a previous round; superseded)

1. Diffed both modules against the current read-only repository, then compared the
   complete canonical signature byte for byte: identical. The only declaration
   removal is the explicitly recorded substitution helper; the historical local
   declaration was already absent. No definition or target changes. Verdict: pass.
2. Compiled both delivered files using lcompile.py --all. Independently compiled
   a scratch copy with #print axioms of determinant_split_comparison_exists:
   exactly propext, Classical.choice, Quot.sound. No direct sorry, forbidden form,
   or hollow data definition remains. Verdict: pass, including all dependencies.
3. No new statement is split off. Read the current helper: substituting hd into hn
   proves it for every rank and open, without any generation assumption. The
   inlined canonical step follows definitionally from LinearEquiv.ofBijective;
   proof irrelevance identifies inclusion proofs. Zero ranks, zero rings and empty
   opens introduce no side conditions. Verdict: pass; the current helper is true.
4. Searched all repository callers of both historical names and the local module:
   only the canonical caller uses the restriction helper or imports its module.
   Read the linear-map construction and bijectivity interfaces and searched the
   upstream library for LinearEquiv.ofBijective. Direct application of hn is the
   shortest route. All old proof_deps removed by this delivery are listed above.
   sk-thm-picard-rr has empty realized lists; the determinant construction and its
   two actual dependencies are preserved. Verdict: valid pruning below the unit.
5. Rebased all three JSON records on the current repository. Only proof,
   proof_deps, proof_origin and the redundant lean attachments change. All current
   statement and statement_change metadata is preserved. Canonical dependencies
   exactly match the two imported construction theorems; no new nodes or unit
   changes. Hole accounting is explicit above. Verdict: records agree with Lean.

Second reading restored the current canonical proof instead of adding a sorry,
inlined naturality, corrected stale mathematical claims and hole counts, and
rebased the change record and all node records. Verification scratch removed.


## Second reading by K3

1. Compared both delivered modules with the current repository using diff, and
   independently compared the canonical declaration's complete source signature
   and visibility byte for byte with the declaration parser: identical. The only
   removed declaration is the helper recorded in the change record. No definition,
   target statement, or surviving docstring changes. Verdict: pass.
2. Compiled both modules with lcompile.py --all: no errors or warnings. Compiled a
   separate scratch copy with #print axioms of
   AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists: exactly
   propext, Classical.choice, Quot.sound, with no sorryAx. Searched every delivered
   Lean source for sorry and forbidden declaration forms: none. The construction
   uses the established linear maps and their proved bijectivity, then
   LinearEquiv.ofBijective; no data are chosen from an unproved existence theorem.
   Verdict: pass.
3. There are no split-off statements or new declarations. Read the construction
   and local-bijectivity interfaces and the removed helper's full statement. The
   helper follows by substituting hd into hn; the replacement applies hn because
   the equivalence's forward map is definitionally d₀. Inclusion proofs agree by
   proof irrelevance. No extra assumptions are needed for zero ranks, the zero
   ring, empty opens, or identity restrictions. Verdict: pass.
4. Searched repository Lean files for the module and both historical names: the
   only importer and helper caller is the adapted canonical module. Repeated
   Mathlib/upstream search using ofBijective and apply_symm_apply, and searched
   local sources: the direct naturality application already takes the shortest
   route. The No longer needed section includes both removed public imports, the
   removed private caller import, and the obsolete restriction proof dependency.
   The compatibility module's private import supports the mandatory declaration
   probe. The caller's other imports are inherited and outside the forced repair.
   Read sk-thm-picard-rr.json: its realized lists are empty; the canonical
   determinant construction and its two mathematical dependencies stay intact.
   Independently compiled the original caller against the sandbox overlay: it
   fails at 100:10 with the removed helper's unknown-identifier error and at
   102:4 with No goals to be solved. The adapted caller compiles. Verdict: pass.
5. Diffed all three node records. Only proof, proof_deps, proof_origin and lean
   change; all statements and statement_change histories are preserved. Checked
   that each proof_deps is exactly the union of the proof steps' uses. The canonical
   attachment stays; both retired attachments use the supported lean: null removal
   directive, resolving the return's requested deletions. No new node or unit edit
   is required. Against the current repository, zero of zero holes close, zero
   holes are added, and zero statements are split off; one module is pruned from
   the target import closure. Verdict: pass.

This reading found no further mathematical repair necessary. Added this independent
review and reverified compilation, axioms, signature preservation, node ownership,
attachment removals, and the forced caller failure. The earlier repair is retained
as pruning and regression prevention, without claiming new proof progress.
