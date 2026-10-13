## What changed

Proved `etaleAbelianKanComparison_locally_surjective` in
`Sheaf.Paper.EtaleAbelianKanComparisonLocallySurjective` without changing its signature,
the existing definitions, or any existing public imports. Added proof-only imports of
`EtaleInverseImageAbelianLiftHom`, `EtaleInverseImageSmallUniverse`, and abelian
coefficient ULift. The flat Kan extension, AB5, adjunction restriction, and adjunction
uniqueness results are already available through retained imports.

The proof applies the existing large-coefficient abelian/set hom-set comparison. The
proved set inverse-image smallness theorem bounds every section group of the large
abelian inverse image of a lifted small sheaf. The private proved helper
`smallAbelianSheaf_essImage` constructs a small abelian presheaf with `Shrink`, transporting
its actual restriction maps with `Shrink.addEquiv`, and proves its sheaf condition.
Restricting the large adjunction along fully faithful coefficient ULift gives a small
abelian adjunction. Uniqueness compares it with the supplied adjunction. The hom-set and
restricted-unit equations identify the concrete Kan comparison with the sheafification
unit followed by the resulting underlying-set sheaf isomorphism. The private proved
helper `etaleSetPullback_unit_hom` expands the constructed set adjunction's unit into
its Kan and sheafification factors. Mathlib's local-surjectivity and composition
instances finish the proof, including the empty-object case.

Updated the existing DAG node's proof, proof dependencies, and proof origin to record
this route. Its statement, source, universe convention, and unit membership remain
unchanged. The item is not itself a realized unit statement or step; the containing
unit `sk-thm-p1` and all its realized steps are preserved.

## Proved and sorry left

Closed the one original hole:
`etaleAbelianKanComparison_locally_surjective`
(node `new-r2-etale-abelian-kan-comparison-locally-surjective`).

No `sorry` remains in the item's module. No holes were added or split off. Both new
private helpers are proved. This is a proof from existing library declarations, not a
new decomposition. Existing transitive holes in imported library modules are not
claimed to be closed by this delivery.

## No longer needed

No original import was removed: all were public statement/interface imports.
Second reading removed four redundant imports added by the first worker:
`Mathlib.CategoryTheory.Adjunction.Restrict`,
`Mathlib.CategoryTheory.Adjunction.Unique`,
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types`, and
`WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`. These modules remain
transitively imported; this is import cleanup, not pruning their closure.

The following planned direct dependencies are not needed by this proof:

- `lem-weil-pbc-affine-etale-essentially-small-cover`: the universe comparison uses the
  already proved `lem-weil-pbc-etale-inverse-image-small-universe`, whose argument uses
  geometric fibres and a conservative small family of points. No new affine-basis
  construction is needed here.
- `lem-weil-pbc-site-sheafification-sections-local` and module
  `Sheaf.Paper.SiteSheafificationSectionsLocal`: Mathlib directly proves local
  surjectivity of the large set-valued sheafification unit; explicit representatives,
  overlap agreement, and covering presieves are not needed in this item.
- `lem-weil-pbc-etale-inverse-image-algebraic-structures` and module
  `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`: use its strictly
  smaller abelian hom-set comparison `etaleInverseImageAbelianLift_hom` instead.
  The ring lift and the abelian/ring operation-transport assertions are not needed.

These are removals from this node's planned direct proof dependencies, not assertions
that no other target or imported module needs them. The original item had not imported
these planned modules.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly noticed that the large-coefficient compatibility theorem cannot be
applied directly to the small-coefficient F. Its proposed fresh affine-basis universe
comparison was unnecessary: `Scheme.etale_setPullback_small` already supplies the
size bound, and one can restrict the large abelian adjunction with a constructed
`Shrink` model. The original theorem docstring describes that alternative affine-basis
plan; the updated DAG and this report describe the implemented route.

No false statement, hollow definition, target change, forced adaptation, or tool
workaround was needed. The comparison isomorphisms used from existence statements are
specified by their adjunction hom-set equations; the small presheaf is constructed by
transporting the actual large section groups, not by selecting arbitrary data from an
unproved mere-existence theorem.

The earlier delivery-tool failure is resolved upstream. The final required
`deliver3.py A3 Sheaf.Paper.EtaleAbelianKanComparisonLocallySurjective
--no-push` run printed `OK (dry run)`: compilation and preflight passed,
except for the second reading reserved for the independent reader. Nothing
was pushed. The source-only `lcompile.py` check also passed without warnings
or errors. No linter suppression, tool edit, or interface change is retained.

## Second reading by A3

1. **Interfaces: pass.** Compared the sole delivered Lean module with the repository
   using `diff -u`, and separately compared the four existing declaration headers as
   strings: all are byte-identical. The three existing construction bodies and all
   public imports are unchanged. The only node edits are `proof`, `proof_deps`, and
   `proof_origin`; no change record or forced adaptation is needed. The theorem still
   quantifies over arbitrary schemes, morphism p, supplied left adjoint H and its
   specified adjunction, and small-coefficient F, and asserts local surjectivity of
   exactly the previously defined Kan comparison.
2. **Proof and axioms: pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings. In a scratch copy, `#print axioms` for
   `etaleAbelianKanComparison_locally_surjective`, both private helpers, and
   `etaleAbelianKanComparison` returned exactly `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. Scanned the delivery for forbidden declarations
   and proof holes: none. Checked the actual restriction maps in the Shrink model,
   reflection of its sheaf condition, the direction of the section-size injection,
   the restriction-unit equation hrest, and the uniqueness-unit equation hz. The
   final hq uses Kan uniqueness to identify the actual comparison, so the final
   instance proves the required map locally surjective, not merely some isomorphic
   source or target. All auxiliary object choices come from proved constructions;
   ea is constrained by its hom-set equation, while L lifts an explicitly constructed
   small model along a fully faithful functor.
3. **Split statements: pass, none.** No new public statement, new DAG node, or sorry
   is introduced. Both private helpers are proved. The first works for every
   objectwise-small large abelian sheaf by transporting actual group operations and
   maps; it requires no nonempty site or section set. The second expands the
   particular constructed adjunction, rather than asserting an equality for an
   arbitrary adjunction. The zero sheaf and the empty scheme cause no extra
   hypothesis: Shrink transports the trivial group, and Mathlib's covering-sieve
   local-surjectivity instances also handle empty objects.
4. **Route and pruning: pass after import cleanup.** Read the existing large hom-set
   comparison and small-universe theorem in full. Their statements supply exactly
   ea/hea and the section-size bound used here. Read Mathlib's sheafification-unit,
   isomorphism, and composition local-surjectivity instances. Independently searched
   for Kan/local-surjectivity comparisons and Shrink/essential-image helpers in
   Mathlib and both library roots; found no shorter public comparison theorem.
   `EpiOverFunctor` has a similar private Shrink construction, but its theorem
   concerns sheafification of a presheaf under additional hypotheses and cannot
   replace this helper. A fresh Loogle query found the expected sheafification-unit
   instance, not a theorem proving this item's abelian universe comparison.
   Read Stacks Tags [00YV](https://stacks.math.columbia.edu/tag/00YV) (abelian
   underlying-set compatibility) and [00WK](https://stacks.math.columbia.edu/tag/00WK)
   (local lifting through sheafification) online because the local literature sources
   are absent. The proof implements that factorization. Compared old and new
   proof_deps: the three omitted planned dependencies are all listed above. No
   original module import is pruned. Read `dag/units/sk-thm-p1.json`: this item is
   absent from its realized statement and steps, and none of those steps is replaced.
5. **DAG: pass.** Checked all four revised steps against the Lean proof, and the
   mathematical/Mathlib declarations named by their dependencies. The left-exactness
   step uses base-change finite limits, flat Kan extension, objectwise limits, and
   exact sheafification. The second uses small-universe sections and ea; the third
   uses adjoint uniqueness with its unit equation; the fourth uses sheafification
   and Kan uniqueness. `proof_deps` is exactly the union of the steps' `uses`.
   `proof_origin` records the implemented small-universe route; statement, source,
   chapter, unit and lean statement record are unchanged.

**Changes in this reading.** Removed redundant proof-only imports of
`Mathlib.CategoryTheory.Adjunction.Restrict`,
`Mathlib.CategoryTheory.Adjunction.Unique`,
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types`, and
`WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`; compilation and the
explicit axiom checks still pass without them. These declarations and instances
are already available through retained imports. Retained `Grp.Ulift`: removing it
loses the required fully faithful and limit-reflection instances. The earlier
report's list of added imports is superseded by this cleanup. No proof body,
existing signature, definition, or DAG route needed repair. Closed one original
hole, added zero holes, split off zero statements.
