## What changed

The Lean module, its existing DAG node and this report change. The second reading
also adds `coord/changes/CechCupPullbackCompat-imports.md` for import pruning.
Three original naturality theorems now have complete Lean proofs. All seven public
signatures stay identical. The second reading removes the unused public import
`Sheaf.AlgebraicGeometry.Coherent`; the other public imports stay identical. Private, proved helpers express
cochain coefficient maps componentwise, restrict pulled-back face sections, transport
concrete kernel cycles through cochain maps, and construct the cup of two cycles.
The kernel-cycle construction uses the existing named `cechCupCochain_leibniz` theorem;
it contains real cochain data and no new proof hole or arbitrary existence witness.

`cechRefinement_coefficient_naturality` follows from the adjunction unit's naturality
and restriction naturality. `cechCup_refinement_naturality` follows tuplewise from
`module_pullback_tensor`'s section normalization, restriction of tensor sections,
and the unit's restriction square on the front and back faces.
`cechCup_coefficient_naturality` first proves the analogous cochain identity, then
uses surjectivity of the kernel-to-homology class map, Leibniz, naturality of cycles
and their homology classes, and both specified cup-product characterizations.
No cover, finiteness, affine, or comparison-isomorphism assumption is introduced.

The original node's Step 4 and proof dependencies now record these actual arguments;
the other proof steps are retained for the four untouched theorems. The unit record
`dag/units/sk-prop-av-cube.json` has no realized node at this item; its route is preserved.
Local single-file compilation passed without errors or warnings. Declaration-scoped
heartbeat allowances concern elaboration of the coefficient-homology and refinement
formulas; the compiler's 60-second wall limit is unchanged.

## Proved and sorry left

Closed 3 original holes, all in namespace `AlgebraicGeometry.Scheme.Modules`:

- `cechRefinement_coefficient_naturality`.
- `cechCup_coefficient_naturality`.
- `cechCup_refinement_naturality`.

Added 0 holes and split off 0 statements. This is a partial proof delivery, not a
relocation of any original hole.

The following 4 original named theorem holes remain untouched, each recorded in
`lem-sc-picard-cech-cup-pullback-compat` and retaining its original proof docstring:

- `AlgebraicGeometry.Scheme.Modules.cechCupPullbackCompat`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.
- `AlgebraicGeometry.Scheme.Modules.cechRefinement_composition_naturality`.

The first theorem still requires the cross-scheme resolution diagram of Tag 01FD
and the cup comparison diagram of Tag 0FKV. The existing
`cechComparisonMapNaturality` supplies coefficient naturality on one scheme and
cover, not either of those diagrams. The sheaf-cup naturalities need compatible
acyclic-resolution pairings. The composition theorem needs its composite cochain
and comparison squares as well as functoriality of cohomology pullback. The existing
`ModuleCohomologyFMapFunctorial.moduleCohomologyPullback_comp` addresses the latter
part (the actual declaration is in `AlgebraicGeometry.Scheme.Modules`), but does
not by itself prove the former two conjuncts. No substitute statement was added.

## No longer needed

`Sheaf.AlgebraicGeometry.Coherent` is removed: no declaration of that module is
used by the signatures or proofs. In particular `IsQuasicoherent` remains available
through the other imports. This removes an unnecessary direct dependency; it does
not claim the module is unreachable from every target. None of the two old
`proof_deps` nodes is removed: they support the four unchanged comparison and
sheaf-cup/composition holes. The five retained public imports supply declarations
in existing signatures. The three completed naturalities do not use comparison
isomorphisms or any affine-cover theorem. They reuse the existing Cech and tensor
interfaces and ordinary Mathlib homology naturality rather than adding auxiliary
items. No new proof-only import was required.

## Where the brief, the DAG or earlier work was wrong

No statement error was found and no existing interface changed. The DAG's Step 4
previously omitted the section-normalized tensor-pullback dependency that its
formula needs; this delivery records it explicitly, together with the refinement
and cup definitions used by the three completed proofs.

The local path `literature/stacks-project/cohomology.tex` is absent. The cited
sources were read on the official Stacks site:
[Tag 01FD](https://stacks.math.columbia.edu/tag/01FD),
[Tag 07MB](https://stacks.math.columbia.edu/tag/07MB), and
[Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV).
No new unsourced intermediate theorem was written. In particular, the original
comparison-map node cannot be used as a direct cross-scheme refinement comparison:
the item's earlier review already correctly records this limitation.


## Second reading by V3

1. **Unchanged interfaces: PASS.** Compared the complete Lean module and node against
   the repository with `diff -u`. All seven existing theorem signatures are byte for
   byte unchanged, including hypotheses, conclusions and visibility. No existing
   definition changed and no other module is adapted. The public import removal has
   change record `coord/changes/CechCupPullbackCompat-imports.md`; the read-only
   downstream script reports zero downstream modules.
2. **Proof and axioms: PASS.** Independently compiled the submitted module (47.6 s)
   and a scratch copy without the unused Coherent import (35.9 s), without errors
   or warnings. Exactly the four reported original named theorem holes remain;
   there are no new holes, forbidden declarations or hollow definitions. Explicit
   `#print axioms` on all seven declarations reports only `propext`,
   `Classical.choice`, `Quot.sound`, and existing `sorryAx`. The completed refinement
   and refinement-cup naturalities have no `sorryAx`; coefficient-cup naturality
   still reaches an imported open proof. The cup cycle contains the actual cup
   cochain, with a kernel proof from the named Leibniz theorem. No arbitrary
   existence witness is introduced.
3. **Split statements and reuse: PASS (none split).** All new helpers are private
   and proved. Checked empty index families, zero degrees, repeated tuple indices,
   zero coefficients and identity coefficient/refinement maps against the tuple
   formulas; no extra covering assumption is needed. Searched the library using
   `cechCupCycles`, `cycleClassLinear_surjective`, restriction composition, and
   homology naturality, and reran Mathlib search with a different homology query.
   The existing cup-cycle and cycle-class helpers are private in CechCupProduct
   and cannot be reused through its public interface. The proofs already use the
   appropriate public Mathlib cycles and homology naturality results. No open
   theorem merely renames the item.
4. **Route and pruning: PASS after repair.** Read the definitions of the two cup
   characterizations, refinement maps and section-normalized tensor comparison,
   and checked the sources at Stacks Tags 01FD, 07MB and 0FKV. Coefficient
   naturality is established on cochains before passing to homology; refinement
   naturality is established on each front/back face. No shorter public theorem
   was found. Removed the unused Coherent import and verified compilation.
   `## No longer needed` now records that import and accounts for both old proof
   dependencies. The unit sk-prop-av-cube has empty realized lists and is untouched;
   the comparison/resolution route of the four remaining holes is retained.
5. **DAG agreement: PASS.** The only node changes are proof, proof_deps and
   proof_origin. Step 4 records all three actual reductions and their cup,
   refinement and tensor-pullback dependencies; proof_deps is the union of the
   steps' uses. The source, statement, statement dependencies, unit, chapter and
   Lean declaration records are unchanged. No new nodes are needed.

Second-reading changes: removed the unused Coherent import, corrected the import
and pruning claims in this report, added the public-import change record required
by preflight, and documented the independent checks above.
No proof was rewritten and no additional hole was added or closed.
