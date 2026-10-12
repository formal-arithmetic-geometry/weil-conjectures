## What changed

The original declaration `CategoryTheory.varyingSite_inverseImage_zero_detection` keeps its
signature, visibility and docstring. Its proof now constructs the later presentation and proves the
transition zero equation from the unit coherence `he`, coefficient cocycle `hφ`, adjunction-unit
naturality, and `map_zero`. Shared, fully proved helpers in the intermediate module compose Arrow equalities across equal
objects and compare their zero kernels; the original module imports and uses them. The only added import in the original module is the
non-public proof import `Sheaf.CategoryTheory.VaryingSiteIntermediateUnitZero`.

Added `Sheaf.CategoryTheory.VaryingSiteIntermediateUnitZero`, with the complete proof of
`CategoryTheory.varyingSite_inverseImage_intermediate_unit_zero`. This theorem removes the system
object transports and map equation, uses `heV` and cocone naturality, and identifies the intermediate
section's zero image using adjunction-unit naturality. It imports the new single-sheaf geometric
lemma for the proof. This proof uses neither the finite-stage composition isomorphisms nor the
coefficient cocycle, and concludes zero before applying the second coefficient map.

Added `Sheaf.CategoryTheory.ColimitSiteUnitZeroDetection`, containing the single-sheaf geometric
kernel statement. It has no coefficient system, composition isomorphisms, `Under` presentation or
outer sheaf colimit. Its docstring records the supplied-site transport, the identity representative
in the section formula, and the filtered equality argument. The original node and both new nodes
record the actual argument and its sources. No existing interface or other module was changed.

## Proved and sorry left

Closed the original hole in `CategoryTheory.varyingSite_inverseImage_zero_detection`
(node `lem-weil-pbc-varying-site-inverse-image-zero-detection`). The new intermediate theorem
`CategoryTheory.varyingSite_inverseImage_intermediate_unit_zero`
(node `lem-weil-pbc-varying-site-intermediate-unit-zero`) is also fully proved.

The delivery adds exactly one hole:
`CategoryTheory.colimitSite_unit_zero_detection`
(node `lem-weil-pbc-colimit-site-unit-zero-detection`). Its entire proof is `:= by sorry` in its own
module. There are no holes in the original or intermediate module and no new axioms or hollow
constructions. Closing one original hole and adding one geometric hole is a decomposition,
not a net reduction in holes. The new statement is strictly part of the argument: it detects zero
for a single sheaf under the bare units, without any coefficient system, system transport,
coefficient cocycle or later coefficient map. Those omitted steps have real Lean proofs here.

All three delivered modules compile through `lcompile.py --all`. The existing declaration's parsed
signature was checked equal to its original signature. New statements were checked at their edge
cases: zero sections work by choosing the identity arrow and `map_zero`; a constant identity diagram
reduces to the unit isomorphism; an empty index is excluded by `IsFiltered`; no injectivity of a
coefficient map or transition functor is asserted or used.

## No longer needed

No existing imports were removed and no entire module is claimed pruned. The original public
`ColimitSites` import is retained as the existing statement-supporting interface.

The original node's three direct proof dependencies
`def-weil-pbc-category-colimit`, `def-weil-pbc-sites-and-cohomology`, and
`lem-weil-pbc-colimit-of-sites` are replaced by
`lem-weil-pbc-varying-site-intermediate-unit-zero`. Their mathematical roles remain in the statement
or below the new single-sheaf geometric lemma; this is not a claim that these nodes leave the
library's target closure. No unrelated planned lemmas or outer sheaf-colimit comparison theorem
were imported. The fixed unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing return: both modules had private copies of `arrow_comp_app_eq` and
`arrow_zero`, and the import-pruning check correctly refused those duplicate statements. Removed
both copies from the original module and exposed the existing copies in the new intermediate
module. The original proof now imports and uses these two shared proved theorems. No import,
existing public signature, proof dependency, or remaining hole changed in this repair.

The original plan treats the supplied-site transport of the inverse-image section formula as an
available application of `ColimitSites`. The actual existing theorem supplies a constructed cocone
and precoverage existentially. It does not directly provide the formula for the caller's supplied
`V` and `Q`. That transport and its kernel consequence are now explicit in the new geometric node,
which is the remaining work. The previously bundled endpoint/coefficient coherence and final
finite-stage composition are both proved rather than hidden in that hole.

LeanSearch returned Internal Server Error. LeanFinder, Loogle and source searches were used and
recorded; no absence verdict is inferred from the unavailable service. The Stacks source was read
at its locally available copy, including `equation-compute-pullback-to-limit`. No statement was
found false and no target or intermediate existing statement was changed.

## New nodes

`lem-weil-pbc-colimit-site-unit-zero-detection` is the single-sheaf inverse-image unit kernel lemma
from Stacks Tag 0A35. Its statement specializes the geometric portion of the original proof and
its complete proof in words explains transport to the supplied cocone and topology. Its Lean
module is `Sheaf.CategoryTheory.ColimitSiteUnitZeroDetection`; it is the sole remaining hole.

`lem-weil-pbc-varying-site-intermediate-unit-zero` makes the coefficient/system coherence step
explicit and applies the preceding single-sheaf lemma. Its theorem has a complete Lean proof in
`Sheaf.CategoryTheory.VaryingSiteIntermediateUnitZero`. No change record is needed because every
existing signature and public import is preserved and no existing module is adapted.

## Second reading by M1

1. **Interfaces: pass.** Compared the delivered original module with the repository using
   `diff -u` and the declaration parser. The sole existing declaration has a byte-for-byte
   unchanged signature, visibility and docstring. The differences are its proof and one plain
   proof import. The two other delivered modules are new; no definition, target, or claimed
   module of another group is changed. No change record is required.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all three modules
   through `lcompile.py --all`, without errors or warnings. Searched all delivered Lean sources:
   the only `sorry` is the entire named theorem `colimitSite_unit_zero_detection`; there are no
   forbidden declarations, hidden holes or definitions choosing unproved existence witnesses.
   A scratch module importing the sandbox compilations printed the axioms of all three main
   theorems and the two shared Arrow helpers. The main theorems use only `propext`,
   `Classical.choice`, `Quot.sound`, and the permitted remaining `sorryAx`; the helpers have no
   `sorryAx`. The original theorem therefore has a closed proof body, not an axiom-clean proof
   of the mathematical target. One old hole closed and one new hole added gives net zero.
3. **Split statements: pass.** Read Tag 0A35's section formula and its construction/adjunction
   argument in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/sites.tex`, together with
   the abelian section formula in `ColimitSites.lean`. The remaining theorem is the single-sheaf
   kernel consequence, with no coefficient system or Under presentation. The two closed
   reductions genuinely prove the omitted endpoint, naturality and coefficient-cocycle steps.
   Thus the remaining hole is strictly a part of the argument, not a renamed copy of the item.
   The zero-section case follows with the identity arrow and `map_zero`; for a constant identity
   diagram the unit is an isomorphism, and the premise forces the section to be zero. Filteredness
   excludes an empty index. No injectivity of arbitrary transition functors or coefficient maps
   is claimed. The docstring provides the category/topology transport, identity representative,
   filtered equality and additive-zero argument; the matching node is present. Independently
   searched LeanFinder with "kernel of adjunction unit for pullback to a filtered limit of sites
   detected at finite stage", Loogle for Arrow transport, the launcher's grep service for
   `colimitSite_unit|unit_zero_detection|compute_pullback_to_limit`, and both local Lean roots
   for unit kernels and colimit-site results. No existing supplied-site kernel lemma was found.
   The existing degree-zero representative is a surjectivity result and cannot detect this
   kernel. Transport from the existential constructed-site theorem is substantial remaining
   formal work; it cannot be closed by a short application of that theorem.
4. **Route and pruning: pass.** Read both reductions top downward. They use unit naturality and
   existing Arrow equality lemmas before the one new geometric hole. Both shared public helpers
   are used by the original proof and by the intermediate proof; the other helpers are private.
   Each public import supports statement vocabulary; each new proof-only dependency is a plain
   import. The report lists all three replaced direct proof dependencies, and correctly claims
   no pruned module. Checked `dag/units/sk-thm-p1.json`: no realized unit statement or step is
   bypassed or removed. All changes are below that unit's route.
5. **DAG: pass.** Checked every delivered node against its module and proof. Each `proof_deps`
   equals the union of the steps' `uses`. The existing node changes only `proof`, `proof_deps`
   and `proof_origin`. Both new nodes contain source, statement dependencies, proof in steps,
   origin, searches, creation information, blueprint ancestry, chapter, unit and Lean records.
   The original reduction uses the intermediate node, which uses the single-sheaf geometric
   node; the latter records the section-formula and filtered-equality dependencies.

Second-reading changes: added this independent review and extended the scratch axiom check to
both shared Arrow helpers. No repair of the delivered Lean proofs or nodes was needed. The sole
remaining hole and the net-zero decomposition are explicitly retained.
