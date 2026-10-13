## What changed

Completed the earlier sandbox proof of `DerivedCategory.localization_cone_construction` in
`Sheaf.RingTheory.MPseudoCoherentLocalizationConeConstruction`, preserving its signature and
all public imports. The three private proved helpers establish monotonicity of approximation
degree, finite top cohomology by localization descent, and a finite-free single-complex
approximation with an epimorphism on top cohomology. The final proof constructs the mapping
cone explicitly and uses its distinguished triangle and long exact homology sequence.

Proof imports are `FiniteHomologyOfMPseudoCoherent`, `Flat.Localization`,
`Localization.Finiteness`, and `ModuleCat.Projective` (under their Mathlib/Sheaf prefixes).
The existing node copy records the actual four-step proof. No new modules, definitions,
statements, public instances, or interface changes were introduced.

## Proved and sorry left

Closed one of one original holes: `DerivedCategory.localization_cone_construction`
(node `lem-pc-m-pseudo-coherent-localization-cone-construction`). Zero holes added and zero
sorries left anywhere in the delivered Lean module. The private helpers
`pseudoCoherent_mono`, `finite_top_of_local`, and `exists_top_approximation` are fully proved.
This is a proof, not a decomposition into new holed statements. The dry run also checks
axioms of all declarations against the three permitted axioms.

## No longer needed

Removed the original proof import `Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle`:
the finite-free single complex witnesses its own pseudo-coherence by the identity.
No assertion about pseudo-coherence of the localized cone is required by this item.
The corresponding node `lem-pc-ring-pseudo-coherent-distinguished-triangle` is not needed by this proof;
other items may still need it.

Replaced the planned `lem-weil-pbc-localization-module-exact` dependency with the Mathlib
leaf `lem-weil-pbc-localization-flat`: the proof establishes homology preservation via
flatness of extension of scalars directly. All other original proof dependency nodes
remain used. No unit statement or realized proof step is bypassed (this unit's realized
statement and step lists are empty).

Removed from the earlier sandbox attempt the unused imports
`Mathlib.Algebra.Category.ModuleCat.Descent`, `Mathlib.RingTheory.RingHom.Flat`,
`Mathlib.CategoryTheory.Abelian.Exact`, and the `import all` lines for
`Mathlib.RingTheory.OreLocalization.Basic`, `Mathlib.RingTheory.OreLocalization.Ring`,
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, and
`Mathlib.Algebra.Category.ModuleCat.Basic`. The narrower ordinary flat-localization import
suffices. The second reading also removed redundant imports
`Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, and
`Mathlib.RingTheory.Finiteness.Cardinality`; the remaining imports provide their needed
declarations transitively. Removing all three together compiles cleanly. No unused proof
imports remain.

## Where the brief, the DAG or earlier work was wrong

The earlier worker left a complete-looking sandbox proof but no report or delivery dry run.
It compiles with the current published library. This attempt verified it, removed unnecessary
imports, recorded its concrete proof steps in the node, and prepared the dry run.
The original DAG gave only one broad step; no mathematical statement correction was needed.
No arbitrary object is chosen from an unproved existence theorem: the finite module surjection
and projective lift use proved Mathlib theorems, and the complex and cone are explicit.
The argument includes the zero ring, empty localization family allowed by the unit-ideal
hypothesis, n=m, and zero top homology without additional assumptions.


## Second reading by C4

1. **Interfaces: pass.** Compared the complete delivered module against the repository
   with `diff -u`. The sole existing declaration, including its docstring and signature,
   is byte-for-byte unchanged through `:= by`. All original public imports remain.
   Only its proof, three fully proved private helpers, and plain proof imports change.
   No definition or public instance was added or altered; no change record is required.
2. **Proof and axioms: pass.** Independently compiled the original sandbox file and a
   scratch copy of the final pruned file with `lcompile.py`, without errors or warnings.
   A scratch `#print axioms DerivedCategory.localization_cone_construction` reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   Read every helper and the final proof: no `sorry`, forbidden declaration, or hollow
   definition occurs. The finite-free surjection is from proved `Module.Finite.exists_fin'`,
   and its lift is from proved `Projective.factorThru`; E and its mapping cone are concrete.
3. **Split-off statements: pass, none.** No new holes or public statements are split off.
   Checked the helpers on m=n, m<n, zero homology, and the zero ring. For an empty family,
   the unit-ideal condition forces the zero ring, and localization descent still applies.
   The projective single-complex construction uses no nonzero-generator assumption.
4. **Route and pruning: pass after repair.** Read the proof from the top downward and
   compared it with [Stacks Tag 066D](https://stacks.math.columbia.edu/tag/066D), its
   finite-free lift and cone paragraph. Searched with Lean Finder for a finite generated
   top-cohomology lift to cycles and with `rg` for single-complex approximation and
   pseudo-coherence monotonicity. No applicable shorter public theorem was found;
   `FiniteConeFreeExtension` is a different descending extension construction, and the
   similar monotonicity helper in `MPseudoCoherentLocalizationConeLocal` is private.
   Tested removal of each plain import, then removal of the three redundant ones together.
   The remaining four plain imports are needed by this proof. The No longer needed section
   accounts for the old proof dependency replaced by localization flatness and the removed
   triangle import. Read `dag/units/sk-thm-picard-duality.json`: realized statement and
   step lists are empty; no recorded unit realization or route is changed.
5. **DAG: pass.** Compared both node versions. Only `proof`, `proof_deps`, and
   `proof_origin` differ. Read each proof step against the actual helpers and final proof;
   their dependency union equals `proof_deps`. The replacement localization-flat node
   matches `IsLocalization.flat`; the other dependencies remain used. No new node needs
   the stage-3 new-node fields.

Second reading changed only three redundant plain proof imports and this report; the
mathematical proof and node record were retained.
