## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.continuousLatticeIntersection_splitData`
with its original signature. The delivery contains the item module and three proved support
modules: `FiniteEtaleLocallyFreeModels`, `SplitProEtaleModuleProductMap`, and
`SplitProEtaleAbelianProductMap`, all under `Sheaf.Paper`.

The abelian comparison is proved on sections. Coproduct injections give disjoint open sheets;
the sheaf condition gives their product. Adjunction transposes identify the section restrictions
with the canonical composition/counit maps. Forgetful comparison, counit compatibility, product
preservation, and reflection of isomorphisms lift this result to internal condensed modules.

Finite common refinements and a coordinate-subtraction automorphism prove local finite freeness
of the integral pushforward and rational unit quotient. The original theorem uses their common
affine refinement, monicity of the unit from faithful inverse image, the existing integral
pushforward comparison, and the proved localization telescope/leg API to construct the three
coordinate isomorphisms and prove both equations. There is no dimension assumption on E or
noetherian assumption on X.

The retained proof was previously compiled within the per-file limit. A separate
`#print axioms` check for all four public declarations reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary check module is excluded from delivery.
Empty splitting families are covered by the sheaf argument; surjectivity supplies a nonempty
sheet family where a coordinate is selected. A one-sheet unit has zero cokernel. No data is
chosen from an unproved existence theorem, and no definition contains a proof hole.

Repair of the return at head `665a2e64a`: removed the duplicate `free_map`,
`free_comap`, and `free_pullback` declarations from both the item and the new
`FiniteEtaleLocallyFreeModels` module. Both now use the existing private lemmas of
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` through proof-only `import all`.
The item additionally removes its duplicate `free_standardPullback` and reuses the
support module's existing helper through `import all`; its duplicate `FreeAt` and
`normalizedPullbackIso` definitions are removed for the same reason. No existing
library declaration or public import changes. The item also removes `freeAt_comp` and
uses the existing `ProEtale.free_pullback_comp_iff` directly.

Final repair validation: all four modules compiled together in import order
(6.6, 5.1, 9.7, and 40.6 seconds). The actual `tools/import_prune_check.py`
passes separately for each module, including the item that triggered the return.
The public item signature is byte-for-byte unchanged; the node proof dependencies
match the union of their proof steps' references. All delivered lines satisfy
the 100-character limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLatticeIntersection_splitData`
(node `lem-weil-pbc-continuous-lattice-intersection-split-data`).

Added zero holes. No `sorry` remains in any delivered module. The three new public theorems
are also fully proved:

- `AlgebraicGeometry.ProEtale.splitProEtaleAbelianProductMap_isIso`.
- `AlgebraicGeometry.ProEtale.CondensedRing.splitProEtaleModuleProductMap_isIso`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtale_locallyFree_models`.

This closes one hole with no decomposition left outstanding.

## No longer needed

The item's direct import of `Sheaf.Paper.FiniteEtaleEtaleLocalSplit` is replaced by
`Sheaf.Paper.FiniteEtaleLocallyFreeModels`. The former remains needed inside that proved
support module, so it is not globally pruned.

No DAG node or existing library module is claimed globally pruned. The item no longer lists
`def-weil-proetale-inverse-image` as a separate proof step: the required inverse-image APIs are
used through the existing source definitions and `ProfinitePointPullback`; its statement
reference is unchanged. The old direct weakly-etale-base-change route is unnecessary.
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`,
`Sheaf.Paper.DirectImageSplitCoverProduct`, and `Sheaf.Paper.SplitCoverSectionsLimit` are not
imported: the latter two concern etale sheaves with constant ModuleCat coefficients, whereas
this proof directly treats pro-etale abelian sheaves and internal condensed modules.

Every new import is used. No unused provisional split or test module is delivered.

The repair removes ten repeated theorem declarations and two repeated local
definitions. Their results remain available through the two imports described above;
no source-library module or DAG node is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid, but its concrete weakly-etale base-change module belongs to
the old pro-etale functor tree. Importing it together with the current internal module functors
introduces duplicate declarations/notation. The proof instead uses the current
`FiniteCoefficient.UpperLowerStar` and `FiniteCoefficient.LowerShriek.Open` APIs and establishes
the needed product map directly. No shared source file was changed.

The local coordinate proof can use the separately locally free unit cokernel, without keeping
chosen sheet coordinates throughout the localization calculation. Invertibility of the pulled
adjoint follows from the existing localization colimit and its zeroth-leg uniqueness; it does
not require an extra scalar-localization counit theorem.

A private interface that packaged the whole family of chart isomorphisms into a cover caused
excessive unfolding of inverse-image and scheme limit definitions. Applying the comparison
on each neighbourhood before binding local free covers removes that cost. All proofs and
constructions remain in their natural modules; no compile-time limit was changed.

The earlier delivery overlooked the already available finite-freeness helpers in
`CondensedConstructibleSerre`, and repeated the normalized-pullback helper in two
modules. The retained independent reading below predates this repair; its import
and duplication conclusions are superseded by the repair notes above. The source
proof and public signatures are unchanged.

The coordinate proof is now written directly in
`continuousLatticeIntersection_splitData`: the two local-free models are obtained at
the start of its proof. This removes the repeated large signature of the former
private `splitData_of_free_pushforward_and_unit_cokernel` helper and the wrapper
application, without changing any mathematical step or public signature. Profiling
files remain in `scratchpad/` and are excluded from delivery; no timeout was increased.

Removed the unused local composition-isomorphism terms `aM` and `a` from
`SplitProEtaleModuleProductMap.moduleSheetMap_forget`; its original argument is
otherwise retained. The proof now substitutes the sheet equality before the
comparison calculation, eliminating `eqToIso` transports before the kernel
checks the diagram. The profiled full module compiles in 11.4 seconds instead
of timing out while checking the transported equality. No definition or
signature of a shared dependency changes.

The module product comparison also removes its two copies of
`ProfinitePointPullback.moduleUnit_forget` and `moduleUnit_forget_inv`, using the
existing inverse-unit lemma through proof-only `import all` instead. This avoids
a further duplicate whose text had different namespace qualifications.

The two final coordinate equations are proved by general categorical naturality
helpers in the item module. This keeps their proof terms independent of the
large concrete inverse-image and scalar-extension constructions and prevents
repeated unfolding during kernel checking. Both helpers are fully proved and
private; no statement is split off and no checking limit is changed.

Delivery-tool delay during repair: the required `deliver3.py --no-push`
run entered the global temporary-worktree-slot queue at 19:52 on October 16.
It had not obtained a slot by 20:23: the process was sleeping in the slot
acquisition loop of `sharedrepo.worktree`, before the dry run's compilation.
A slot finally became available around 20:26, after roughly 34 minutes. The dry run completed its four-module compilation and began the axiom probes, but had not printed OK as the hard stop approached. This is separate from Lean compilation; the complete final set compiled locally
in 6.6, 5.1, 9.7, and 40.6 seconds, with only the three permitted axioms.

## New nodes

`lem-weil-pbc-split-proetale-abelian-product-map` records the canonical abelian sheet product
comparison. It is fully proved, including the restriction identification and sectionwise
sheaf limit argument.

`lem-weil-pbc-split-proetale-module-product-map` records the fully proved lift through module
forgetful functors, with the canonical maps specified.

`lem-weil-pbc-finite-etale-locally-free-models` records the fully proved preservation of local
finite freeness by finite etale pushforward and by the adjunction unit quotient. The item node's
proof, proof dependencies, and proof origin now follow this route. The blueprint unit and the
item statement are unchanged. No change record is required: all existing signatures and public
imports are unchanged, and there are no adaptations of existing dependency modules.

## Earlier second reading (a previous round; superseded)

1. **Existing interfaces: pass.** Compared all four delivered modules with the shared
   repository. Only the item module already exists there. Its complete
   `continuousLatticeIntersection_splitData` signature, from `theorem` through `:= by`,
   is byte for byte unchanged, and its four public imports are unchanged. No existing
   definition, target, dependency module, or declaration signature is modified. The
   existing node differs only in `proof`, `proof_deps`, and `proof_origin`. The three
   other modules and nodes are new; their recorded Lean signatures are exact substrings
   of their modules. No change record or forced adaptation is needed.

2. **Proof and axioms: pass.** Independently compiled the four-module set in import
   order: abelian product map, module product map, local free models, and the item.
   Each completed without errors or warnings and within 60 seconds. Independently
   compiled a scratch axiom-check module against the sandbox outputs; all four public
   theorems have exactly `propext`, `Classical.choice`, and `Quot.sound`. Scanned every
   delivered module for holes and forbidden declarations: none. The noncomputable
   definitions are explicit adjunction, pullback, and scalar-extension isomorphisms.
   The choices of splitting covers and bases are from fully proved existence results,
   not an unproved arbitrary witness. The localization argument compares two colimit
   cocones using the zeroth leg and the proved localization-legs theorem; it does not
   assume an inverse-image/scalar-extension commutation result without proving it.

3. **New statements and edge cases: pass.** There are no split-off holes. Read Stacks
   Tag 095B (`lemma-pushforward-locally-constant`, lines 9973--9991 of the local
   `etale-cohomology.tex`) and Bhatt--Scholze Lemma 6.8.13 in the local PDF. The former
   supplies the split-cover/product argument; the new statements explicitly extend
   that argument to pro-etale abelian sheaves and internal coefficients. They do not
   claim that the paper states these exact generalized interfaces. The latter's
   noetherian global lattice theorem is not being asserted without its hypotheses:
   this item proves only its unchanged local coordinate statement.

   In the abelian comparison, the cofan hypothesis makes each sheet an open immersion;
   pullback sheets cover the test object and have disjoint ranges. Equal-index overlaps
   use monicity; unequal-index overlaps have empty source, hence terminal sections.
   This covers `n = 0`. In the locally free models, surjectivity supplies a sheet above
   the selected neighbourhood point, so the chosen `Fin n` coordinate exists. For
   `n = 1`, subtracting that coordinate leaves the empty biproduct, hence zero cokernel.
   An empty scheme is handled by the point-indexed empty cover. Rank zero and varying
   sheet ranks cause no issue: finite products are flattened only after finite common
   refinement, with no equality of ranks assumed.

   Repeated searches with different terms using the prescribed `msearch.py`:
   leanfinder, “Direct image of a locally constant finite free sheaf along a finite
   covering; quotient of the adjunction unit”, returned condensed locally constant
   adjunctions, not these results; loogle, `"cokernel", "biproduct"`, returned
   `cokernelBiproductιIso`, which the proof already uses; indexed grep,
   `locallyFree.*lowerStar|lowerStar.*locallyFree|unit.*cokernel`, returned no hits.
   Direct `rg` of both library roots and the upstream checkout found the etale disjoint
   cover API, adic coefficient results, and a private diagonal-cokernel calculation in
   `IntegralLfpLocalTorsionCharts`; none supplies this public pro-etale internal-module
   comparison. No shorter existing result was found.

4. **Route and pruning: pass after cleanup.** Followed the argument from the item
   downward: common compact free cover, faithful inverse image and mono unit, the
   existing integral pushforward comparison, preserved localization telescope, and
   conjugation by the three bases. The new local-free theorem is proved from finite
   etale splitting, canonical product comparison, and coordinate subtraction. The
   abelian and module comparisons explicitly identify the canonical counit maps, so
   the unit calculation is about the required map. The `realized` entries of
   `dag/units/sk-thm-properbasechange.json` name the projective-line, reduction, and
   torsion-assembly steps; this local auxiliary calculation bypasses none of them.
   Both removed old proof dependencies are accounted for under “No longer needed”:
   finite-etale local splitting remains inside the new models theorem, and the
   inverse-image API is used through the source and comparison modules. No library
   module is globally pruned. Checked public versus proof-only imports. An experiment
   making `Mathlib.Algebra.Category.Grp.AB` private failed at the new public signature
   with `Abelian Ab` missing; its public visibility is necessary and was retained.

5. **DAG agreement: pass.** Read the four node proofs with the Lean modules open.
   In each, `proof_deps` is exactly the union of the steps' `uses`; the existing item's
   five steps describe the actual proof. The three new nodes have the required source,
   search records, creation data, blueprint ancestry, chapter/unit, and exact Lean
   records. All three support theorems are proved, rather than restatements with holes.
   Their use graph is abelian comparison to module comparison to local free models to
   coordinate data. No new public statement depends on a private helper in its type.

**Changes by the second reader.** Removed the unused private `freeAt_comp` and
`freeAt_refine` lemmas from `FiniteEtaleLocallyFreeModels`: its actual refinement proof
uses the normalized `free_standard_refine` route. Corrected “small etale topology” to
“small pro-etale topology” in the new private disjoint-cover helper's docstring.
Added this independent review. Closed no further holes and added no holes; the delivery
still closes the single original hole with all three support theorems fully proved.

## Second reading by B2

1. **Existing interfaces: pass.** I diffed the item against the repository and
   compared its complete theorem signature through `:= by`: it is byte for byte
   unchanged, as are its four public imports. The three support modules are new.
   Their node `lean.statement` fields are exact substrings of their Lean files.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   No definition, target statement, or other existing module is changed.

2. **Proof and axioms: pass.** I compiled the four modules in import order through
   `lcompile.py`: 6.9, 5.7, 7.1, and 38.3 seconds, without warnings. A scratch
   axiom probe against the sandbox outputs reports only `propext`,
   `Classical.choice`, and `Quot.sound` for all four public declarations. Scanning
   all delivered Lean files finds no `sorry` or forbidden declaration, and no
   definition contains a proof hole. The choices of covers and bases come from
   fully proved results; the explicit isomorphism definitions use categorical
   constructions and do not hide arbitrary data chosen from an unproved theorem.

3. **New statements and edge cases: pass.** I read the local Stacks proof of
   `lemma-pushforward-locally-constant` (Tag 095B) and the local text of
   Bhatt--Scholze Lemma 6.8.13. The former supplies the finite split-cover/product
   argument; the new pro-etale/internal-module interfaces are explicitly agent
   variants. The latter is a noetherian global lattice theorem; the unchanged
   item proves only the local coordinate assertion and does not silently assert
   that global theorem without its hypotheses.

   In `splitSections_limit`, the coproduct isomorphism supplies open sheets,
   their pullbacks cover each test object, and disjointness makes cross-sheet
   overlaps empty. Equal-sheet overlaps use monicity. Thus the abelian product
   comparison also covers zero sheets. The module lift checks the actual
   counit maps using `moduleUnit_forget_inv`, composition coherence, product
   preservation, and reflection of isomorphisms. In `exists_split_sections`,
   surjectivity supplies a sheet over the chosen point, allowing the selected
   `Fin n` coordinate in `diagonal_cokernel`. Subtracting it from the other
   coordinates sends the diagonal to its biproduct injection; for one sheet the
   complement is empty and its cokernel is zero. Empty schemes use the empty
   point-indexed cover. Finite common refinement permits different local ranks.

   Fresh searches used leanfinder for faithful surjective etale pullback, loogle
   for `CategoryTheory.Adjunction, CategoryTheory.Mono`, and indexed grep for
   diagonal-cokernel and faithful-surjective APIs. Loogle finds
   `Adjunction.unit_mono_of_L_faithful`, already used by the proof's inferred
   instance. Direct `rg` in both library roots finds the etale disjoint-cover
   API, etale constant-coefficient faithfulness, and block-diagonal cokernel
   calculations. These do not supply the pro-etale internal-module comparison
   or the diagonal-to-selected-injection calculation. No shorter existing
   result was found. All three new support statements are fully proved;
   none is a renamed copy of the item with a new hole.

4. **Route and pruning: pass.** From the item downward I checked the free covers
   of the pushforward and unit cokernel, their common affine refinement,
   faithfulness and monicity of the rational unit, and invertibility of the
   pushed embedding's adjoint. `localizedAdjoint_isIso` preserves the explicit
   localization telescope, compares its zeroth leg with the pulled adjoint,
   then uses localization-leg uniqueness to obtain an isomorphism. The final
   two equations use categorical naturality, with the bases chosen earlier.
   No unit-level step is bypassed: the project's proper-base-change unit still
   realizes projective-line, reduction, and torsion-assembly steps unchanged.
   Both old dependencies removed from the item are accounted for under
   `No longer needed`; no module is globally pruned. All four import-prune
   checks exit zero. Proof-only imports, including `import all` for existing
   private transport helpers, preserve the public interfaces.

5. **DAG agreement: pass.** For all four nodes, `proof_deps` equals the union of
   the steps' `uses`. Their proofs describe the actual Lean route, with the
   support graph abelian product comparison to module comparison to local
   free models to coordinate data. The new nodes have source, search records,
   creation metadata, blueprint ancestry, chapter, unit, and exact Lean records.
   No new public signature depends on a private helper.

**Changes made by this second reading:** documentation only. I added this
current review section and independent verification results. No Lean proof or
statement required repair. The delivery closes the one original item hole,
adds no holes, and leaves no split-off obligation.
