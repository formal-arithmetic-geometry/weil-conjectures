## What changed

Replaced the rejected finite-support cocycle split with a finite-piece bar construction. The new `Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData` module states the geometric input as strict augmentation data and leaves its complete construction as one named theorem. The cocycle module is proved from this data by choosing zero comparison cochains; the parent module keeps its cone assembly proof and imports only the cocycle module.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_flat_telescope_arrow_cocycles` from the strict bar-data theorem, and retained the complete cone-assembly proof of `AlgebraicGeometry.exists_flat_telescope_arrow_diagram`. The legacy construction wrapper remains proved from the unconditional parent theorem. The only added and remaining sorry is `AlgebraicGeometry.exists_flat_telescope_arrow_bar_data` (node `lem-sc-flat-telescope-arrow-bar-data`), in the new module. It is the finite-piece bar construction and target homotopy-equivalence theorem. On the current baseline, `AlgebraicGeometry.exists_flat_telescope_arrow_diagram_construction` is the one holed declaration: one hole closed and one added, net zero. This is a decomposition, not a completed geometric proof. The already-proved unconditional parent declaration keeps its signature and now performs the cone assembly itself. The cocycle theorem (node `lem-sc-flat-telescope-arrow-cocycles`) is a new proved declaration, with no sorry. The private helpers `telescope_augmentation` and `cone_comparison` are fully proved. No data are chosen inside a definition.

## No longer needed

Removed the parent proof imports of `Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagramCore`, `Sheaf.Algebra.Homology.BoundedFlatReplacement`, and `Sheaf.Algebra.Homology.FlatTruncationTower`; the parent proof now uses only the cocycle module and Mathlib cone APIs. The core node `lem-sc-flat-telescope-arrow-diagram-core` and module `Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagramCore` are no longer needed by this module. The cocycle module also removes its earlier proof imports of bounded replacement and truncation tower. No global pruning of those two modules is claimed: their nodes `lem-pc-kflat-bounded-flat-replacement` and `lem-pc-flat-truncation-tower` remain construction ingredients below the new bar-data theorem. No other planned node is pruned. The bounded replacement and truncation tower remain dependencies of the new bar-data theorem, whose module now imports both privately to retain the construction plan in the import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery claimed that finite support of each generator lets a whole source stage factor through one target stage. This is false for an infinite free source mapping into a filtered union of finite target stages. The replacement uses all finite subcomplexes as a filtered bar diagram and enlarges the target tower by finite cone blocks; homotopy equivalence is obtained from split filtrations and bar homotopies. The strict bar-data theorem supplies tower and target augmentation data, while omitting the source-cone map and both cone-map equalities proved in the parent. Its proof is an agent expansion of the parent construction, not a literal assertion of Stacks 077J, 06YS, or 06YJ. The previous second reading is superseded by this repair; the independent reading of this repair is recorded below. Existing public signatures and public imports are unchanged. The unit `sk-thm-picard-duality` has empty realized lists here and its route is unchanged. No definition or consumer is modified, and no change record or forced adaptation is needed. Edge cases: zero arrows give zero factor maps, identity arrows use the same finite-piece indexing, and the empty scheme admits zero diagrams. In the previous countably generated source example, the source bar stage is a sum over all finite pieces and the target bar stage receives those pieces individually; no uniform bound on the old target indices is required.

## New nodes

`lem-sc-flat-telescope-arrow-bar-data` records the remaining finite-piece bar construction in `dag/nodes/sec-picard-framework/lem-sc-flat-telescope-arrow-bar-data.json`, with module `Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData`. LeanSearch was unavailable; LeanFinder, Loogle, local library and Mathlib grep, and blueprint searches supplied cone and Dold-Kan APIs but no simultaneous tower construction. Its docstring gives the construction argument: affine flat generators, finite subcomplex filtration, bar enlargement, strict sums, and target homotopy equivalences.

`lem-sc-flat-telescope-arrow-cocycles`, in `dag/nodes/sec-picard-framework/lem-sc-flat-telescope-arrow-cocycles.json`, records the proved zero-cochain consequence in `Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles`. This node was present in the rejected sandbox but is new relative to the repository. Its old geometric proof has been replaced by the strict augmentation equations, and it has no remaining hole. Its searches locate the Mathlib cone descent and comparison APIs but no geometric construction theorem.

## Second reading by F1

1. Compared the parent module with the repository version, by diff and by extracting
   each existing declaration signature. Both
   `AlgebraicGeometry.exists_flat_telescope_arrow_diagram` and
   `AlgebraicGeometry.exists_flat_telescope_arrow_diagram_construction` have
   byte-identical signatures. Public imports are unchanged. There are no definition
   changes, forced adaptations, or change records. Verdict: pass.
2. Compiled the three modules in import order with `lcompile.py --all`, without
   errors or warnings. Read the cone descent, cochain comparison, zero-cochain
   consequence, and legacy wrapper. There is exactly one sorry, the named
   `AlgebraicGeometry.exists_flat_telescope_arrow_bar_data`; no definition or private
   helper contains a hole and no forbidden declaration mechanism occurs. Scratch
   axiom checks cover both helpers and all four public theorems; the helpers use
   only standard axioms, and the public theorems additionally depend on `sorryAx`
   through the explicitly reported geometric input. Verdict: pass as a decomposition,
   not as a completed proof independent of sorry.
3. Read the full bar-data statement and construction, checked Stacks 077J and 06XX
   against their actual statements, and repeated searches with different terms:
   LeanFinder for split filtrations and telescope/bar homotopy equivalences, Loogle
   for cone descent, and grep for simplicial replacements, homotopy colimits, and
   flat-telescope declarations. Found cone descent and generic Dold--Kan/extra-
   degeneracy APIs, but no existing simultaneous flat-tower theorem. The remaining
   theorem omits source-cone construction and both comparison equalities; those
   are actual Lean reductions, not a renamed application of the original item.
   Checked finite-piece support (including infinitely many source generators),
   zero and identity arrows, and zero complexes on the empty scheme. The finite
   affine-generator pieces are bounded in both directions; bar stages remain
   bounded above even with arbitrarily long simplex strings. The target filtration
   is split by named summands; its split exact telescope sequence gives a homotopy
   equivalence, rather than cancellation of a mere quasi-isomorphism. The cited
   split generator-valued tower is stronger than the existing flat-only Lean
   tower, and the docstring explicitly constructs it from the cited literature.
   Verdict: the geometric input is a proper remaining construction subproblem.
4. Reviewed from the target downward. Mathlib supplies the source augmentation and
   comparison homotopies; the proved cocycle theorem is their zero-cochain input.
   The old core dependency is bypassed; the report accounts for every removed old
   proof dependency. The bounded-replacement and truncation-tower modules remain
   needed below the bar construction, so no global pruning of them is claimed.
   Checked `dag/units/sk-thm-picard-duality.json`: its realized lists are empty
   here, and this delivery changes none of its unit statement or steps. Verdict:
   pass, with the dependency-import repair below.
5. Checked all four node signatures against the Lean (whitespace normalized),
   proof steps and dependency unions against the actual reduction, and the new
   nodes' sources, searches, creation records, blueprint ancestry, unit, and chapter.
   Existing node edits are confined to `lean`, `proof`, `proof_deps`, and
   `proof_origin`. Verdict: pass.

Changed only the bar-data module's proof imports: restored private imports of
`Sheaf.Algebra.Homology.BoundedFlatReplacement` and
`Sheaf.Algebra.Homology.FlatTruncationTower`, which its node and natural-language
construction retain. Updated the pruning report accordingly. No theorem statement
or Lean proof body was changed by this reading. One old hole is closed and one new
hole is added, net zero; two existing parent declarations have proof bodies, with
the new geometric theorem still open. All checks and the delivery dry run are
performed using the prescribed launcher tools.
