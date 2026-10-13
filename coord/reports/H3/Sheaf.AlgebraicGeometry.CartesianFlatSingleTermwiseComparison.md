## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison`
with a composition of three isomorphisms: localized cartesian base change, the inverse
of the supplied representative mapped through the localized derived pullback functor,
and its finite-free termwise computation. The existing declaration's signature,
universes, visibility and docstring stay identical. Its two new imports are private
proof imports. The original node now records this composition.

Added `Sheaf.AlgebraicGeometry.LocalizedMixedDerivedPullback`, which constructs the
intermediate functor from the canonical equivalence between localizations on W,
standard derived tensor pullback along g, and the exact derived inverse overEquiv V.
This is a real construction; its definition contains no `sorry` and chooses no arbitrary
witness of existence. Its two standard localization models are `HasDerivedCategory.standard`.

Added `Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange` for the geometric
comparison, without any complex P, termwise functor L or representative eP. Added
`Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel` for termwise computation,
without f, p, F, M, the cartesian square or a direct-image functor. Thus neither new
statement restates the original: they are independent parts joined by the mapped eP.
This retains the Noetherian approximation unit's comparison step and bypasses no unit.

Sources checked: [Stacks 0A1D](https://stacks.math.columbia.edu/tag/0A1D),
[06YD](https://stacks.math.columbia.edu/tag/06YD),
[06YJ](https://stacks.math.columbia.edu/tag/06YJ), and
[08FE](https://stacks.math.columbia.edu/tag/08FE). The local clone has the citation tables
but not the downloaded Stacks source; the cited statements and proofs were read online.

## Proved and sorry left

Closed `AlgebraicGeometry.cartesian_flat_single_termwise_comparison`
(node `lem-pc-cartesian-flat-single-termwise-comparison`): one upper hole closed by a
compiling proof from the two strictly smaller comparisons and the supplied eP.
This is a decomposition, not an axiom-free completion of its mathematical dependencies.

Added holes, each the whole proof of a public named theorem with a complete proof in
words in its docstring and a matching node:

- `AlgebraicGeometry.cartesian_flat_single_localized_baseChange`, node
  `lem-pc-cartesian-flat-single-localized-base-change`.
- `AlgebraicGeometry.localizedMixedDerivedPullback_finiteFree_model`, node
  `lem-pc-localized-mixed-pullback-finite-free-model`.

No hole remains in the item's module; no hole occurs in any definition. The remaining model computation was explored with compiled finite-free flatness and
K-flat open-pullback steps. Its complete localization composition was not closed in the
compiler time limit; the attempted proof remains only in the scratchpad and is not
delivered. The model
comparison was checked mathematically on zero complexes, rank-zero terms, arbitrary
bounds and empty opens: the functorial computations impose no extra hypothesis in these cases.

## No longer needed

No original import was removed, and no global pruning is claimed. The new model module omits the direct-image Basic import, the duplicate tensor
pullback import and the unused pullback-square import; the new geometric module omits
the duplicate tensor pullback import. These were only scaffold imports of new files,
not existing library dependencies. The original public
imports remain to preserve the module's public interface. The old direct proof
dependencies `lem-pc-restrict-derived-direct-image-open`, `lem-pc-rf-base-change-complex`,
`lem-pc-flat-complex-derived-pullback`, and `def-pc-ringed-spaces-derived-direct-image`
are replaced in the item's immediate proof plan by the two comparison nodes and the
constructed functor. The geometric and K-flat mathematics they express is retained
below those nodes; this replacement is decomposition, not pruning.

## Where the brief, the DAG or earlier work was wrong

The stated dependency modules were not actually imported by the original module;
it had only public statement imports. No existing theorem directly matches the
independent universes and arbitrary cartesian square of this item. In particular,
`relativelyFlat_derivedBaseChange_complex` has one universe for all scheme localizations
and a canonical pullback square. `nonempty_derivedBaseChange_iso_of_isFlatOver` additionally
requires separatedness, so it cannot be applied under this item's quasi-separatedness
hypothesis. These are interface gaps, not evidence that the statement is false.

The blueprint ancestor utility cannot follow `created.item` for this node because that
field contains a module name. The new records therefore inherit the original node's
explicit ancestor `lem-pc-coherent-hi` and prepend this item node to its `via` list.
No statement, definition or public interface of an existing dependency was changed;
there are no forced adaptations or change records.

## New nodes

`def-pc-localized-mixed-derived-pullback`:
`Sheaf.AlgebraicGeometry.LocalizedMixedDerivedPullback`, declaration
`AlgebraicGeometry.localizedMixedDerivedPullback`. Explicitly constructs the canonical
mixed-universe localized pullback; no new proof hole.

`lem-pc-cartesian-flat-single-localized-base-change`:
`Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange`, declaration
`AlgebraicGeometry.cartesian_flat_single_localized_baseChange`. Splits off the geometric
open/cartesian/relatively-flat comparison before choosing any model.

`lem-pc-localized-mixed-pullback-finite-free-model`:
`Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel`, declaration
`AlgebraicGeometry.localizedMixedDerivedPullback_finiteFree_model`. Splits off the
K-flat computation and ordinary pullback composition, independently of direct images.

All nodes record LeanFinder, Loogle, source grep and the attempted LeanSearch query;
LeanSearch returned an Internal Server Error. The blueprint search found no exact
mixed-universe comparison. No new node replaces a unit statement or its route.

## Second reading by H3

1. Unchanged interface: compared every delivered module with the repository using
   `diff`. The three auxiliary modules are new. In the existing item the only edits
   are two private proof imports and the theorem body; the existing signature,
   universes, visibility and docstring are byte-for-byte unchanged. No existing
   definition or target statement changes, and no change record is required.
2. Proof and construction: inspected the three-isomorphism composition and its
   directions. The inverse of eP correctly takes the direct image to the restricted
   representative. The mixed pullback is constructed explicitly using localization
   uniqueness, standard derived pullback and the exact inverse open-site equivalence;
   it chooses no new arbitrary existence witness. Only the two listed public named
   theorem proofs contain `sorry`; no definition does. Compiler and explicit axiom
   probe results are recorded below when complete.
3. Split statements: read Stacks Tags 0A1D, 08FE, 06YD and 06YJ independently.
   The geometric statement uses open restriction, relative flat base change with
   the structure-sheaf unit, and transport of localization models. The model statement
   uses bounded-above finite-free K-flatness and exact open restriction, independently
   of any direct image or cartesian square. Each is a strictly smaller part of the
   argument, rather than a renamed copy of the original statement. Checked zero
   sheaves, zero/rank-zero complexes, arbitrary integer bounds, empty opens and the
   identity square: the comparisons remain valid without a new hypothesis.
   Repeated LeanFinder search with “K-flat complex exact restriction derived tensor
   inverse image localization equivalence”, Loogle with “Localization.uniq” (service
   reported unknown identifier), service grep with “derivedBaseChange|mapDerivedCategoryFactors|
   flatComplexDerivedPullback”, and local rg with alternate base-change and exact
   restriction terms. No exact duplicate was found; ordinary exact-functor
   factorization and K-flat computations are components already in the library.
4. Shortest route and pruning: read the existing relatively-flat complex and flat
   complex computation theorems. The former uses a common localization universe and
   canonical pullback; the simpler single-module result additionally requires
   separatedness. Neither applies immediately to this arbitrary cartesian square
   with independent supplied models. The imports are for signature/definition data
   or the two proof comparisons, with proof-only imports private. The report lists
   every old immediate proof dependency replaced; none is claimed globally pruned.
   The unit record sk-thm-picard-coherence has empty realized statement/step lists;
   its Noetherian approximation route and this comparison's place on it are retained.
   No additional split theorem was closed during this reading.
5. DAG agreement: checked all four records, their self-contained statements, sources,
   proof steps, dependency unions, origin, search records, creation metadata,
   blueprint ancestry and Lean declaration records. The existing node describes
   the actual three-isomorphism composition. The new definition's node describes its
   actual composite. Repaired the finite-free model node to name the existing
   lem-pc-flat-complex-derived-pullback used in its docstring's planned computation.

Second-reading changes: added that missing planned proof dependency, independent
search records and this review;
no Lean declaration or proof was changed. This remains one upper hole closed and
 two lower holes added (decomposition, net minus one hole), with no global pruning.
A read-only git status command was mistakenly run at the start despite the brief;
no manual git mutation was performed. Subsequent comparisons used only file reads.

Explicit scratch-copy `#print axioms` compiled successfully: the constructed
`AlgebraicGeometry.localizedMixedDerivedPullback` has exactly `propext`,
`Classical.choice`, `Quot.sound`; the original theorem and each of the two split
comparison theorems have those three plus `sorryAx`, as expected for this
reported decomposition. No additional axiom occurs. The scratch copy was removed.

All four delivered modules compiled successfully with `lcompile.py --all`, with
no errors or warnings. Reported elapsed times include shared-slot waiting.
