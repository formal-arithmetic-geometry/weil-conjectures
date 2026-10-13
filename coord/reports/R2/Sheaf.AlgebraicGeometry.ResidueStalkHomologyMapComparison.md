## What changed

Repair of the returned delivery: generalized the private helper
`strictlyPerfect_single_restricted_unit` in place to an explicit arbitrary integer
`i`, with support bounds `[i,i]`, the rank-one identification at `i`, and zero
terms off `i`. The target applies this lemma at `0`. This removes the word-for-word
duplicate statement identified by `import_prune_check.py`. Reusing the existing
private helper through `import all` was tested, but importing
`Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk` would close an import cycle:
that module already reaches this item. Thus this repair uses the return entry's
explicitly permitted generalization alternative, without changing that module or
any public interface. The generalized proof compiles for all integers, including
negative degrees; no new hole or dependency is added.

Replaced the sorry in `AlgebraicGeometry.isIso_residue_stalk_homologyMap` with a
complete proof from two separate natural comparisons. The existing signature and
visibility are unchanged. A private proof verifies strict perfectness of the
single restricted structure sheaf in any integer degree, specialized at degree zero. Naturality of the open restriction comparison
transports `ha`; functoriality and `hα` make the localized derived arrow invertible;
the strictly perfect comparison and cancellation give the stated homologyMap.

Added the concrete functor `AlgebraicGeometry.localizedResidueHomology`, using
standard localizations on the open subscheme and its residue scheme. Its data is
an explicit composite of already defined functors, with no new choice from an
unproved mere-existence statement.

Added and proved `AlgebraicGeometry.exists_localizedStrictPerfectResidueHomology_iso`.
Its private K-flatness helper proves that every transported strictly perfect
complex is K-flat, using finite-free stalk retractions, bounded-above flat module
K-flatness, and the stalk criterion. The main proof constructs the natural
comparison from the chosen derived counit, exact localization, exact global
sections, and the existing natural residue tensor-stalk isomorphism. Abstracting
the constructed natural transformations inside the proof prevents repeated
expansion of the derived constructions. The resulting inverses satisfy the
naturality equation for every chain map.

Added `AlgebraicGeometry.nonempty_localizedResidueHomology_restriction_iso` as the
remaining open-restriction/composition comparison. It applies to all derived
objects and does not mention the target's representing arrow, `ha`, `c`, `e` or
`hα`. Its docstring contains the full geometric argument and the auxiliary
localization-universe transport. Updated the original DAG proof and added nodes
for the construction and both comparisons.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.isIso_residue_stalk_homologyMap`
(node `lem-sc-residue-stalk-homology-map-comparison`). No sorry remains in the item.

Also proved the new comparison
`AlgebraicGeometry.exists_localizedStrictPerfectResidueHomology_iso`
(node `lem-sc-localized-strict-perfect-residue-homology`) and its private helpers
`strictlyPerfect_overEquiv_isKFlat` and `inverse_naturality_of_isIso_app`.
The item's private `strictlyPerfect_single_restricted_unit` is proved for arbitrary
integer degree and specialized at zero in the main proof.

Added exactly one hole:
`AlgebraicGeometry.nonempty_localizedResidueHomology_restriction_iso`
(node `lem-sc-localized-residue-homology-restriction`). This is the only sorry in
these four delivered modules. Its conclusion is a natural functor comparison,
not the isomorphism assertion of the original theorem under another name.

This delivery is a decomposition: one original hole closed, one new hole added,
net zero new/closed holes before the maintainer's import-closure ledger. The
termwise naturality and K-flatness arguments are complete proofs from existing
named declarations. Existing imported holes, notably the residue global-sections
comparison, are unchanged.

## No longer needed

Removed the direct proof imports from the item:
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`,
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`, and
`Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections`.

`lem-pc-flat-complex-derived-pullback` and its module
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` are no longer used by this
proof route: the chosen derived counit is applied directly after the proved
stalkwise K-flatness argument. The composition and residue global-sections
nodes remain needed below the two comparison modules; removing their direct
imports from the item does not claim they are globally unnecessary.

No unit statement, unit proof step, or module realizing one is bypassed. No
other original node is claimed unnecessary, and no whole-library pruning claim
is made.

## Where the brief, the DAG or earlier work was wrong

The original plan did not supply a natural comparison between exact localized
restriction and derived residue pullback with independent chosen localization
universes. The composition theorem assumes a common family of derived categories
for all schemes, whereas the item supplies only S, its over-sites and the residue
schemes of S. The new construction uses standard localizations on U and its
residue scheme; the remaining comparison states the required transport explicitly.
Object-only residue cohomology isomorphisms cannot replace naturality for the
fixed representing arrow.

The termwise comparison needed actual finite-free stalk retractions and natural
counit comparisons, rather than treating arbitrary object isomorphisms as
natural. These parts are now proved. The existing statement was not found false.
Zero complexes, zero maps and shifts are covered by the same naturality proof;
an empty open has no point to which either new theorem applies.

LeanSearch was attempted for the new concepts but returned Internal Server Error.
LeanFinder, Loogle, and local source searches were used and recorded. No exact
existing comparison was found. The primary source tags were read online because
the local clone contains the literature inventory but not the Stacks source:
[06YJ](https://stacks.math.columbia.edu/tag/06YJ),
[0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
[0098](https://stacks.math.columbia.edu/tag/0098).

## New nodes

`def-sc-localized-residue-homology` records the explicitly constructed localized
derived residue homology functor in `LocalizedResidueHomology.lean`.

`lem-sc-localized-residue-homology-restriction` records the remaining natural
comparison under open restriction in `LocalizedResidueHomologyRestriction.lean`.
It is a geometric comparison for every derived object, with a full proof in words.

`lem-sc-localized-strict-perfect-residue-homology` records the proved termwise
comparison and its naturality in `LocalizedStrictPerfectResidueHomology.lean`.
All three nodes inherit the original chapter and unit, and trace their blueprint
origin to the theorem of the cube's structure-sheaf pushforward argument.
No change record or forced adaptation is needed.
The second reader added the two missing planned proof-dependency imports
`Sheaf.Topology.PointModuleEvaluationEquivalence` and
`Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections` to
`LocalizedResidueHomologyRestriction.lean`; both are private imports.


## Earlier second reading (a previous round; superseded)

1. **Interface unchanged: pass.** Diffed the entire item against the repository.
   Only private imports, a private theorem, and the target proof differ. The existing
   `isIso_residue_stalk_homologyMap` signature and docstring are byte for byte unchanged;
   there is no changed definition or target statement. The existing node differs only
   in `proof`, `proof_deps`, and `proof_origin`. The other three modules are new.
2. **Proof and data: pass.** All four modules compiled locally in import order without
   errors or warnings. The sole textual hole is the named public theorem
   `nonempty_localizedResidueHomology_restriction_iso`, with its node and full proof
   docstring. No forbidden declaration, tactic option, or hollow definition occurs.
   Scratch-copy `#print axioms` checks gave only `propext`, `Classical.choice`,
   `Quot.sound` for the new functor; the target and the two comparisons also use
   `sorryAx` from the named remaining and imported open statements.
   `localizedResidueHomology` is an explicit functor composite using standard
   localizations, not an arbitrary witness. The chosen derived pullback is specified
   by its universal property, and the comparison witnesses are used only inside
   theorem proofs. The target first conjugates the image of `a` by natural restriction,
   applies `hα` and functoriality, then uses the simultaneous strictly-perfect comparison
   and cancels its invertible target component. The private source-perfectness proof
   handles degree zero by the rank-one free module and every other degree by zero.
3. **New statements and edge cases: pass.** Read the construction and both comparisons
   in Lean and their nodes. The strictly-perfect comparison asserts a family of
   isomorphisms with naturality for every chain map; its proof constructs exactly that
   family from a natural transformation invertible on strictly-perfect objects.
   The remaining restriction comparison has no representing arrow, perfectness,
   `ha`, `c`, `e`, or `hα`: it is just the geometric restriction/scalar comparison,
   strictly one part of the original argument. The open immersion's residue-field
   map goes from the residue field on S to the one on U, matching `extendScalars`.
   Its map is an isomorphism (Mathlib ResidueField.lean, line 177), and the residue
   square is the identity at line 261. Zero objects/maps and shifted complexes work
   functorially; an empty open supplies no point. No connectivity or negative-degree
   condition is hidden. Read the sources
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S),
   [0098](https://stacks.math.columbia.edu/tag/0098), and
   [08DW](https://stacks.math.columbia.edu/tag/08DW).
   Repeated LeanFinder, Loogle and local searches with different queries, recorded
   in the new nodes. No existing exact natural comparison was found. The existing
   K-flat residue-cohomology theorem is only an object comparison and cannot supply
   the required square for a fixed chain arrow. The remaining hole requires further
   localization and residue-field transport, not a short application of the existing
   independent-universe open-restriction theorem; it remains explicitly open.
4. **Route and pruning: pass, with a pre-existing bookkeeping gap.** The proven K-flat
   helper uses finite-free stalk retractions, projectivity/flatness, bounded-above
   tensor acyclicity and the stalk criterion. The main natural comparison uses the
   derived counit, exact localization, exact global sections and the residue
   tensor-stalk isomorphism. These are genuine reductions below the cube unit;
   its general-cube/structure-sheaf route is kept. Read
   `dag/units/sk-prop-av-cube.json`, including its imported blueprint statement and
   proof step. The standalone blueprint section is absent on this machine. The
   `realized` statement and step arrays are empty already in the repository. This
   delivery does not change
   them or bypass a realizing node. Of the three old proof dependencies,
   `lem-pc-flat-complex-derived-pullback` is unused by this route;
   `lem-pc-ringed-spaces-derived-pullback-composition` and
   `lem-sc-residue-pullback-global-sections` remain dependencies of the comparisons.
   All three removed direct imports are listed above. Public imports support types,
   signature-local instances or the concrete public definition; extra proof imports
   are private. No whole-library module pruning is asserted.
5. **DAG agreement: repaired and pass.** The original node's three steps match source
   strict perfectness, natural conjugation, and cancellation. The new construction
   node has no proof dependencies; the proven natural-comparison node lists precisely
   the stalk-projectivity, bounded-flat, stalk-K-flat, derived, evaluation, and residue
   comparison inputs. The open restriction node has the source/docstring proof,
   independent-universe restriction and composition dependencies, required creation,
   blueprint, search, chapter/unit and verbatim Lean records. Its last planned step
   also names the point-evaluation and residue-global-sections nodes, but its imports
   omitted their modules: added those two private imports to make the plan executable.

Changes made by this reading: the two missing private proof-dependency imports,
additional actual search records, and this review. No proof or statement was rewritten.
The delivery remains a decomposition: one original hole closed, one new hole added.


## Second reading by R2

1. **Interfaces: pass.** Compared the delivered item with the read-only repository
   using a textual diff and checked its entire theorem signature byte for byte.
   The existing signature, visibility and docstring are unchanged. The other three
   modules are new; no existing definition is changed and no adaptation is present.
2. **Proof and construction: pass.** Compiled all four modules locally in import
   order, with no errors or warnings (3.9, 3.2, 42.8 and 12.4 seconds). The only
   textual sorry is the reported public restriction-comparison theorem. No forbidden
   declaration or hollow definition occurs. A scratch module's explicit print-axioms
   checks show only propext, Classical.choice and Quot.sound for the constructed
   functor, and those plus sorryAx for the two comparisons and original theorem.
   The functor is an explicit composite with standard localizations; derived
   pullback is determined by its universal property. The proven comparison builds
   a natural transformation from the derived counit and tensor-stalk comparison,
   then inverts its strictly-perfect components. The main proof conjugates a by
   natural restriction, uses ha and halpha, and cancels the invertible component.
3. **Split statement: pass.** Read the remaining comparison's full proof docstring
   and node. It concerns all derived objects and omits the target's representing
   arrow, perfectness and invertibility assumptions: it is a separate geometric
   part of the argument, not a renamed target. The residue-field scalar map has
   the correct direction and is invertible for an open immersion. Empty opens
   have no point; identity opens, zero objects/maps and shifts require no extra
   hypothesis. Fresh LeanFinder search for exact open restriction commuting with
   residue derived pullback found only ordinary restriction formulas. Fresh Loogle
   search for residueFieldMap found the existing residue-square identity and
   open-immersion isomorphism, but no derived natural comparison. Local rg over
   Sheaf and WeilConjectures found object-only residue cohomology comparisons
   and the already cited generic restriction theorem. Read its independent-universe
   interface and the composition interface: completing the remaining comparison
   still requires localization and scalar transport, not a short direct application.
4. **Route and pruning: pass.** Read the cube unit record. Its statement and general
   cube proof step are preserved; its realized arrays were already empty. The
   generalized single-complex helper proves all integer degrees, with finite-free
   rank one at its chosen degree and zero elsewhere. The shorter K-flat route
   uses the existing stalk-projectivity, bounded-flat and stalk-criterion results.
   All removed direct imports are reported. FlatComplexDerivedPullback is the
   unused old proof dependency; composition and residue global sections remain
   needed inside the new comparisons. Public imports support public signatures
   or the concrete definition; proof-only comparison imports are private.
5. **DAG: pass.** Checked the existing node diff: only its proof, proof_deps and
   proof_origin change. Checked all three new nodes' complete records, proof
   dependency unions, chapter/unit, provenance and exact Lean signatures. The
   original node's steps match strict perfectness, natural conjugation and
   cancellation. The new natural-comparison node matches the actual K-flatness,
   counit, evaluation and residue comparison proof. The remaining node's planned
   imports are present and private.

Changes made in this reading: appended this independent review and performed fresh
search, compilation and axiom checks. No Lean or DAG repair was necessary. The
delivery closes isIso_residue_stalk_homologyMap and adds only
nonempty_localizedResidueHomology_restriction_iso as an open hole: a decomposition
of one original hole into one lower hole, with no claim of positive net progress.
