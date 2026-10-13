## What changed

The proof of `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_surjective`
is complete, with its original signature and visibility unchanged. Two proof-only imports
provide separate statements for the geometric derived-image dictionary and the general
perfect-complex matrix argument. No existing definitions, signatures, or public imports
were changed. The item's node now records the actual proof and its two dependencies.

The proof chooses standard derived-category localizations, obtains the derived truncation
map and its exact comparison square, applies the universal lowest-cohomology criterion,
and maps that square through the ordinary stalk functor. It explicitly lifts a target germ
through two bijections and cancels the target comparison. In particular, it proves the
surjectivity of the specified `moduleBaseChangeMap`, not of an arbitrary map between
isomorphic modules. The choice of derived data occurs only inside a theorem proof; no
object is defined from an unproved mere-existence assertion.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_surjective`
(node `lem-sc-picard-base-change-stalk-surjective`). No sorry remains in the item's module.

Added two strictly intermediate holes, each in its own new module:

- `AlgebraicGeometry.Scheme.picardRankMatch_derived_truncation_data`
  (`lem-sc-picard-rank-match-derived-truncation-data`, module
  `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData`). This asserts the
  connective perfect derived-image data, the universal rank charts, and the exact
  degree-zero comparison square. It asserts no surjectivity or invertibility of the
  pulled-back truncation map or ordinary base-change map. Its argument uses relative
  flatness, canonical derived base change, the rank dictionary, and mate compatibility;
  it does not use the matrix-zero argument.
- `AlgebraicGeometry.Scheme.perfect_universalH0_truncation_pullback_isIso`
  (`lem-sc-perfect-universal-h0-truncation-pullback`, module
  `Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback`). This is a general
  derived-category statement with no proper morphism, Picard module, rank-match
  predicate, or ordinary base-change map in its signature. It supplies the canonical
  matrix argument for an already supplied derived morphism and rank charts.

This is a decomposition, not a net reduction of holes: one original hole closed,
two new holes added. The existing sorries in imported library modules are unchanged.
All three delivered modules compile under lcompile.py; the main proof's explicit
stalk transport also compiled against the two sibling modules.

## No longer needed

No existing import was removed: all original imports are public and contribute to the
existing interface. The two additional imports are proof-only.

The representing-immersion theorem `lem-sc-perfect-h0-locally-closed` and its module
`Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus` are not needed for this proof:
we need the canonical comparison on each matrix chart, rather than construction of
an immersion representing the rank functor. Thus they were not added as proof imports.
The representing-locus construction is pruned from this item's route only; this does
not assert that it is absent from every other target's closure.

The full open-square theorem `moduleBaseChangeMap_open_restriction` is not invoked by
the new main proof. Its module remains public because it defines `moduleBaseChangeMap`.
Exact open restriction is used internally to the general criterion and the comparison
dictionary. The original perfect direct-image, residue-model, pullback-composition and
adjunction dependencies remain needed inside the two split steps; they are not pruned.
No unit statement or unit proof step is bypassed (`sk-prop-av-cube` has empty realized
entries for this node).

For completeness, all seven old direct `proof_deps` disappear from the main node's
list. Their disposition is:

- `lem-sc-perfect-h0-locally-closed`: removed from this route.
- `lem-sc-perfect-finite-free-residue-model`: moved to the general truncation criterion.
- `lem-pc-rf-perfect-base-change`: moved to the geometric derived-data lemma.
- `def-sc-picard-universal-rank-match`: retained in the signature and used in the
  geometric derived-data lemma.
- `lem-pc-module-pullback-identity-composition` and
  `lem-pc-module-pullback-adjunction`: moved to the geometric derived-data lemma.
- `lem-weil-pbc-module-base-change-map-open-restriction`: its definition remains in
  the main signature; its compatibility theorem is used in the geometric dictionary.

Only the representing-locus module is pruned from the planned proof route; none of
these modules is asserted to leave the whole target import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's declared lowest-cohomology-locus and universal-pullback theorems
supply `Nonempty` object isomorphisms, not an equality identifying the canonical map.
Using those alone cannot prove surjectivity of the adjoint-defined map. The new general
criterion concerns the actual pulled-back derived arrow, and the new geometric dictionary
pins its degree-zero map to the exact ordinary comparison. This missing canonical
compatibility is now explicit instead of being hidden in a transport step.

The uniform-rank chart requires care when fibres are empty. Properness gives an open
empty-fibre locus, and flat finite presentation makes the nonempty-fibre locus open too.
Choose rank zero on the former. On the latter, ranks of E after a common residue-field
extension force every test rank to equal the chosen rank. This is spelled out in the
new geometric theorem's proof in words. No connected-fibre assumption is introduced.

The ancestor helper printed `blueprint.from.node = None` for this newly created item;
the item itself already records `thm-sc-theorem-of-cube` as its blueprint ancestor.
The new nodes preserve that recorded ancestor and its omitted-detail place. Blueprint
searches for universal lowest cohomology, lowest cohomology, Picard rank, degree-zero
base change and truncation found no existing blueprint statement of these new canonical
interfaces. Existing relevant stated modules were read before the new statements.

## New nodes

`lem-sc-perfect-universal-h0-truncation-pullback` is the canonical-arrow strengthening
needed beyond the existing object-only universal-lowest-cohomology pullback theorem.
Its source is Stacks 0BDL's matrix-chart proof, with 0BCD, 08CR and 06YD supplying the
model, actual chain-map representative and termwise derived pullback. The node records
performed LeanFinder, Loogle and grep searches; LeanSearch returned an internal server
error and is recorded as unavailable. Rank zero, empty schemes, disconnected schemes,
nonreduced rings, variable ranks on different opens and arbitrary further base changes
were checked against the argument. The identity test supplies local freeness of M;
the residue test fixes the first model-term rank; both are necessary.

`lem-sc-picard-rank-match-derived-truncation-data` is the geometric dictionary for
Stacks 0BDP's second and third paragraphs, 0B91(2), and the canonical mate in 08HY.
It leaves the general matrix calculation to the other node. Performed searches found
only generic exact-functor and degree-zero right-derived comparisons; the existing
canonical mate-square module is cited in its plan. The empty-fibre and rank-zero cases
are addressed above; either F=E or F=dual E has the same finite locally free rank.
For empty T or test schemes there is no point to check. All choices are existential
witnesses in theorem statements, and neither new module introduces definitions.

There are no change records or forced adaptations because existing interfaces did not change.

## Second reading by F4

1. **Unchanged interface — pass.** Compared the main module with the repository
   using `diff -u`; the only Lean changes are two plain proof imports and the
   replacement proof. Its theorem signature is byte-for-byte unchanged, as checked
   independently against both the original file and the node's `lean.statement`.
   Neither helper module exists in the repository. There are no new definitions,
   forced adaptations, target changes, or undeclared signature changes.
2. **Kernel proof and axioms — pass as a decomposition.** Compiled all three modules
   in import order with `lcompile.py --all`: no errors or warnings. Separate scratch
   copies with `#print axioms` for all three declarations report exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The only two literal `sorry`s
   delivered are the reported named helper theorems. No forbidden declaration or
   hollow definition occurs. The choices in the main theorem eliminate existential
   witnesses inside a proposition proof; they define no exported data. The stalk
   functor sends the exact comparison equation to the displayed equation of maps;
   two surjective lifts and injectivity of the target comparison prove the original
   stalk map surjective.
3. **Split statements — pass.** Read both complete proof docstrings, their nodes,
   the existing perfect residue-model and universal-lowest-cohomology declarations,
   flat-complex pullback, affine-map representative, perfect direct-image base change,
   and the canonical degree-zero mate/unit modules. Independently checked the source
   arguments at Stacks [0BDL](https://stacks.math.columbia.edu/tag/0BDL),
   [0BDP](https://stacks.math.columbia.edu/tag/0BDP),
   [0B91](https://stacks.math.columbia.edu/tag/0B91), and
   [0EWY](https://stacks.math.columbia.edu/tag/0EWY).
   The general helper is about a supplied arrow, with no Picard geometry or ordinary
   comparison in its statement. In a residue model the negative terms vanish and
   the first term has rank r. The identity test gives an injective square inclusion
   of H0 into that term; zero dual cokernel makes each coordinate of d0 vanish even
   over a nonreduced ring. An affine chain-map representative of the given arrow
   then has invertible degree-zero component, which remains invertible on pullback.
   The geometric helper supplies a perfect derived image, universal rank charts and
   the canonical square, and asserts no invertibility of the map needing the matrix
   calculation. Proper flat finite presentation makes the fibre-image locus both
   open and closed. Over its complement the derived image is zero; over its image
   rank comparison with E fixes the rank of every further test. Empty bases, empty
   fibres, rank zero, disconnected bases and F equal to the dual cause no exception.
   Fresh LeanFinder, Loogle and grep queries used truncation/singleFunctor and
   direct-image-unit terminology; results are generic truncation/adjunction tools
   and the singleFunctor-homology isomorphism, not either complete helper. Additional
   `rg` searches of Sheaf and WeilConjectures found the object-only universal
   lowest-cohomology theorem and canonical mate square already cited by the report;
   neither determines the required invertibility on its own. Neither remaining hole
   can be closed by a short application of these existing declarations.
4. **Top-down route and pruning — pass after report repair.** The main proof uses
   exactly the two intermediate steps and the elementary stalk transport. All
   original public imports supply signature notation or types (in particular
   FlatPullbackStalk defines `Hom.stalkLinearMap`); both new imports are plain.
   The helpers' public imports likewise supply their statements. No unrelated
   proof-only public import was added. Enumerated all seven old direct dependencies
   under `No longer needed`, distinguishing the representing-locus route removed
   from dependencies retained indirectly in the helpers. Read the unit record
   `sk-prop-av-cube`: its statement and sole step have empty `realized` lists, and
   neither is changed or bypassed. No whole-target-closure pruning is claimed.
5. **DAG/Lean agreement — pass.** Checked all three recorded Lean signatures verbatim,
   and checked every `proof_deps` equals the union of its proof steps' `uses`.
   The main node's three steps match the actual compiled proof. Both new nodes have
   source, natural-language argument, dependency/search records, status, creation
   provenance, blueprint ancestor, chapter/unit and complete Lean records. The
   square-injective-free-map dependency is an existing Mathlib composite leaf,
   not a missing declaration to restate. The old node changes only the allowed
   proof fields and keeps its original statement and provenance.

Second reading changed only this report: completed the removed-direct-dependency
inventory and recorded the independent review. No Lean proof, signature or node
needed repair. One original hole is closed and two intermediate holes are added;
this remains a decomposition with net holes closed minus added equal to -1 before
any whole-closure pruning, not a claim of a completed axiom-free theorem.
