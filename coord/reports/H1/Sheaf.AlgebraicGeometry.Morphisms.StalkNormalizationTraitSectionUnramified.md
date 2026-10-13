## What changed

The signature of `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_unramified`
is unchanged. Its proof now combines two independent local conditions using Mathlib's
`Algebra.FormallyUnramified.of_map_maximalIdeal`, then spreads the resulting stalk property
to an open source neighbourhood.

Three new modules are imported privately for this proof: `StalkNormalizationTraitSectionMaximalIdeal`,
`StalkNormalizationTraitSectionResidueSeparable`, and `FormallyUnramifiedStalkNeighbourhood`
(all under `Sheaf.AlgebraicGeometry.Morphisms`). The last module is proved entirely from Mathlib,
including a private affine-stalk localization helper. No existing definitions or interfaces change.
All four modules compile together without warnings through lcompile.py.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_unramified`
(node `lem-sbc-stalk-normalization-trait-section-unramified`). This is a decomposition,
not a proof independent of new sorries: one upper hole is closed and two lower holes are added.

Also proved, with no sorry:
`AlgebraicGeometry.FormallyUnramified.exists_neighbourhood_of_stalkMap`
(node `lem-sbc-formally-unramified-stalk-neighbourhood`). Its private affine helper is proved too.

The delivery leaves exactly two sorries, each in its own new module:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_maximalIdeal`
  (`lem-sbc-stalk-normalization-trait-section-maximal-ideal`). This is only the maximal-ideal
  generation part of the local unramifiedness criterion.
- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_residue_separable`
  (`lem-sbc-stalk-normalization-trait-section-residue-separable`). This is only residue
  separability and does not assume the rational generic section point.

The two local conclusions are strictly separate parts of the criterion: maximal-ideal generation
alone allows purely inseparable field extensions, while separable residue extensions alone allow
ramified DVR extensions. Neither states formal unramifiedness or the requested open neighbourhood.
Their docstrings give the complete tame-chart argument and source.

Edge checks: an empty normalization fibre makes both claims vacuous; the trivial group and
exponent-one charts give identity stalk and residue maps; disconnected covers are handled
componentwise via stabilizers. Residue separability needs tameness but not generic splitting.
The maximal-ideal calculation uses splitting to rule out every exponent greater than one by
an integral valuation equation. The general neighbourhood lemma assumes locally finite type,
which supplies finite generation of differentials; it assumes neither Noetherianity nor flatness.

## No longer needed

No existing dependency node or module is pruned. Removed the redundant direct public import
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` from the new
`FormallyUnramifiedStalkNeighbourhood` module: its remaining FormallyUnramified import already
exports finite-type morphisms. The original node has no proof dependencies to prune. The original
public imports support its unchanged statement and remain. Each of the three new private imports
is used explicitly. No blueprint unit or step is bypassed; the unit's realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

The node's single non-elementary proof step has no named dependencies: there were no stated
lemmas from which its tame normalization argument could simply be assembled. This delivery
makes the two local algebra conclusions explicit and proves their assembly and openness step.
No false statement or forced adaptation was found. LeanSearch was unavailable; the actual
failed queries are recorded alongside successful LeanFinder, Loogle and source-grep searches.
The Stacks source was checked online at Tags 0EYH, 0EYI, 0EYJ and 02GF because the local
literature checkout is absent on this machine.

## New nodes

`lem-sbc-stalk-normalization-trait-section-maximal-ideal`: maximal-ideal generation from the
split trait valuation calculation of Tag 0EYI(2); one named sorry in its own module.

`lem-sbc-stalk-normalization-trait-section-residue-separable`: residue separability from the
tame charts of Tag 0EYH, without the rational-point assumption; one named sorry in its own module.

`lem-sbc-formally-unramified-stalk-neighbourhood`: the general source-neighbourhood lemma from
Tag 02GF, fully proved using Mathlib's unramified locus and localization machinery.

No change records are needed: no existing statement, definition or public import was changed.


## Second reading by H1

1. **Existing interface unchanged: pass.** Compared the delivered item with the repository by
   `diff -u`. Its only changes are three private imports and the replacement of `by sorry` by
   a proof. The entire existing declaration signature and docstring are byte-for-byte identical;
   no existing definition changes and no change record is required. The three other modules are
   new, so they do not alter an existing interface.
2. **Proof and axioms: pass as a decomposition.** Compiled all four files in import order with
   `lcompile.py`, without errors or warnings. Scratch-copy `#print axioms` checks show only
   `propext`, `Classical.choice`, `Quot.sound` for the neighbourhood theorem and its private
   affine-stalk helper. The item and the two named lower holes additionally have `sorryAx`.
   Exactly two textual sorries remain, each the complete proof of its reported public theorem;
   there are no definitions with postponed data and no forbidden declarations. The original
   hole is closed syntactically, but is not an axiom-free proof: one hole closed, two holes added.
3. **New statements: pass.** Read each hypothesis and conclusion of both new local algebra
   statements and checked them against Stacks Tags 0EYH, 0EYI(2), and the trait argument of 0EYJ.
   The maximal-ideal claim retains generic splitting; the residue-separability claim deliberately
   omits it, because tame charts already give separability. In a chart over the special divisor,
   the residue field is unchanged; the etale chart extensions are separable, so the conclusion
   descends. Generic splitting forces each chart exponent to be one by the uniformizer valuation,
   giving maximal-ideal generation. Trivial groups and exponent-one charts reduce to identity
   maps; an empty fibre is vacuous. Conversely a ramified tame DVR map need not generate the
   maximal ideal, and a purely inseparable field extension has zero maximal ideals without being
   separable: these are independent, strictly partial conclusions, not renamed copies of the item.
   Their source-and-proof docstrings and individual nodes are present. Repeated searches with
   different words via msearch.py (LeanFinder: tame special-fibre residue separability; Loogle:
   formally unramified stalks; grep: tame, ramificationIndex, inertia), and rg over both library
   roots. The hits give the local criterion and the forward stalk implication, not either new
   tame-normalization claim or the converse neighbourhood theorem. Neither lower hole has a
   short proof from the available declarations.
4. **Route and pruning: pass.** Read the item's proof top down. It supplies the finite-type
   stalk instance, combines maximal-ideal equality and residue separability with Mathlib's
   `Algebra.FormallyUnramified.of_map_maximalIdeal`, then uses the proved neighbourhood theorem.
   The latter reduces to affine stalk localizations and
   `Algebra.exists_formallyUnramified_of_isUnramifiedAt`; the source basic-open restriction is
   identified with the localization before applying the affine criterion. All three private
   imports are used. The old node has no proof dependencies, hence none is omitted from
   `No longer needed`. Read `dag/units/sk-prop-input-spreading.json`: its realized lists are
   empty and the trait/section steps still use tame charts and the split-section valuation test;
   this delivery does not replace that route. Removed one redundant direct import in the new
   neighbourhood module, and verified that its signature and proof still compile.
5. **DAG and Lean: pass.** Each of the four lean.statement strings occurs verbatim in its
   module, every proof_deps list equals the union of its steps' uses, and all nodes retain the
   item's chapter and unit. The existing node differs only in proof, proof_deps, proof_origin.
   Its three new dependencies are precisely the declarations the new Lean proof invokes. New
   records contain the source, origin, searches, creation record, blueprint ancestry, and Lean
   module/file/declaration/statement fields. The two unfinished nodes record exactly their
   docstring arguments; the neighbourhood node records its proved affine localization route.

Second reading changed only the new modules' headers (added missing module-level source and
blueprint references), removed the redundant FiniteType import from the new neighbourhood
module, and expanded this report. No mathematical statements or proof bodies were changed.
