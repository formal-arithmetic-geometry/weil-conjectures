## What changed

Proved `AlgebraicGeometry.Etale.RawRestrictedComparison.derivedSectionPullback_zero`
with its original signature and visibility. Added the proof-only import
`Sheaf.AlgebraicGeometry.DerivedSectionSingleUnit`.

Added two proved modules. `Sheaf.AlgebraicGeometry.DerivedSectionSingleUnit` computes
unit–Leray pullback on a single sheaf before taking homology, using the defining derived
adjunction and composite-unit equations. `Sheaf.CategoryTheory.RightDerivedSingleZeroUnit`
constructs the actual single-object right-derived unit and proves its degree-zero normalization
from the already proved
`CategoryTheory.Functor.rightDerivedPlusSingleUnitHomology_comp_comparison`.
The unbounded transport calculation follows the proved private calculation in
`Sheaf.AlgebraicGeometry.RawRestrictedSectionsUnitZero`; the unit–Leray calculation follows
proved private calculations in `Sheaf.Paper.EtaleKInjectiveUnitLeray`.
These calculations are used locally because their public geometric theorems impose
irrelevant representative or K-injectivity hypotheses.

The target combines the two proved calculations by a categorical cancellation lemma and
naturality along the restriction/single isomorphism `b`. No restriction triangle,
coefficient morphism, or invertibility of ordinary section pullback is used.
The existing node's proof and proof dependencies now describe this Lean argument.
Second reading retained the helper's statement-bound local expressions with
`extract_lets`, delaying expansion of τ to its use in the proof, after a 60-second
compile timeout. The revised helper compiles within the limit. In the original item proof, second
reading also removed eager expansion of the helper equation, used naturality of
`whiskerRight τ H` directly, and replaced the final normalization rewrite and
`zeroIso` simplification by congruence, transitivity and associativity.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.RawRestrictedComparison.derivedSectionPullback_zero`
(`lem-sbc-derived-section-pullback-zero`).

Added and proved:
`AlgebraicGeometry.Etale.RawRestrictedComparison.derivedSectionPullback_single_unit`
(`lem-sbc-derived-section-single-unit`) and
`CategoryTheory.Functor.rightDerivedSingleUnit_zero`
(`lem-sbc-right-derived-single-zero-unit`).
`CategoryTheory.Functor.rightDerivedSingleUnit` is a real composite of existing maps;
it has no postponed data or proof.

No `sorry` remains in any delivered module, and no holes were added. This is a proof,
not a decomposition into unproved statements. The auxiliary statements cover zero objects,
the zero functor, zero sheaves and empty schemes without added assumptions.

## No longer needed

No module was pruned and no existing import was removed. The old direct proof-dependency
edges `def-weil-pbc-inverse-image` and
`prop-weil-pbc-derived-inverse-image-adjunction` are replaced at the item by
`lem-sbc-derived-section-single-unit`, which still uses both nodes. These dependencies
remain necessary transitively; they are not pruning claims.
`def-sbc-raw-restricted-cohomology-comparison-map` remains necessary for the original
statement and its `zeroIso` definition. No existing node or module is claimed pruned.
The proof does not import `Sheaf.Paper.EtaleKInjectiveUnitLeray` or
`Sheaf.AlgebraicGeometry.RawRestrictedSectionsUnitZero`: their unrelated public constructions
are not needed; only their proved generic calculations are reused.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. Second reading found intermittent
60-second compile timeouts and shortened the generated equality proofs, retaining
the statements, constructions and argument. The node's resolution-level plan can be
shortened by using the existing proved single-unit normalization, transporting it to the
unbounded functor, and then applying naturality. The unit's prescribed route is unchanged.
LeanSearch was unavailable; semantic/type searches and Mathlib/library source searches
were completed. No existing signatures, definitions or other held modules were adapted.

## New nodes

`lem-sbc-derived-section-single-unit` records the proved pre-homology unit–Leray square
on arbitrary single sheaves. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedSectionSingleUnit.lean`.

`lem-sbc-right-derived-single-zero-unit` records the real single-unit construction and
its proved degree-zero normalization. Its module is
`lean/Sheaf/CategoryTheory/RightDerivedSingleZeroUnit.lean`. The substantive normalization
uses the existing proved node `lem-sbc-right-derived-single-unit-homology-comparison`.
Both nodes inherit the item's chapter and unit. No change record is needed.

## Second reading by W4

1. **Interfaces — pass.** Read the three delivered modules and diffed the original
   `DerivedSectionPullbackZero.lean` against the repository. The existing theorem's
   signature, universe, visibility and docstring are byte for byte unchanged. Its
   only import addition is plain `import DerivedSectionSingleUnit`, for the proof.
   The other two modules and their public declarations are new. No existing
   definition, statement or other group's module was adapted; no change record is needed.

2. **Proof and trust — pass.** Compiled all three modules in import order through
   `lcompile.py --all`, with no errors or warnings. Read every proof and scanned the
   delivered sources: no `sorry`, forbidden axiom or implementation escape is present.
   Scratch copies with `#print axioms` confirm that `derivedSectionPullback_zero`,
   `derivedSectionPullback_single_unit`, `rightDerivedSingleUnit_zero`, and the
   construction `rightDerivedSingleUnit` use only `propext`, `Classical.choice`,
   and `Quot.sound`; none uses `sorryAx`. The construction is Q of the inverse
   single-complex comparison followed by the existing localization unit, with no
   arbitrary witness chosen from an unproved existence theorem. The delivery closes
   the one original hole and adds zero holes.

3. **Auxiliary statements — pass.** There are two newly proved auxiliary statements
   and no unproved split-off statements. Read [07A6](https://stacks.math.columbia.edu/tag/07A6)
   for derived adjunction and [0156](https://stacks.math.columbia.edu/tag/0156),
   Lemma 13.20.4(2), for the left-exact zeroth normalization. The single-unit equation
   uses the derived-unit factorization and the composite Leray unit, then chain-map
   extensionality from a single complex; it requires neither injectivity of the
   sheaf nor invertibility of section pullback. The normalization transports the
   already proved `rightDerivedPlusSingleUnitHomology_comp_comparison` and cancels
   `toRightDerivedZero` with `rightDerivedZeroIsoSelf`. Zero objects, the zero functor,
   zero sheaves, identity morphisms and empty schemes introduce no extra conditions:
   the equalities reduce to zero maps or canonical comparison identities. Repeat
   Loogle search `"rightDerived", "unit"`, LeanFinder search for the zeroth cohomology
   of the canonical sheaf-to-derived-sections map, and Mathlib/library grep for
   homology/unit and single/unit formulas found the used building blocks, but no
   public theorem giving either complete new formula. The matching existing
   unbounded transport and unit–Leray calculations are private, so cannot be
   imported as public lemmas. The new lemmas express separate parts of the argument,
   not a renamed unproved copy of the item.

4. **Route and imports — pass.** Read the proof from the item downward: the helper
   `map_zero_comparison` cancels H⁰ of the source unit, whose invertibility follows
   from its normalization; it never cancels ordinary section pullback. Naturality
   of τ along `b.hom` then gives precisely the definition of `zeroIso`. The new
   normalization imports the existing bounded-below theorem for proof only; its
   public imports supply the constructions in its public signatures. The geometric
   helper's public imports supply the actual unit construction and global-sections
   data in its signature. No dispensable import or shorter public route was found.
   The old inverse-image and derived-adjunction edges are retained through the
   single-unit helper, as clarified under No longer needed; no module is pruned.
   Read `dag/units/sk-lem-failure-field.json`: its statement and sole step are
   unchanged, and its existing `realized` lists are empty. This item is a lower
   degree-zero comparison, not the unit's key statement; the delivery neither
   replaces a fixed unit step nor claims to complete those existing bindings.

5. **DAG — pass.** Read all three node records and their dependency declarations.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   The union of each node's step uses equals its `proof_deps`. The new records
   match their Lean declarations and carry the source, complete proof steps,
   search records, W4 creation record, blueprint ancestor, chapter and unit.
   The item's two steps describe the single-unit normalization/cancellation and
   naturality transport actually written in Lean. Both new statements are proved,
   and their dependency on the existing bounded-below comparison is explicit.

Second-reading changes: added the source and construction APIs to the new
`rightDerivedSingleUnit` docstring; clarified the two old direct dependency edges
that now occur through the single-unit helper; appended this independent reading.
Also replaced eager initial expansion in `derivedSectionPullback_single_unit` by
`extract_lets τ L F R` and unfolded τ only at the component calculation. This
addresses the repeated 60-second timeout without splitting a file or statement.
The revised module compiles cleanly (51.9 seconds including launcher overhead).
In `derivedSectionPullback_zero`, removed eager expansion of the helper equation;
used naturality of `whiskerRight τ H` instead of applying H and simplifying its
map of a naturality equation; and used direct congruence/transitivity/associativity
in place of the final normalization rewrite and expansion of `zeroIso`. The final
item module compiles cleanly in 54.2 seconds including launcher overhead.
No signature, definition body, node or import changed.
