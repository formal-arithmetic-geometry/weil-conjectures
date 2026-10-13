## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.open_union_restriction_comparison_diagram`
by assembly of proved direct comparison data and the supplied-data overlap-coherence lemma.
The original theorem signature is byte-identical. The main proof preserves the three
localization witnesses by `Exists.imp` and combines the proved equivalences and direct
comparisons with the coherence witnesses. The remaining lemma constructs the common `qI`
by the functor associator, whiskering the supplied direct intersection comparison, and
composing with the canonical ambient restriction comparison.

Added `OpenUnionRestrictionComparisonData`, with a complete proof of the three derived
localizations, equivalences, and direct comparison isomorphisms. Its proved private helpers
transport local w-smallness along an exact equivalence, compare overlap restriction with
Mathlib's scheme restriction functor, and construct the module equivalence of `Opens.isoOfLE`.
These are actual constructions, with no new unproved data definitions.

Added `OpenUnionRestrictionComparisonCoherence`, isolating descent of the two overlap comparison isomorphisms. The statement takes the direct equivalences and
comparisons as inputs, and constructs only the overlap comparisons, ambient intersection comparison, and pasting laws.
It takes the already proved direct comparison data as inputs and supplies both overlap
pasting identities with the same intersection comparison.

The proof inlines localization witnesses with `letI` to match the dependent statement.
A documented local style-linter option permits this inlining. A local unused-variable
linter option preserves the inherited, unused JW and JV statement bindings unchanged.
No global attributes change.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.open_union_restriction_comparison_diagram`
(node `lem-sc-open-union-restriction-comparison-diagram`).

Proved the new theorem
`AlgebraicGeometry.Scheme.open_union_restriction_comparison_data`
(node `lem-sc-open-union-restriction-comparison-data`) without a `sorry`.

Added one hole:
`AlgebraicGeometry.Scheme.open_union_restriction_comparison_coherence`
(node `lem-sc-open-union-restriction-comparison-coherence`). No holes remain in the item's module.
This is a decomposition, not an independent proof of the original theorem: one original
hole is closed and one strictly smaller overlap-coherence hole is added. The direct
data construction is proved. Inherited dependencies may still use `sorryAx`.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.DerivedOpenLocalization` and
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`.
The former is still needed through the proved comparison-data construction.

The old direct proof dependency `def-pc-derived-open-restriction-maps` remains a
statement dependency and is retained through the public import and both new nodes.
The old `lem-pc-derived-open-localization-universe` remains needed through the data node.
Only the following old dependency is unused by the new argument.

The proof no longer needs
`lem-pc-open-derived-localization-adjunction` or its module
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`: localization transport is
constructed directly using the exact module equivalence and local w-smallness. No
right adjoint to direct image is used. The derived-open-localization universe lemma
and the canonical restriction definitions remain needed. This pruning is relative to
this item; other routes may still reach the removed module.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt omitted the required LeanSearch search records. Ran that search
and recorded its actual service-unavailable result in both new nodes. The earlier
LeanFinder, Loogle, and source grep records are backed by the sandbox search log.

The original proof dependencies do not state the comparison data or threefold restriction
coherence. The two new nodes isolate that missing content instead of treating an unproved
dependency as unavailable.

Stacks Tag 08BW (`cohomology.tex`, `lemma-mayer-vietoris-hom`) states the derived Hom
Mayer-Vietoris sequence and invokes the extension-by-zero adjunction. It does not literally
state this explicit comparison diagram. The new proofs and nodes mark the comparison
argument as an agent-written expansion using Mathlib's `overFunctorEquiv`,
`overMapCompOverEquiv`, `restrictFunctorComp`, and `restrictFunctorCongr`.
Tag 08BT (`lemma-adjoint-lower-shriek-restrict`) supplies the derived restriction adjunction.
Both source passages were read, including their TeX labels.

Edge cases checked: empty opens, disjoint W and V, repeated opens, and the whole open
use the same canonical scheme isomorphism and localization transport. The coherence
lemma allows arbitrary comparison automorphisms: precomposition with open restriction
is fully faithful on functor categories because restriction is a localization, so those
comparisons descend uniquely. It requires no quasi-compactness, quasi-separatedness,
nonempty points, or morphism-compatibility hypothesis. The unit record has no realized
nodes at this level; the finite-duality/open-gluing route above this node is retained.

## New nodes

`lem-sc-open-union-restriction-comparison-data` records the proved direct comparison
construction, with the canonical restriction definition and derived-open-localization
universe lemma as dependencies.

`lem-sc-open-union-restriction-comparison-coherence` records the remaining two-arm overlap coherence
argument, with exact extension by zero, restriction of extension by zero, and the
canonical restriction definition as dependencies. Its complete proof in words explains
localization descent and the underived-to-derived coherence calculation.

No definition, statement, or importer-visible attribute changes; no change record is needed.

The earlier generic single-chain formulation was replaced by the two-arm supplied-data
coherence interface to reduce repeated elaboration of concrete derived categories. The
first geometric construction remains completely proved; the remaining statement is
strictly the second coherence step, not the original existential construction renamed.


## Second reading by Y3

1. Compared the existing module with the repository using `diff -u` and checked the
   declaration text against the node's verbatim Lean statement. Verdict: the sole
   existing signature is byte-identical; changes are proof-only imports, local options,
   and proof. No definition, public import, or target statement changes. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`.
2. Compiled all three modules with `lcompile.py --all`: no errors or warnings.
   Searched all delivered Lean for prohibited declarations and holes: precisely one
   `sorry`, in the named coherence theorem, and none in definitions. A scratch
   `#print axioms` check gives only `propext`, `Classical.choice`, and `Quot.sound`
   for the data theorem; the coherence and assembled diagram additionally use `sorryAx`.
   The private definitions explicitly construct equivalences and localizations; none
   selects arbitrary data from an unproved mere-existence theorem. Verdict: valid
   decomposition, one original hole closed and one smaller hole added, net zero holes.
3. Read the supplied-data coherence statement, docstring, node, canonical restriction
   definitions, and the source passages at Tags 08BT/08BW. It assumes direct comparisons
   rather than reconstructing the original existential data. For either arm, full
   faithfulness of precomposition with restriction descends the isomorphism obtained
   from qW (respectively qV), qIY and canonical composition. This permits arbitrary
   comparison automorphisms; no unmentioned compatibility is needed. Empty, disjoint,
   repeated and total opens obey the same argument. The shared qI is the whiskered
   qIY followed by ambient composition, so both equations agree. Verdict: true and
   strictly a remaining part of the argument, not a restatement. Independent searches
   used LeanFinder for localization/open-immersion precomposition, Loogle for
   `Localization.fullyFaithfulWhiskeringLeft`, msearch grep for preimageIso/restriction
   composition/isoOfLE, and repository rg for overlap coherence. Results provide
   ingredients, not an existing theorem with this statement. No quick complete proof
   of its derived threefold coherence calculation was found.
4. Reviewed the shortest-route data proof: Mathlib scheme isomorphisms, exact
   equivalence transport and localization size transport suffice; the old
   direct-image localization adjunction is unnecessary. All new proof imports remain
   private; the remaining proof plan uses the adjunction/localization ingredients.
   The No longer needed section accounts for all three old proof dependencies:
   restriction definitions and localization universe lemma remain, while the old
   localization-adjunction node is pruned from this route. The unit record
   `sk-thm-picard-duality` has `realized.statement = []` and `realized.steps = [[]]`;
   nothing in the unit or its finite-duality/open-gluing route is altered. Verdict: pass.
5. Checked every node signature against Lean and every proof-dependency list against
   its steps. New nodes include source, proof in words, search records, origin,
   creation, blueprint, chapter, unit and Lean record. Verdict: pass after repairing
   stale single-chain terminology in the original node and undefined PB/SA/qB/t
   placeholders in the coherence node's proof description.

Second-reading changes: corrected the two DAG proof descriptions; clarified the
canonical unit/stalk justification in the coherence docstring and joined an awkward
line break; added the precise Mathlib calculus-of-fractions import containing
`Adjunction.isLocalization_rightAdjoint'` used by that proof plan; completed the
old-dependency accounting above. No theorem signature or executable proof changed.
