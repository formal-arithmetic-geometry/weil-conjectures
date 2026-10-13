## What changed

Reduced `AlgebraicGeometry.Scheme.exists_boundedAbove_finiteFree_lift` without changing
its signature, visibility, universes, or public imports. Its body now packages the
pseudo-coherent object as quasi-coherent, applies the existing quasi-compact-open lift,
constructs the actual functor `tilde.functor Gamma(X) ⋙ Modules.restrictFunctor X.isoSpec.hom`,
and combines a local module comparison with a ring-level finite-free model.
The bound is proved by preservation of zero objects. Finite freeness is proved termwise
using an actual finite basis, `tildeFinsupp`, `mapFreeIso`, and `restrictUnitIso`.
The final derived isomorphism is the composition of the localized chain-map isomorphism,
the representation isomorphism, and the original open-lift isomorphism.

Added `Sheaf.AlgebraicGeometry.AffineOpenLocalizedModel` for the affine representative,
finite principal-open local models, and detection of localized quasi-isomorphisms.
Added `Sheaf.RingTheory.FiniteLocalizationFreeModel` for the descending finite-free
construction and denominator clearing. Neither statement asserts the original conclusion:
one constructs no finite-free replacement, and the other mentions no scheme, open,
sheafification, or original object E. Their proofs are postponed separately.
Updated the original DAG proof and proof dependencies to match this combination.

Compiled all three modules in dependency order with `lcompile.py --all`; each compiled
without errors or warnings, and the main module also compiled separately. No definitions
or target statements were changed, no forced adaptations were needed, and no data
was defined by choosing an arbitrary witness of a theorem left unproved.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_boundedAbove_finiteFree_lift`
(node `lem-sc-affine-pseudo-coherent-lift`). Its complete combining proof compiles.
There are no sorries left in the original module.

Added two holes, each a public named theorem in its own module, with source and complete
proof in words in its docstring and node:

- `DerivedCategory.exists_finite_localization_free_model`
  (`lem-sc-finite-localization-free-model`): the ring-level descending cone construction.
- `AlgebraicGeometry.Scheme.exists_affine_open_localized_model`
  (`lem-sc-affine-open-localized-model`): affine model and principal-open comparison.

This is a decomposition, not an axiom-free proof or a net hole reduction: one original
hole closed, two holes added. Existing dependencies may themselves still reach sorries.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentCriterion`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.RingTheory.ConePseudoCoherent`
- `Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent`

The direct node `lem-pc-affine-pseudo-coherent-criterion` is replaced by the narrower
`lem-pc-affine-pseudo-coherent-principal-model` comparison, which is what a cover of
an arbitrary open requires. The whole-affine criterion and its global unit-ideal
gluing argument are not needed on this branch.

For completeness, all old direct proof dependencies removed from the main node are
`lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-affine-pseudo-coherent-criterion`, `lem-sc-cone-pseudo-coherent`, and
`lem-sc-finite-cohomology`. The criterion is unused on this branch; the other three
are relocated below the new nodes.

The affine equivalence, cone pseudo-coherence and finite top cohomology remain necessary
below the two new nodes. Their imports are relocated to the respective intermediate
modules, not claimed as globally pruned. No assertion is made that a module has left
all targets' import closures. Quasi-coherence and quasi-compact-open lifting remain
explicit imports and steps; the original unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned denominator-clearing and infinite descending construction are substantial
formal steps, despite being marked elementary in the original DAG. They are now an
explicit ring-level item with the same source argument. Global finiteness of cone
cohomology cannot be assumed from finiteness only over the chosen open; existing
unit-ideal localization glue and global finite-cone model statements therefore cannot
be applied as they stand. The new ring statement deliberately has no unit-ideal premise.

The repository's literature checkout contains lists but no `perfect.tex`. Read the
Stacks Tag 08EE page directly at https://stacks.math.columbia.edu/tag/08EE, including
its cone induction and the denominator-clearing instruction. Searches of the library,
DAG, whole blueprint index, and Mathlib found no exact theorem for either new interface.
The LeanSearch endpoint returned Internal Server Error twice; this is recorded as
unavailable, not as evidence of absence. Loogle, LeanFinder and source grep ran and
are recorded in `searches.jsonl` and the new nodes.

Checked the empty open, empty family, zero ring, zero complex and rank-zero cases.
For the ring statement the empty family uses F=0. For the affine comparison the empty
open has zero restriction category, so detection is vacuous. For a nonempty cover the
powers used to clear denominators are units at the corresponding localization; the
finite direct sum covers every localization simultaneously. Bounds are arbitrary
integers, and no bounded-below assertion is made. An acyclic localized target admits
the zero model. If a localization element is a unit, its condition reduces to the
usual global pseudo-coherent finite-free model. No source statement was weakened.

## New nodes

`lem-sc-finite-localization-free-model` records the algebraic construction from steps
3–4 of Tag 08EE. It uses the existing cone pseudo-coherence and finite top-cohomology
statements to make localized obstructions finite, clears denominators into actual global
cycles, and retains already fixed degrees in the downward construction.
Its empty-family and zero-ring cases were checked. The statement is strictly the
ring construction part of the original argument.

`lem-sc-affine-open-localized-model` records the affine comparison from steps 2 and 5
of Tag 08EE, using Tag 06Z0 and the existing principal-open pseudo-coherent comparison.
It supplies a module representative and a finite local family, plus the fact that
quasi-isomorphisms at that family become invertible after restriction to U. It does
not construct a finite-free complex or conclude the original theorem. The canonical
sheafification functor is supplied explicitly and constrained by a natural isomorphism.

Both nodes have the original chapter and unit, the nearest blueprint ancestor
`lem-sc-finite-duality`, full statements and proof steps, verbatim Lean signatures,
and actual logged Mathlib searches. No change record is needed because no existing
statement, definition, or exported interface changed. The affine derived equivalence
remains a generic tool already used by the original route.

## Second reading by B2

1. Compared the delivered main module with the repository using `diff`, then checked
   its full parsed declaration statement. The existing signature is byte-for-byte
   identical, including all named arguments, universes and hypotheses; visibility
   and public imports are unchanged. The two additional modules are new. No
   definition, existing interface, target, or forced adaptation is changed. PASS.
2. Independently compiled all three modules in dependency order with `lcompile.py`.
   They compile without errors or warnings. Searched the delivered source for
   forbidden declarations and bypasses: none. Exactly two `sorry`s remain, each
   the entire proof of a public named theorem, and both are reported above. Scratch
   copies with `#print axioms` for all three declarations show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. No definition chooses an
   arbitrary witness from an unproved existence theorem: the `obtain` steps select
   witnesses only inside this existential theorem's proof. PASS as a decomposition,
   not an axiom-free proof.
3. Read both new signatures, docstring proofs, and nodes against Tag 08EE and the
   actual definitions of scheme and ring pseudo-coherence. The ring construction
   needs only finiteness at the selected localizations: multiplying cycle
   representatives by powers clears denominators and kills their differentials,
   without a unit-ideal assumption. The affine comparison provides no finite-free
   replacement and the ring lemma provides no scheme comparison, so neither
   restates the original item. Checked empty U, empty family, zero ring, nilpotent
   localization elements, rank zero, repeated elements, unit elements, and arbitrary
   integer bounds. For nilpotent elements the localized category is zero; repeated
   elements only repeat conditions. These cases introduce no missing hypothesis.
   Repeated searches with different wording using LeanFinder, Loogle, Mathlib grep,
   and `rg` over both source roots found no exact duplicate. In particular,
   `exists_finiteFree_model_of_finite_cones` requires global cone finiteness, and
   localization glue requires a unit-ideal family: neither applies here. The two
   remaining formalizations are substantial and could not be closed by a short
   application of an existing declaration. PASS.
4. Read the combining proof from its conclusion downward: zero preservation gives
   the upper bound, actual finite bases and the tilde/restriction free-module
   isomorphisms give each finite-free term, and the three composed derived
   isomorphisms give precisely the original restriction conclusion. Public imports
   supply signature material; the new comparison, ring construction, quasi-coherence
   and open-lift dependencies are plain proof imports. All four removed old direct
   proof dependencies are now explicitly listed under No longer needed. The affine
   equivalence, cone lemma and finite-cohomology lemma remain below the new nodes;
   no global pruning is claimed for them. The unit/chapter route is unchanged.
   `dag/units/sk-thm-picard-duality.json` already has empty realized entries
   (`statement: []`, `steps: [[]]`); that pre-existing bookkeeping gap is recorded
   here, and the delivery does not modify the unit or bypass its route. PASS for
   this delivery, with that pre-existing gap noted.
5. Compared the old and new item node: only `proof`, `proof_deps`, and
   `proof_origin` differ. The new dependency union matches the actual combining
   proof. All three recorded Lean statements match their declarations after
   whitespace normalization. Both new nodes have source, complete proof steps,
   statement and proof dependencies, search records, split status, creation and
   blueprint ancestry, original chapter/unit, and Lean records. PASS.

Second-reading changes: corrected the main module's historical lemma number to
36.13.3 (the stable source tag remains 08EE); clarified the ring docstring's initial
cutoff n=b+1 and the n-pseudo-coherence of the finite approximation required by the
cone lemma; explicitly enumerated all four removed old proof-dependency node ids;
added this independent review and its search records. No Lean statement or proof
body changed. Net holes remain one closed minus two added, namely -1.
