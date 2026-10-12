## What changed

Replaced both original sorries in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` with compiling proofs.
All existing signatures, definitions, docstrings, and public imports are unchanged.
Added two proved private helpers, transferring terminal sections invariance first from
sets to abelian groups and then from abelian groups to modules. The module/abelian
inverse-image comparison used here is already proved in the library.

The chart theorem transports the terminal module-unit isomorphism along a chart
restriction arrow isomorphism. The derived theorem explicitly constructs the source
and target homology/single-complex comparisons, verifies their commuting square by
expanding `rightDerivedBaseChange_app`, and composes it with the degree-zero
augmentation square. It uses the already proved
`Etale.baseChange_eq_derivedBaseChangeMapPlus`, rather than a new termwise exchange
statement. These are reductions with real composition and cancellation proofs.

Added proof-only imports of `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`,
`Sheaf.CategoryTheory.RightDerivedBaseChangeZeroUnit`,
`Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres`,
`Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`, and
`Sheaf.AlgebraicGeometry.EtaleChartSectionsArrowComparison`.
Added the two new Sheaf modules and four DAG records named below.

Validation: all three sandbox modules compile together through `lcompile.py --all`.
The source module compiles without warnings. A declaration/interface comparison
confirms that only the two original public theorem bodies changed; no existing public
signature or definition changed. Import-direction checks accept both new imports.
The delivery dry run is the final validation.

## Proved and sorry left

Both original declarations now have complete Lean proofs:

- `AlgebraicGeometry.Etale.isIso_upperStarSectionsMap`:
  `lem-sbc-module-chart-sections-flat-connected`.
- `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_zero`:
  `lem-sbc-base-change-homology-zero-underived`.

No sorry remains in the item. The delivery adds exactly two named sorries:

- `AlgebraicGeometry.Etale.nonempty_etaleChartSections_arrowIso`, in
  `Sheaf.AlgebraicGeometry.EtaleChartSectionsArrowComparison`:
  `lem-sbc-etale-chart-sections-arrow-comparison`.
- `CategoryTheory.Functor.rightDerivedBaseChange_zero_unit`, in
  `Sheaf.CategoryTheory.RightDerivedBaseChangeZeroUnit`:
  `lem-sbc-right-derived-base-change-zero-unit`.

The chart reduction also uses the existing sorried declarations
`AlgebraicGeometry.etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres`
and `AlgebraicGeometry.etaleInverseImageAlgebraicStructures`, through their existing
nodes. Thus this delivery reduces the item; it does not claim its transitive closure
is free of sorries. Each new sorry is strictly part of the argument: the first has no
flatness or connectedness hypothesis and proves a restriction comparison; the second
is an equation for arbitrary functors and augmentations, not the original etale arrow
isomorphism under another name.

Edge cases checked mathematically before stating the lemmas: empty etale charts and
the zero coefficient ring still give the usual terminal sections comparisons;
identity morphisms give adjunction-unit identities. The chart comparison is independent
of surjectivity. The derived equation specializes to the natural transformation itself
for identity functors, and to zero composites for zero functors. The existing flat
connected-fibre theorem supplies its own connected geometric-fibre condition, obtained
in Lean from `GeometricallyConnected`.

## No longer needed

No original import is removed, and no module is claimed to be globally prunable:
the unchanged normal-form, chartwise-gluing, and smooth-specialization route is retained.

The present derived proof does not import
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise` or use the sorried node
`lem-weil-pbc-derived-exchange-termwise`: the source-library comparison is already
proved. This avoids adding that planned dependency to this item, but does not claim
other targets no longer need it.

The chart proof does not import `Sheaf.Paper.EtaleRestrictionPullbackUnit`
(`lem-weil-pbc-etale-restriction-pullback-unit`), whose chart morphism is Cartesian;
the item allows arbitrary chart morphisms. The new comparison isolates this generality
and retains the existing localization/composition lemmas as its proof dependencies.

Removed redundant imports from the new chart module during development:
`Mathlib.Algebra.Category.ModuleCat.AB` (already public through ConcreteCoefficients),
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
The statement only needs UpperLowerStar.Defs and ConcreteCoefficients. Localization
and composition remain the planned proof ingredients of its new node, rather than
unused imports in its current statement module.

## Where the brief, the DAG or earlier work was wrong

No DAG node records this module in `lean.module`. Its two sorried declarations have no
`(blueprint: ...)` docstring tags. The chart docstring identifies unit `sk-prop-deg0`
Step 2, and the surrounding theorem identifies
`sbc-lem-degree-zero-flat-base-change`. The four new records explicitly attach the
two proved declarations and the two remaining parts of their arguments.

The existing blueprint degree-zero node's one-step equalizer sketch is not a faithful
proof of these declarations: in particular, connected components are not geometric
points in general. I did not change that statement or invent an equalizer proof.
The existing source module already contains the correct normal-form, sections,
and sheaf-gluing assembly following Stacks Tags 0EZX and 0EYS. This delivery fills its
two gaps and leaves the unit's steps intact.

LeanSearch was attempted for both new comparison lemmas but returned an internal
server error. The search records explicitly say unavailable; they make no absence
claim from that service. Loogle/LeanFinder and direct source searches located the
existing isomorphisms and ruled out an exact existing comparison declaration.

Sources checked: Stacks https://stacks.math.columbia.edu/tag/0EZX, including footnote 1,
and https://stacks.math.columbia.edu/tag/05TD, part (3). The generic augmentation
compatibility is derived from the source-library defining base-change unit equation;
Tag 05TD supplies the interpretation of the degree-zero augmentation.
No statement or definition correction, and hence no change record, is needed.

## New nodes

`lem-sbc-etale-chart-sections-arrow-comparison` is the remaining restriction/composition
comparison for arbitrary charts, without flatness or connectedness. Its new module
contains one public theorem with its source and four-step proof in words.

`lem-sbc-right-derived-base-change-zero-unit` is the remaining generic degree-zero
augmentation equation. Its module contains one public theorem with its source and
three-step proof in words. Its proof dependencies are existing derived-comparison and
homology nodes, not a new copy of the etale degree-zero arrow-isomorphism statement.

`lem-sbc-module-chart-sections-flat-connected` attaches the proved original chart
theorem and records its actual set-to-abelian-to-module and chart-transport argument.
It records the sections part of `sk-prop-deg0` Step 2; the existing unit record has
empty `realized` fields and this delivery does not modify that record.

`lem-sbc-base-change-homology-zero-underived` attaches the proved original degree-zero
arrow comparison and records both commuting squares and their composition. No new
sorry is attached to this node. All four records lie in `sec-smooth-base-change`,
unit `sk-prop-deg0`, and carry exact parsed Lean signatures and search records.


## Second reading by W2

1. Interface preservation — PASS. Read the full diff against the repository and
   checked the declaration table with `stage3_delivery.diff_module`: no existing
   statement changed, no existing definition changed, both original sorry bodies
   were replaced, and all existing public imports and docstrings are unchanged.
   The five added imports in the item are proof-only. The two new modules expose
   only their stated comparison theorems and publicly import their signature needs.

2. Proof and trust — PASS as a reduction. Independently compiled all three files
   with `lcompile.py --all`: no errors or warnings. A scratch copy with `#print axioms`
   checked both original theorems, both private transfer helpers, and both split
   theorems: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` occur.
   The latter comes from the explicitly reported open intermediate theorems.
   Scanned all delivered Lean files: exactly the two named theorem sorries, no
   hollow definition or prohibited declaration. The scratch copy was removed.

3. Split statements — PASS. Read both signatures, their complete proof docstrings,
   and their nodes. The chart comparison follows restriction to the etale objects
   and inverse-image composition, for arbitrary chart arrows; it does not assume
   flatness, connectedness, or a Cartesian chart. Empty charts still give terminal
   module sections and the zero ring gives zero modules. For identity maps the
   comparison is adjunction coherence. The augmentation equation is obtained by
   applying H^0 to the defining derived-base-change unit equation and transporting
   through the named homology comparisons. Identity functors reduce it to `e`;
   zero functors reduce it to zero. Neither statement restates an original gap.
   Independently searched Loogle for `toRightDerivedZero`, LeanFinder for the
   chart/terminal-unit comparison, and `rg` in Sheaf, upstream, and Mathlib.
   Found the augmentation isomorphisms and restriction/composition ingredients,
   but no existing exact replacement for either split theorem. Checked Stacks
   0EZX including footnote 1, 0A3H, and 05TD (3). The remaining compatibility proofs
   require substantial comparison/coherence work, not a few-minute application.

4. Route and pruning — PASS, with a pre-existing metadata gap. Read the unit
   `sk-prop-deg0`: normal form, sections comparison on both sides, gluing, and
   smooth specialization remain in the unchanged surrounding Lean proofs. The
   new derived argument uses the proved source comparison and two actual commuting
   squares, not the sorried termwise exchange. The added proof imports each supply
   a used ingredient; the new statement modules have no proof-only public import.
   No old attached node existed for either gap, hence there is no old proof_deps
   list to subtract. The report explicitly names the avoided planned dependencies.
   The unit's `realized` arrays were already empty; preserving the route does not
   fill them. This should be repaired by the maintainer, whose unit file is outside
   this delivery's writable set. Corrected the report's wording to make this clear.

5. DAG agreement — PASS. Checked all four new records, their exact Lean signatures,
   chapter/unit, source, blueprint origin, creation fields, and searches. The chart
   proof's dependencies record the set-to-abelian-to-module transfer and chart
   transport. The degree-zero proof records the source-library comparison, homology
   isomorphisms, augmentation square, and arrow composition. The two unproved nodes
   describe precisely the two remaining intermediate equations/comparisons.
   Existing exact-homology and degree-zero-resolution dependencies are Mathlib
   leaves; the single-complex comparison has its existing upstream declaration.

Second reading changed only the report: added this independent review and corrected
its claim about the unit's `realized` metadata. No Lean proof or statement needed repair.
