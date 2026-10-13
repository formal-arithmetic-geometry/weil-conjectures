## What changed

Replaced `AlgebraicGeometry.derived_open_union_ses_presentation`'s hole with a
construction from two strictly separate intermediate statements: exactness of
the fixed underived union complex, and comparison of the fixed open-image
complexes with arbitrary localized-site right adjoints. The original signature
and docstring are unchanged. All new imports in the item's module are proof-only.

The proof constructs the source library's functorial K-injective resolution of a
Mathlib localization preimage of E, localizes its actual quasi-isomorphism, builds
the concrete short complex, and constructs its middle-term comparison using
`Q.mapBiprod` and `biprod.mapIso`. Both projections of the first-arrow equation are
proved from the nested-restriction comparison and the biproduct identities.
The proved private helper `map_pair_comparison` combines the two component
equalities using generic biproduct identities, so the geometric proof needs no
rewriting through large restriction-functor expressions.
The proved private helper `exists_injective_representative` abstracts the
resolution calculation over a Grothendieck abelian category, avoiding unnecessary
unfolding of concrete sheaf-module definitions in the geometric proof.
No data definition selects a witness from an unproved existence statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.derived_open_union_ses_presentation`
(node `lem-sc-derived-open-union-ses-presentation`).
This is a decomposition into two lower holes, not an unconditional proof.
The item's module has no remaining sorry.

Added, and left with exactly `:= by sorry`:

- `AlgebraicGeometry.schemeOpenUnionImageComplex_shortExact`
  (`lem-pc-open-union-image-complex-exact`, new module
  `Sheaf.AlgebraicGeometry.OpenUnionImageComplexExact`): underived exactness for
  a fixed complex with injective terms. It does not mention a derived category,
  an object E, a supplied right adjoint, or comparison isomorphisms.
- `AlgebraicGeometry.schemeOpenModuleImageComplex_localized_comparisons`
  (`lem-pc-localized-open-image-complex-comparisons`, new module
  `Sheaf.AlgebraicGeometry.LocalizedOpenImageComplexComparisons`): derived
  comparisons of the fixed J_T and their nested restrictions for a K-injective
  representative. It does not assert a short complex or exactness, and it needs
  neither a two-open cover nor termwise injectivity.

Net holes in this delivery: one closed, two added. Existing imported holes are
unchanged; their use is intentional under the stage-3 brief.

## No longer needed

Second reading removed redundant direct imports from the two new modules:
`Sheaf.AlgebraicGeometry.DerivedCategory` from
`LocalizedOpenImageComplexComparisons` and
`Mathlib.CategoryTheory.Preadditive.Injective.Basic` from
`OpenUnionImageComplexExact`. Both remain available through the public imports of
`KInjectiveMayerVietorisData`; both new modules recompiled cleanly.

No pre-existing import was removed: the original module imported only
`Sheaf.AlgebraicGeometry.DerivedCategory`, which its statement still needs.

The planned three-open wrapper node
`lem-pc-kinjective-mayer-vietoris-comparisons` and its module
`Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisComparisons` are not needed by this
proof route. The generalized localized comparison uses the individual explicit
computation and restriction-comparison nodes instead. This is pruning of this
node's route, not a claim that the wrapper is unreachable from all other targets.

The other former direct proof dependencies removed from this node's direct route are:

- `def-pc-derived-open-restriction-maps`: retained through the concrete image-complex
  data, and used in the localized-comparison argument.
- `lem-pc-open-derived-localization-adjunction`: retained by the localized-comparison node.
- `lem-pc-open-image-complex-comparison-restriction`: retained by that same node.
- `lem-sc-ringed-space-injective-restriction-surjective`: retained by the new exactness node.
- `lem-weil-pbc-exact-functor-derived-factorization`: retained by the localized-comparison node.

`prop-pur-kinjective-resolutions-exist` remains a direct proof dependency.
No unit statement or realized unit step is bypassed; this unit's realized lists
are empty.

## Where the brief, the DAG or earlier work was wrong

The existing exactness and presentation theorems assume U union V is all of X;
they cannot be specialized to this item's arbitrary opens on X. The existing
comparison interface uses the open-subscheme category and the fixed
`schemeDerivedDirectImage`, whereas this statement allows arbitrary right
adjoints on localized module sites. These are the two gaps split off here.

The local literature checkout lacks `cohomology.tex`; the Stacks pages for
[08BV](https://stacks.math.columbia.edu/tag/08BV) and
[079W](https://stacks.math.columbia.edu/tag/079W) were read directly.
LeanSearch returned Internal Server Error for both new statements; LeanFinder
and actual searches of Mathlib and the project supplied the remaining searches.

`blueprint_refs.py ancestor` returns None for this stage-3-created item because
its created.item is a module name, not a DAG node id. The new nodes retain the
explicit existing blueprint ancestry of the parent, prefixed by the parent id.

## New nodes

`lem-pc-open-union-image-complex-exact` realizes step 2 of the parent argument.
The arrows and all three complex objects are fixed by the existing concrete
data; only their zero composite and short exactness remain to prove. Its
sectionwise argument is Stacks 08BV on U union V, with injective restriction
surjectivity. Empty and repeated opens were checked in the mathematical statement.

`lem-pc-localized-open-image-complex-comparisons` realizes the comparison portions
of steps 1 and 3. It states the K-injective computation independently of any
exactness construction and records how the common Hom universe, the open-site
equivalence, exact derived factorization, and uniqueness of right adjoints
transport the existing nested comparison. Its supplied adjunctions handle empty
and repeated opens as well. Neither new node repeats the parent statement.

No interface change record or forced adaptation is needed.

## Second reading by U3

1. **Statements and visibility: pass.** Read the complete repository/sandbox diff of
   `DerivedOpenUnionSESPresentation`. The existing theorem's signature and docstring
   are byte-for-byte unchanged, as confirmed also by `stage3_delivery.diff_module`
   (`statement_changed = []`). The only existing public import remains
   `Sheaf.AlgebraicGeometry.DerivedCategory`; all four added imports are proof-only.
   The two new modules introduce only the reported theorem statements, with no
   new data definition. There are no forced adaptations or change records.

2. **Proof and axioms: pass, relative to the two named lower holes.** Independently
   compiled all three delivered modules with `lcompile.py`, without errors or
   warnings. The main proof uses the actual `Q.objPreimage`, the source's constructed
   `kInjectiveResolutionFunctor` and `toKInjectiveResolution`, and the proved
   degreewise-injectivity result; its comparison is obtained by localizing the
   actual quasi-isomorphism, not choosing an arbitrary unproved representative.
   `S`, `f`, `g`, and the biproduct isomorphism are explicit constructions. Checked
   the private biproduct helper projection by projection: `map_lift_mapBiprod`
   gives the localized lift, and each projection is exactly the supplied nested
   comparison identity. The only textual holes are the two public theorems
   reported above, each with body exactly `:= by sorry`. No forbidden declarations
   or hollow definitions occur. The scratch `#print axioms` audit and delivery
   probe verify only the standard axioms plus `sorryAx` for the named open claims.
   This is one upper hole closed and two lower holes added, a decomposition
   (net -1), not an unconditional proof.

3. **New statements: pass.** Read the concrete `schemeOpenModuleImageRestriction`
   mate in `KInjectiveMayerVietorisData`, the explicit computation isomorphism in
   `OpenImageComplexComparisonIso`, and its proved nested compatibility in
   `OpenImageComplexComparisonRestriction`. Read Stacks
   [08BV](https://stacks.math.columbia.edu/tag/08BV),
   [01EB](https://stacks.math.columbia.edu/tag/01EB),
   [08BS](https://stacks.math.columbia.edu/tag/08BS), and
   [079W](https://stacks.math.columbia.edu/tag/079W). Exactness uses gluing over
   `T ∩ (U ∪ V)` and injective restriction surjectivity to `T ∩ U ∩ V`;
   it does not presume ordinary direct image preserves epimorphisms. The
   localized comparison uses the open-site equivalence and exact derived
   factorization, then `rightAdjointUniq` with its counit equation; hence arbitrary
   supplied adjunctions, including differing normalizations, are covered.
   Its beta is the supplied counit (the inverse hom equivalence of identity),
   with the same nested restriction as `derivedOpenHomRestriction`.
   Empty opens give zero terms, equal opens give the diagonal/difference exact
   sequence, disjoint opens give zero overlap, and zero I gives zero terms.
   Non-covering U,V are allowed because the first term is J_(U ∪ V), not I.
   Each new claim is strictly part of the argument: exactness contains no
   localization/comparison, and comparison contains no exactness or short complex.
   Both have complete source/proof docstrings and matching new DAG nodes.
   Independent LeanFinder searches used section-surjectivity and right-adjoint
   transport terminology; Loogle found `Adjunction.rightAdjointUniq`; Mathlib
   grep found its counit identities and degreewise exactness. Read the project
   `KInjectiveMayerVietorisExact`, `KInjectiveMayerVietorisDegreewise`,
   `OpenModuleImageAmalgamation`, and comparison modules, and searched the upstream
   `WeilConjectures` tree. The exactness interfaces require U ∪ V = top, and the
   comparison interfaces concern open-scheme categories with the fixed right
   derived functor. No existing declaration supplies either new statement as
   written; neither closes by a few-minute direct application.

4. **Route and pruning: pass, with report/import cleanup.** The proof first uses
   Mathlib localization/biproduct tools and the constructed upstream resolution,
   and leaves only underived exactness and localized adjunction comparison.
   Checked all seven old direct proof dependencies. The unused three-open
   comparison wrapper is pruned from this route; the other removed direct
   dependencies remain below the two new nodes or in concrete-data statement
   imports, as individually listed in `## No longer needed`. The unit
   `sk-thm-picard-duality` has `realized.statement = []` and `realized.steps = [[]]`;
   no realized unit node or step is bypassed. Removed two redundant imports in
   the new modules: `DerivedCategory` in the localized comparison module and
   `Mathlib.CategoryTheory.Preadditive.Injective.Basic` in the exactness module.
   Their declarations are already publicly available through
   `KInjectiveMayerVietorisData`. No existing module import was removed.

5. **DAG: pass.** The parent node's three steps now match the resolution,
   concrete short-complex construction, and two-projection comparison in Lean;
   its `proof_deps` are exactly the resolution node and the two new nodes.
   The new exactness node records fixed data and injective restriction
   surjectivity. The new comparison node records the explicit computation,
   common-universe open localization, nested comparison, and exact factorization
   (the last is an existing Mathlib leaf). Verified chapter/unit, source,
   searches, creation/blueprint ancestry, and Lean records of both new nodes.
   Only `proof`, `proof_deps`, `proof_origin`, and `lean` change in the existing
   node; statement fields and maintainer review records are preserved.

Second-reading changes: removed the two redundant new-module imports; expanded
`## No longer needed` to enumerate all former direct dependencies; added this
independent review. No theorem statement or proof body changed.

