## What changed

Proved `AlgebraicGeometry.Etale.exists_etaleHypercohomology_pullback_functorial`
with its statement unchanged. Added the proof-only imports
`Sheaf.Paper.EtaleHypercohomologyPullbackMaps` and
`Sheaf.Paper.DerivedEtaleCohomologyPullbackLaws`.

The proof obtains the construction and derived abutment laws separately. It proves
spectral-sequence identity and composition itself. The proved private helper
`spectralSequence_ext_first` inducts on the integer page using `Int.leInduction`;
the homology compatibility equation and cancellation of the page comparison
isomorphism give the successor step. For nonnegative resolution degree, cancel
the first-page identification and apply `cohomologyPullbackFunctorial`,
`cohomologyMap_map`, and `Sheaf.H.map_comp_apply`. For negative resolution degree,
the presentation's `negative` field gives equality of maps from a zero object.
Thus the construction lemma does not assume any identity or composition law for
its spectral-sequence maps. No assertion is proved merely by applying a renamed
copy of the original theorem.

The dependent existential types have named binders unused in their own types.
The completed theorem therefore uses a local `linter.unusedVariables false`
setting; no declaration binder or type was changed to silence that warning.
A local transparency setting supports the complex-component comparisons.

All three delivered modules compile in import order using lcompile. No targets,
definitions, or existing declaration signatures were changed. The unit
`sk-prop-h2` has no realization assigned to this auxiliary node; its route stays
unchanged. The new statements were checked in the zero-complex case, identity
scheme map, and complexes concentrated in one degree. The latter case reduces
the construction to ordinary sheaf cohomology; the derived identity/composition
statement reduces to the ordinary unit and inverse-image coherence laws. No
extra finiteness or bounded-above hypothesis was introduced.

## Proved and sorry left

Proved in the original module:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_pullback_functorial`
(node `lem-weil-pbc-hypercohomology-e1-pullback-functorial`).
Its module contains no sorry. Its proof still depends on named sorry theorems,
as intended for a stage-3 reduction.

New remaining sorry declarations:

- `AlgebraicGeometry.Etale.exists_etaleHypercohomology_pullback_maps`, in
  `Sheaf.Paper.EtaleHypercohomologyPullbackMaps`, node
  `lem-weil-pbc-hypercohomology-pullback-maps`. This is the construction,
  E1 identification, and stable-page/filtered-abutment comparison, without
  spectral-sequence or abutment identity/composition laws.
- `AlgebraicGeometry.Etale.derivedEtaleCohomology_pullback_laws`, in
  `Sheaf.Paper.DerivedEtaleCohomologyPullbackLaws`, node
  `lem-weil-pbc-derived-cohomology-pullback-laws`. This states only identity and
  composition for the explicitly specified unit--Leray--complex-map derived
  cohomology pullback. It has no spectral sequence or filtration witnesses.

Both proofs are exactly `by sorry`; each has its source and complete proof in
words in the docstring and its matching DAG node. The private helper is proved.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Their construction work remains in the proof plan of the new construction
module; these removals relocate dependencies rather than prune the transitive
DAG. No original supporting node or module is claimed globally unnecessary.
The original node's proof_deps now name the two construction/law obligations,
the ordinary cohomology laws, the spectral-sequence definition and the
presentation definition. Its old resolution and filtered-complex dependencies
are named by the new construction node instead. All public imports stay as on
the original module.

The complete old direct `proof_deps` removed from the original node are:

- `lem-weil-pbc-cartesian-eilenberg-functorial`
- `thm-sp-spectral-object-yields`
- `thm-sp-if-e1`
- `prop-weil-pbc-inverse-image-exact`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-etale-cohomology`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `def-weil-pbc-kinjective-resolutions`
- `lem-weil-pbc-inverse-image-composition`

These remain construction or derived-coherence dependencies of the split nodes;
none is claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The existing `cohomologyPullbackFunctorial` declaration gives ordinary
cohomology naturality, composition, and identity, but does not contain the
canonical derived P identity/composition laws mentioned in the old plan.
The new derived-law node isolates that missing interface. The source module
`WeilConjectures.SixFunctors.Etale.Derived.GlobalSections` explicitly lists
deriving general pullback naturality as a TODO; its Leray isomorphism alone
is not a theorem giving the two laws.

`Functor.exists_hypercohomology_firstPage` supplies nonfunctorial existential
presentations. It does not assert compatibility of page maps and stable-page
isomorphisms for varying schemes. `cartanEilenberg_lift` supplies a double-complex
lift, not the E1 computation or the canonical derived abutment comparison.
The new construction obligation records precisely this remaining assembly.

The literature files are absent in this local read-only clone. I read the
Stacks Project pages for Tags 015J, 015K and 0EZM on the official site.
Tag 015K explicitly explains the filtered-complex source of functoriality.
Searches through the prescribed msearch tool found no exact replacement:
LeanSearch was unavailable (HTTP Internal Server Error), Loogle listed the
spectral-sequence API, LeanFinder found general complex extensionality and
underived pullback coherence, and Mathlib grep found no matching étale
hypercohomology pullback or derived-law theorem. The failed service is recorded
as unavailable, not as a negative result. Blueprint searches for
`hypercohomology` and `cohomology pullback` found no exact version of either new
statement; the existing hypercohomology nodes concern other spectral sequences
or the objectwise first-page theorem.

## New nodes

`lem-weil-pbc-hypercohomology-pullback-maps`:
`lean/Sheaf/Paper/EtaleHypercohomologyPullbackMaps.lean`. It packages steps 1--3
of the original construction, excluding all functoriality laws; its proof plan
keeps the original resolution, row comparison and filtered convergence route.

`lem-weil-pbc-derived-cohomology-pullback-laws`:
`lean/Sheaf/Paper/DerivedEtaleCohomologyPullbackLaws.lean`. It isolates the two
canonical derived abutment laws from the final part of the old plan. It is
independent of the spectral-sequence construction.

No change records are needed: all new imports are proof-only and all existing
public statements and definitions are unchanged.

## Second reading by M2

1. Compared the original module with the read-only repository by diff and checked
   the entire theorem signature byte for byte: identical. The only existing-node
   fields changed are `proof`, `proof_deps`, and `proof_origin`. There are no
   changed definitions, target statements, or public imports in the original
   module, and no undeclared signature change. Verdict: pass.
2. Compiled all three delivered modules in import order with lcompile. Read the
   full proof, including the page induction, the negative-degree zero-source
   cases, and the inverse-image comparison components. The two reported named
   theorems are the only sorries; there are no definitions with sorry or forbidden
   declarations/options. Scratch-copy `#print axioms` checks give exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the three public
   theorems. The private page-extensionality helper has only the three permitted
   axioms. Verdict: pass as a reduction with two open obligations.
3. Read both split statements, their docstrings and nodes, and the upstream
   resolution, first-page, derived adjunction and Leray definitions. The
   construction obligation omits all identity/composition laws; the derived-law
   obligation contains no spectral-sequence or filtration witnesses. Each is
   strictly part of the original argument, and the proved E1-to-all-pages
   reduction is substantive. Mathematically checked zero complexes, identity
   maps, zero complex morphisms, a sheaf in a single (including negative) degree,
   and differently bounded source/target complexes: finite diagonals and finite
   filtrations follow from the individual lower bounds; no common bound across
   all complexes is required. In degree zero the laws are the ordinary unit
   coherence, and negative resolution degrees have zero E1 source. No false
   edge case or added hypothesis was found. Independently searched Loogle for
   `CategoryTheory.SpectralSequence.Hom`, LeanFinder for derived natural
   transformation composition, and Mathlib grep for `rightDerived_ext` and
   comparison-factorization lemmas; also searched the Sheaf and upstream source
   using global-section/unit/coherence terminology. These find ingredients,
   including `NatTrans.rightDerived_comp` and `Functor.rightDerived_ext`, rather
   than either complete obligation. Read Stacks Tags
   [015J](https://stacks.math.columbia.edu/tag/015J),
   [015K](https://stacks.math.columbia.edu/tag/015K), and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM) on the official site; the
   filtered-complex functoriality route agrees with them. Neither remaining
   obligation can be closed by a short application of an existing theorem.
   Verdict: pass.
4. Checked the top-down route: construction and abutment laws are supplied
   separately; ordinary cohomology laws prove E1 functoriality, then induction
   proves every later page. Mathlib hom_ext requires all pages, so it does not
   replace that induction. The original node realizes no statement or step in
   `sk-prop-h2` (`realized` is `statement: []`, `steps: [[]]`); no unit route was
   altered. The complete removed direct dependency list is now recorded above,
   with the distinction between relocation and global pruning. Removed the new
   derived-law module's unnecessary imports of the termwise presentation and
   topological-invariance module; it now publicly imports only derived global
   sections and the derived adjunction module needed by its signature.
   Verdict: pass.
5. Parsed all three node records and compared their recorded Lean signatures
   after whitespace normalization. The signatures match; proof_deps equal the
   union of step uses; the original node describes the actual construction/law
   applications and page induction. New nodes have sources, proof plans,
   proof_origin, searches, split status, creation and blueprint metadata, and
   Lean records with the correct module, declaration, chapter and unit.
   Verdict: pass.

Changes made by the second reader: minimized imports of the new derived-law
module, corrected its conclusion indentation, and completed the report's removed
DAG-dependency list. No mathematical statement or proof was rewritten.
