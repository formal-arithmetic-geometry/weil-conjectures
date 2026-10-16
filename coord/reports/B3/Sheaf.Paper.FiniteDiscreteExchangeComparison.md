## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_comparison`
by a reduction through concrete exact coefficient realization, bounded triangulated devissage,
the three actual unit--square--counit comparisons, and naturality. The existing statement,
including its universes and hypotheses, is unchanged.

Added a proved finite-discrete condensed-ring comparison by locally bijective sheafification.
The finite family of clopen fibres proves local surjectivity; constants prove local injectivity,
with the empty covering handling empty profinite sets. The comparison preserves ring operations.

Added `Sheaf.Paper.FiniteDiscreteSchemeRing`: a proved monoidal comparison of the
constant ring with its inverse image on every scheme. The proof conjugates terminal-section
comparisons under monoidal adjunctions and explicitly identifies the transported ring structures.

Added a concrete derived realization functor and proved its shift, triangulated, fullness,
and single-complex APIs. Fullness uses the existing source-library bounded-below
comparison theorem, whose proof still depends on the existing comparison injective-acyclicity hole. A private import bridge exposes this consequence without exposing the old
pro-etale upper/lower-star definitions, which conflict with the newer coefficient definitions.

The exchange-step interface is a generic three-step comparison structure. Its composition method
proves the arrow isomorphism from the three commuting squares. The record also remembers the
specified total arrows and their defining factorization equations, so consumers use the interface
without unfolding the site functors. The factors are fixed to the actual unit, square and counit
steps: the residual statement cannot choose arbitrary factorizations. Bounded derived origin uses existing `DerivedCategory.prop_of_bounded`, rather
than a new constructible derived-category theorem.

## Proved and sorry left

One original hole closed: `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_comparison`.
One new hole: `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_coefficientRealization`
(node `lem-weil-pbc-finite-discrete-coefficient-realization`). This is a decomposition, not a net
hole reduction. The parent combines the lower statements by genuine Lean proofs.

The residual statement now receives the already proved monoidal coefficient-ring
identifications on all schemes. It concerns abelian coefficient equivalences, **sheaf-level** constructible
origin, and the three comparison squares. It does not assume origin of arbitrary bounded
complexes or an isomorphism of the assembled exchange arrows. It still needs a sectionwise
coefficient encoding consistent across schemes; transport of local finite presentations; and
unit, composition, and counit identities for the derived adjunction comparisons. Independent
choices of the supplied encodings may twist scalar actions and must not be assumed coherent.

Proved without new holes: `Profinite.finiteDiscreteCondensedRing_constant`,
`AlgebraicGeometry.ProEtale.finiteDiscreteEtaleRealization_full`,
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteRealization_single`,
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_stepRealization`,
`AlgebraicGeometry.ProEtale.finiteDiscreteSchemeRing_constant`,
`FiniteDiscreteThreeStepComparison.nonemptyArrowIso`,
and the concrete realization's additive, shift, triangulated, and fullness instances.

Axiom verification distinguishes local proofs from closure. The constant-function map,
condensed-ring comparison, scheme-ring isomorphism and comparison, concrete realization,
single-complex compatibility, and generic three-step assembly use only `propext`,
`Classical.choice`, and `Quot.sound`. The fullness bridge additionally reaches the pre-existing
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective` hole
(node `lem-weil-pbc-comparison-grothendieck-injective-acyclicity`). The parent and step realization
also reach the new residual hole. Their `#print axioms` includes `sorryAx`, so the original
hole is closed only relative to these open dependencies. The delivery closes one original
hole and adds one: a one-for-one decomposition rather than a completed target proof.
This is the balance within the delivered files; no pinned target-closure ledger figure is claimed.

Empty schemes and the zero ring require no nonzero assumptions. The fibre-cover proof handles
empty profinite sets separately by the empty covering. The residual comparison does not assert
exchange is invertible, and adds no properness or Cartesian hypothesis.

## No longer needed

The original route's `lem-weil-pbc-finite-ring-constructible-derived-origin` is unnecessary for
this item: bounded origin follows from the sheaf origin, fullness, and generic triangulated
bounded devissage. Its lower implementation need not be developed for this route.

The original direct dependency `prop-weil-pbc-site-comparison-finite-level` and its module
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` are not used directly by the parent.
The concrete realization uses the proved source-library derived comparison theorem directly;
the residual adjunction coherence must compare the actual functors, rather than merely assume
the finite-level exactness/unit/acyclicity conjunction. Site-comparison theory itself is still
needed; this removes the original direct dependency, not that mathematical input. The
sheaf-origin node still cites finite-level comparison transitively, so this node is not
claimed as globally pruned.

Removed the parent's private import of `Sheaf.Paper.ConstantInternalModuleSheafEquivalence`.
Its statement remains a planned dependency of the residual coefficient-realization node;
the parent uses the new realization interface instead. This is not a claim that the encoding
lemma is globally unnecessary.

Removed the unused flat-resolution import from the new fullness bridge. Moved the
triangulated-subcategory import from the new realization wrapper to a private proof import
of the item. The constant-pullback construction imports its conjugation and pushforward
coherence tools privately. Removed the three redundant public imports from the new
coefficient-realization module; its realization-functor import supplies their statement API.

Second reading removed six redundant imports. From the item: the public
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` and the private
`Mathlib.CategoryTheory.Triangulated.Subcategory` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`. All three remain available
through the retained public pro-etale exchange import. From the new condensed-ring module:
`Mathlib.CategoryTheory.Sites.LocallyBijective` and
`Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology`, already supplied publicly by
`ContinuousMap`. From the new realization-functor module: the public
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, already supplied
publicly by the pro-etale exchange import. Removing these redundant imports does not remove
any declaration from the public import closure.

For completeness, the third removed original direct proof dependency is
`lem-weil-pbc-constant-internal-module-sheaf-equivalence`. It remains a planned dependency
of the residual node; only its direct use by the parent was removed. Thus all three old
`proof_deps` have been accounted for. No existing Lean module is withdrawn or claimed globally
pruned. No unit-realization step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old derived-origin dependency has no Lean attachment, but that does not block this proof:
existing generic bounded devissage replaces it. The finite-level comparison statement is not
itself an exchange-coherence theorem. Compatibility of underlying abelian sheaves alone does
not license arbitrary coefficient encodings to be identified across different schemes.

The source has old and new pro-etale functor trees with overlapping public names. Publicly
importing the old derived-comparison module together with the internal-module framework fails.
A private-import bridge proves the needed fullness consequence and prevents the old definitions
from leaking into the item. No source file or existing signature was changed to achieve this.

The inherited item blueprint metadata names the non-blueprint target
`nt-target-proetale-e` as its blueprint ancestor. New nodes instead name the actual
blueprint ancestor `thm-weil-pbc-finite-extension`, recording the target and intermediate
created nodes in `via`. The inherited field is outside the worker's permitted edits.
Blueprint searches for constant rings, exchange realization, and triangulated single
complexes found no identical blueprint statement; the constant-ring-map blueprint uses
ordinary ring sheaves rather than the present condensed internal ring object.

Individual-file checks do not refresh dependency artifacts; final verification uses the required
sandbox compilation in import order. Temporary diagnostics are kept outside `lean/`.

## New nodes

`lem-weil-pbc-finite-discrete-condensed-ring-constant`: the proved locally bijective constant-to-
continuous-function ring comparison, in `Sheaf.Paper.FiniteDiscreteCondensedRing`.

`lem-weil-pbc-finite-discrete-etale-realization-full`: the proved safe fullness bridge, in
`Sheaf.Paper.FiniteDiscreteEtaleRealizationFull`.

`lem-weil-pbc-finite-discrete-single-realization`: concrete derived realization and its proved
single-complex compatibility, in `Sheaf.Paper.FiniteDiscreteRealizationFunctor`.

`lem-weil-pbc-finite-discrete-coefficient-realization`: the single residual obligation, in
`Sheaf.Paper.FiniteDiscreteCoefficientExchange`; its remaining work is described above.

`lem-weil-pbc-finite-discrete-exchange-step-realization`: the proved combination of coefficient
realization with single complexes and derived functor instances, in
`Sheaf.Paper.FiniteDiscreteExchangeRealization`.

`lem-weil-pbc-finite-discrete-scheme-ring-constant`: the proved monoidal constant-ring
pullback comparison, in `Sheaf.Paper.FiniteDiscreteSchemeRing`.

`lem-weil-pbc-three-step-arrow-comparison`: the proved generic composition of three
commuting squares, in `Sheaf.Paper.FiniteDiscreteRealizationFunctor`.

Change record: `coord/changes/FiniteDiscreteExchangeComparisonImports.md` documents the
redundant public-import removal and its six unchanged downstream users. No existing
statement or definition was changed.

## Second reading by B3

1. **Interfaces: pass.** Compared every delivered path with the shared repository. Six Lean
modules are new; the only existing module is the item. Its theorem signature, section
hypotheses and universes are byte-for-byte unchanged. Its existing public imports retain the
same public declaration closure after removing one redundant import. No existing definition,
target statement, or module held by another group is changed. The required import-change
record documents the preserved public declaration closure and all downstream users.

2. **Lean proofs and axioms: pass, with open dependencies recorded.** Compiled all seven
modules together in import order using `lcompile.py --all`, with no errors or warnings. A
scratch module checked `#print axioms` for the parent and every principal construction and
new theorem. Only the three permitted axioms and `sorryAx` for the identified open dependencies
occur. There is exactly one literal `sorry` in the delivered Lean, in the reported public
residual theorem; no forbidden declaration or hollow definition. The realization definition
is the explicit composite of derived functors for a supplied equivalence. It does not choose
arbitrary data from an unproved existence theorem; existential witnesses are eliminated only
inside proofs of propositions.

3. **Residual statement: pass as a decomposition.** Read the sheaf-origin and constant-module
encoding dependencies, checked the zero ring, empty schemes, empty profinite set, identity
square, and general non-Cartesian square cases. The new hole asks for underived sheaf origin
and the three specified comparison squares for fixed concrete realizations. It does not ask
for arbitrary bounded-complex origin or the assembled exchange-arrow isomorphism. The parent
proves bounded origin by `DerivedCategory.prop_of_bounded`, then assembles and transports the
comparison by naturality. Thus the new hole is a strictly lower obligation, although it still
requires substantial coefficient and adjunction coherence work. Its proof-in-words and matching
node are present; expanded the finite-matrix argument connecting local finite presentations
to locally constant finite module sheaves. Checked the sources directly at
[Stacks Tag 09AK](https://stacks.math.columbia.edu/tag/09AK) and
[Bhatt--Scholze](https://arxiv.org/pdf/1309.1198), Corollary 5.1.6, Proposition 5.3.2,
and Lemmas 5.4.1 and 5.4.3. Independent `msearch.py` LeanFinder and Loogle queries about internal
constant-ring module equivalences and pullback/direct-image compatibility, plus grep for
constructible essential image and exchange-step interfaces, found generic `SheafOfModules`
APIs, but no replacement for this internal `Mod` comparison. Searched both project roots by
concept as well. The residual cannot be closed in a few minutes from those APIs.

4. **Route and pruning: pass after repair.** Checked bounded devissage, the actual
unit/square/counit factors, their total-arrow equations and naturality transport. The route
keeps the realized statement and three steps of `dag/units/sk-thm-properbasechange.json`.
Removed six redundant imports and explicitly accounted for every removed original
`proof_deps` entry above. No global module pruning is claimed.

5. **DAG: pass after repair.** Read all eight delivered nodes, their declarations and dependency
unions. New nodes carry source, proof-in-words steps, search records, creation provenance,
blueprint provenance, chapter, unit, and verbatim Lean statements. Corrected the fullness
bridge node to name its existing generic injective-acyclicity dependency and to distinguish an
existing Lean proof from a proof whose axiom closure is already complete. Existing parent node
changes remain confined to stage-3-owned fields.

Second reading changed import redundancy, fullness dependency metadata, source attribution,
the residual docstring's finite-matrix argument, and report accuracy. The mathematical reduction and the one residual statement were retained.

The first dry run required an import-change record for removing the redundant public import.
Added `coord/changes/FiniteDiscreteExchangeComparisonImports.md`, enumerating all six
transitive downstream modules from the read-only downstream tool. No user is adapted.
The unchanged direct user `Sheaf.Paper.IntegralFiniteExchangeComparison` also compiled
against the sandbox artifacts, with no errors or warnings. Its scratch copy is outside
`lean/` and is not delivered.
