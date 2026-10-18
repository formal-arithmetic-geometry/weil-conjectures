## What changed

Replaced the hole in `CategoryTheory.exists_ringedExtendedCech_global_model` by a complete
Lean construction from two strictly smaller obligations. The existing statement, universes,
instances, and the final completion-model theorem are unchanged.

The construction indexes by **all** specified finite generating slices, which form a cover.
It sheafifies the concrete Godement ring family on each slice, glues the resulting augmented
complexes, and composes the local derived Čech comparison with the gluing isomorphism and the
comparison for derived restriction. The final augmentation equation is proved using naturality
of `mapDerivedCategoryFactors`; it is not an additional assumption.

The delivery also proves the infrastructure used in this construction: the finite generating
cover; simultaneous local linear expressions in finite generators; equality of the generated
section ideals on common test spans; effective gluing of augmented module complexes; canonical
module-sheafification isomorphisms on a covering locus; restriction of module sheafification;
and the corresponding canonical ring-family comparisons. The presheaf terms, restrictions,
differentials, augmentation, and degreewise sheafification are explicit definitions with no
postponed data or choice from an unproved existence theorem. The specified ring-family maps
are parameters of these definitions. The existential global proof uses the existing strict
Godement functoriality theorem.

The finite-generator descent theorem is itself proved: its local-equality hypotheses are
supplied by `exists_cover_generatingLists_ideal_eq`, and it applies the more general ideal
descent obligation. The latter file includes fully proved common-span comparison and uniqueness
helpers, with their formulas on original presheaf-unit sections. The common-span comparisons
are proved to satisfy the triple cocycle; evaluation gives linear transitions and is
proved to preserve composition and differentials. These support the remaining naturality and augmentation
assembly. The canonical common-span comparisons also preserve the degree-zero augmentation,
proved on presheaf-unit sections by transport of the ring-family augmentation. Since the
target is a single-degree complex, this is the equation needed for augmentation compatibility.

The source was read in `algebraization.tex`, Tags 099D/099E, especially the finite common
refinement and independence-of-ideals paragraphs. The proper-base-change unit's realized
statement and three steps are retained. No existing definition or statement was repaired,
and no module belonging to another group was adapted.

Validation: the required delivery dry run compiled all 13 modules and passed preflight,
including the axiom probes, with no deferred probe. The review class is CODEX because the
delivery adds modules and nodes. Existing statements and target signatures are unchanged.

## Proved and sorry left

Original holes: **1**. The item's file now has **0** holes.

Closed in the item's file:

- `CategoryTheory.exists_ringedExtendedCech_global_model`
  (`lem-weil-pbc-extended-cech-global-model`). Its proof combines finite generation, strict
  descent, effective augmented gluing, and derived augmentation naturality.

Added and still open:

- `CategoryTheory.exists_ringFamily_idealDescentData`
  (`lem-weil-pbc-functorial-ring-complex-ideal-descent`), in
  `Sheaf.Paper.FunctorialRingComplexIdealDescent`. The section-ideal comparison, canonical
  sheafification/restriction comparisons, canonical common-span chain isomorphisms, and
  the uniqueness test on presheaf-unit sections are proved. A family of canonical chain
  comparisons with the triple cocycle is constructed. Evaluation is proved to preserve
  composition and differentials. Their degree-zero augmentation equation is proved. What remains is restriction
  naturality of the evaluated transitions, transfer of the augmentation equation through
  terminal evaluation and the specified rank-one identifications, and assembly of the
  descent data.
  This obligation has no ideal module, finite-type assumption, covering-family assumption,
  derived category, or Čech comparison.
- `CategoryTheory.ringFamilySheafModel_cech`
  (`lem-weil-pbc-functorial-ring-complex-cech-comparison`), in
  `Sheaf.Paper.FunctorialRingComplexCechComparison`. What remains is the natural scalar-extension
  comparison from a K-flat replacement over the global-section ring, followed by exact
  sheafification, and the explicit finite ordered tensor/localization comparison. The existing
  Godement Čech and normalized base-change declarations are the ring-theoretic inputs.
  This obligation concerns one global generating list and contains no ideal-sheaf descent.

Thus this is a **decomposition**, not a net proof: one original hole closed, two holes added,
net holes closed minus added **−1** within the changed declarations. Pre-existing holes
in imported modules are not counted here. There are no other new holes, anonymous holes, axioms,
or holes in definitions. In particular `exists_ringFamily_descentData`,
`exists_augmentedComplex_of_glueData`, `exists_cover_generatingLists_ideal_eq`,
`exists_ringFamilySheafModel_restrictionIso`,
`ringFamilySheafModel_iso_of_locally_equal_ideals_with_unit`, and the module-sheafification
comparison/uniqueness theorems are fully proved.

The empty finite generator types, empty lists, empty cover/index type, repeated generators,
zero generators, and zero ring are allowed in the constructions and in both new obligations.
Finite simultaneous lifting and ideal-span membership include the empty-index cases, and
no terminal object or fibre products in the original site are assumed.

## No longer needed

No pre-existing import in the item's module was removed: all its original imports support its
unchanged statements or the already proved reflector argument. All new proof-only imports of
that module are private.

The **global-model route** does not use
`lem-weil-pbc-special-cocontinuous-sheaf-equivalence`
(`Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`) or
`def-weil-pbc-sites-and-cohomology` (`Sheaf.CategoryTheory.SiteCoveringAxioms`). A cover indexed by all
specified finite generating lists and effective augmented gluing replace the dense-subsite
reduction and transport of module categories. Neither module is imported for this proof.

It also does not use the aggregate `lem-weil-pbc-ring-complex-functorial`
(`Sheaf.Paper.RingComplexFunctorial`): the concrete Godement family and its strict maps suffice.
The Godement Čech and base-change inputs remain needed for the separate local comparison;
they are not claimed to be pruned.

The final completion-model node now cites exactly its two proved combining inputs,
`lem-weil-pbc-extended-cech-global-model` and
`lem-weil-pbc-extended-cech-reflector-properties`. Its former direct references to
`lem-weil-pbc-ringed-site-module-sheafification-exact`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-pbc-ringed-localization-rhom-calculus`,
`lem-weil-pbc-ringed-derived-complete-elements-ideal`,
`lem-pur-rhom-global-sections`, and `def-pur-derived-internal-hom` are no longer direct
proof dependencies. Several remain needed transitively by the unchanged reflector proof
or by the local Čech comparison; no whole-library pruning claim is made for them.

Exploratory wrappers discarding the canonical unit formulas and an unused same-site
span-equality corollary were removed from the delivery. The retained canonical statements
supply the stronger interface required by descent. An unused alternate construction of
the restricted augmentation and its full-complex wrapper were also removed: the retained
degree-zero equation is the needed compatibility, since the target is concentrated in
degree zero. A weaker transition-family wrapper which discarded the unit formulas was
also removed; the retained coherent chain-comparison family has the information needed
for naturality. The unused direct derived-restriction
import was replaced by the directly needed `RingedSiteModules` import in the new
single-list Čech comparison module.

## Where the brief, the DAG or earlier work was wrong

The original global-model node had an empty `proof_deps` list and put the whole global
construction into one unresolved step. There was no stated augmented-complex gluing API or
formal independence-of-generators interface supplying that step. The new route records the
explicit constructions, the proved finite common-refinement argument, and the two remaining
obligations separately. Neither new obligation restates the original global existence theorem.

The earlier completion-model node still described a dense-subsite argument and the entire
reflector proof inline, although Lean already delegated the latter to the reflector-properties
theorem. Its proof route has been updated to match the actual Lean combination.

During source checking, Tag 03DJ was found to concern exact extension by zero, rather than
restriction/sheafification compatibility. The new restriction module cites the verified
Sites Tag 04B8 (`lemma-almost-cocontinuous-sheafification`) and Modules on Sites Tag 04IY
(`lemma-relocalize`). Existing modules were not changed for this citation issue.

## New nodes

`def-weil-pbc-ringed-ideal-generating-index`: the explicit small index of all specified
finite generating slices.

`lem-weil-pbc-finite-ideal-generating-cover`: the finite-type local generator data provide a
cover, and hence the family of all such specified slices is covering. Proved.

`def-weil-pbc-functorial-ring-complex-sheaf`: the actual presheaf complex and its augmented
degreewise module sheafification, parameterized by the ring family and its maps.

`def-weil-pbc-augmented-module-complex-glue-data`: linear transitions on all test spans,
including differential, cocycle and augmentation equations.

`lem-weil-pbc-augmented-module-complex-gluing`: effective degreewise gluing of those data
and construction of the global augmentation. Proved.

`lem-weil-pbc-finite-generators-local-span`: simultaneous local linear expressions for a
finite family of sections in finite global generators. Proved from the existing finite
section lifting theorem and finite free coordinates.

`lem-weil-pbc-ringed-generating-lists-local-equality`: two specified finite lists generating
one ideal sheaf give equal section ideals locally on every common test span. Proved.

`lem-weil-pbc-module-sheafification-local-iso`: canonical local-equivalence comparisons,
covering-locus uniqueness, and their augmented chain-complex form. Proved.

`lem-weil-pbc-module-sheafification-restriction`: the unit-compatible restriction comparison
and uniqueness of maps tested on original presheaf-unit sections. Proved.

`lem-weil-pbc-ring-family-locally-equal-models`: the augmented ring-family comparison under
locally equal generated section ideals, including its canonical unit formula. Proved.

`lem-weil-pbc-ring-family-restriction`: the ring-family chain comparison under continuous,
cocontinuous restriction, with its unit formula. Proved.

`lem-weil-pbc-functorial-ring-complex-ideal-descent`: the remaining coherent ideal-descent
obligation; the common-span comparisons, uniqueness, family cocycle and evaluated transition
composition/differential and degree-zero augmentation helpers in its module are proved.

`lem-weil-pbc-functorial-ring-complex-descent-data`: the finite-generator descent theorem
obtained by supplying the proved local section-ideal equalities. Proved from ideal descent.

`lem-weil-pbc-functorial-ring-complex-cech-comparison`: the remaining local derived
comparison for one globally specified list, with its augmentation equation.

There are no change records: no existing definition or statement signature changes.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
