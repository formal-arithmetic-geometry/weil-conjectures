## What changed

Proved `CategoryTheory.ringed_sheaf_slice_adjunction`, retaining its complete statement and
`RingedSheafSliceAdjunctionData` unchanged. The proof constructs the ringed element-site
localization, the fibre equivalence, both module adjunctions, exact additive extension by
zero with its direct-sum sheafification formula, and relocalization.

The existing element-site constructions are moved verbatim into
`Sheaf.CategoryTheory.RingedSheafSliceConstruction` and publicly re-exported from the item.
This allows the three supporting proof modules to import the constructions without a cycle.
Every existing public name, universe, signature and definition body is preserved.
Change record: `coord/changes/U3-ringed-sheaf-slice-construction.md`.

The supporting modules prove element-site descent by lifting sieves and gluing pairs,
construct the general ringed module direct image from compatible families, and compute
presheaf extension using the universal property of direct sums. Mathlib supplies the
canonical extension adjunction, exact coproducts of modules, and module sheafification.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ringed_sheaf_slice_adjunction`
(`lem-weil-pbc-ringed-sheaf-slice-adjunction`).

Added zero holes. Every supporting theorem is proved:

- `CategoryTheory.elementModuleExtension_adjunction`
  (`lem-weil-pbc-element-module-extension-adjunction`).
- `CategoryTheory.element_site_descent` (`lem-weil-pbc-element-site-descent`).
- `CategoryTheory.continuous_cocontinuous_ringed_restriction`
  (`lem-weil-pbc-continuous-cocontinuous-ringed-restriction`).
- `CategoryTheory.element_module_presheaf_extension_formula` and
  `CategoryTheory.element_module_presheaf_extension`
  (`lem-weil-pbc-element-presheaf-extension`).

There are no remaining `sorry`s in any delivered Lean file. The existing direct-sum
identity and composition proofs are retained verbatim. This is a proof, not a decomposition.

Validation: all five delivered modules compile in import order without warnings.
All three unchanged direct consumers compile against them:
`Sheaf.CategoryTheory.RingedPresentationTransport`,
`Sheaf.Paper.OrientedProperFibreExchange`, and
`Sheaf.SixFunctors.OpenTensorNormalization`. `#print axioms` for the original theorem and every supporting
main theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed direct imports and corresponding unused proof dependencies:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the public construction uses the existing
  Grothendieck topology and no special precoverage-axiom predicate.
- `Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`
  (`lem-weil-pbc-continuous-cocontinuous-topos-adjunction`): Mathlib's proved
  Grothendieck-topology adjunction applies directly; its precoverage/pullback hypotheses
  need not be reconstructed.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
  (`lem-weil-pbc-ringed-topoi-module-adjunction`): that interface uses commutative rings;
  here the compatible-family construction handles the assigned `RingCat` signature directly.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`lem-weil-pbc-module-sheaves-colimits-forgetful`): the two adjunctions give preservation
  of colimits and limits for restriction, while presheaf extension and module sheafification
  give left exactness of extension.
- The separate dependency `def-weil-pbc-sheafification`: the fibre equivalence glues pairs
  directly. There is no separate set-sheafification construction in the proof.

Other original public imports move with the unchanged constructions;
`RingedToposMorphism` remains public in the item. The supporting theorem imports are
proof-only. No pre-existing module is withdrawn. These removals concern this proof's
requirements; modules still needed by other parents remain available. The unit's own
statement and realized steps are untouched.

## Where the brief, the DAG or earlier work was wrong

The declared continuous/cocontinuous interface has precoverage and covering-pullback
hypotheses not supplied by this item's signature. The general ringed-module adjunction
interface is restricted to commutative rings, while the assigned Lean theorem uses all rings.
The source arguments remain valid for those rings. The proof supplies the missing general
compatible-family construction and the arbitrary-sheaf element-site descent explicitly.

The direct-sum calculation can be proved through its hom equivalence with restriction,
without implementing a separate comma-category finality argument. Exactness follows from
Mathlib's exact coproducts and exact module sheafification; no sectionwise surjectivity of
sheaf epimorphisms is assumed. Empty fibres and the zero ring are covered by the same
coproduct and universal-property arguments. Empty covers are included in the descent proof.

The retained DAG records had signatures truncated at named arguments such as `(F := ...)`;
these records now contain the complete Lean theorem signatures.

The direct-sum functor, adjunction and evaluation isomorphism (`rawSumFunctor`,
`rawSumAdjunction`, `rawSumEvaluationIso`) are now private `@[no_expose]` definitions
instead of reducible abbreviations. This prevents routine elaboration from expanding
adjoint construction terms; `rawSumFunctor_map_lof` is the proved characterizing lemma
used for the summand calculation. The optimized presheaf-extension module compiles in
7.0 seconds in the final import-order compile, with no warnings; the main item
compiles in 12.1 seconds. Their signatures and mathematical
constructions are unchanged, and no consumer can refer to these private helpers.

Resumed validation on 2026-10-19: all five retained modules compile in import order
against the current published build. The current direct consumers compile against the
identical compiled overlay: RingedPresentationTransport in 26.6 seconds,
OrientedProperFibreExchange in 14.0 seconds, and OpenTensorNormalization in 45.5 seconds.
A fresh downstream scan lists 995 transitive importers; the change-record user table
has been refreshed to include each one. The extracted constructions and original data
structure were compared with current sources and are textually identical. The old
profiling module was moved out of the delivery source tree; it was a diagnostic artifact,
not part of the construction or proof.

## New nodes

`lem-weil-pbc-element-module-extension-adjunction`: the unchanged construction definitions
and the proved specialization of Mathlib's canonical extension adjunction.

`lem-weil-pbc-element-site-descent`: proved topology comparison, cocontinuity, the sheaf-slice
fibre equivalence and its natural identification, and continuity for maps of element sites.

`lem-weil-pbc-continuous-cocontinuous-ringed-restriction`: proved general ringed restriction
with compatible-family module direct image and its adjunction and linearity verification.

`lem-weil-pbc-element-presheaf-extension`: proved direct-sum formula by the universal property
and uniqueness of a left adjoint; finite-limit preservation follows from evaluation,
Mathlib's exact module coproducts, and joint reflection of limits by module evaluation.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
