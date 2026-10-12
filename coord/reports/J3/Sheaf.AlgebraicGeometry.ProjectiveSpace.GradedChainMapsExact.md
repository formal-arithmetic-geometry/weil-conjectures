## What changed

Replaced the hole in `AlgebraicGeometry.Proj.graded_chain_maps_exact` by a complete
Lean proof from the chart maps and exactness of equal-degree away fractions.
The existing signature is unchanged. Three fixed-chart maps are constructed; two
applications of the localized exact-pair statement establish the basis-section
properties. A proved private helper checks zero composites by sheaf separation,
constructs local lifts for both kernels and the last map, proves the first map monic,
and combines the exact short complexes into `ComposableArrows.mk₃.Exact`.

Added `Sheaf.AlgebraicGeometry.ProjectiveSpace.FixedChartMap`, with a **proved**
`AlgebraicGeometry.Proj.fixed_chart_map`. It directly localizes the linear map,
transports it through the injective chart identifications, checks linearity and
restrictions, and extends the map from the standard-open basis using Mathlib's
`restrictHomEquivHom`. The initial elaboration timeout was caused by underspecified
arguments to `extend_hom_app`; explicit arguments resolved it. No file was split
in order to evade a compile limit.

Added `Sheaf.Algebra.Module.ProjAwayDegreeZeroExactPair`, with the general
exact-pair interface needed for the two middle terms. The endpoint properties are
conditional, rather than assumptions required for exactness. It has one remaining
hole. Updated the original node's proof, dependencies and origin to the actual
basis-section argument. No target, definition, existing signature or public import
changed. All additions and proof imports were checked for import cycles.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Proj.graded_chain_maps_exact`
(node `lem-sc-p1-graded-chain-maps-exact`). No sorry remains in the item's module.
Also proved `AlgebraicGeometry.Proj.fixed_chart_map`
(node `lem-sc-p1-fixed-chart-map`) and the two private basis helpers.

Added exactly one hole: `LocalizedModule.proj_away_degreeZero_exact_pair`
(node `lem-sc-p1-away-degreezero-exact-pair`), whose proof is exactly `by sorry`.
Its docstring and node give the localized grading construction, independence after
clearing denominators, homogeneous-component lifting, and transport through the
chart maps. This is a decomposition of the original hole, **not** a claim that the
target is independent of sorry or that the net hole count decreased. The remaining
statement concerns three abelian groups on one localization, no sheaves, stalks or
sheaf maps, and assumes an exact pair rather than a four-term exact chain.

All three delivered modules compile locally in import order. The item and the proved
chart-map module have no sorry. The prescribed delivery dry run is the final check.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists`
  (`lem-weil-pbc-proj-graded-module-sheaf-exists`, as a proof dependency; it still
  supplies the meaning of the fixed chart hypotheses in the original statement).
- `Sheaf.AlgebraicGeometry.ProjSheafificationExact`
  (`lem-sc-p1-proj-sheafification-exact`).
- `Sheaf.AlgebraicGeometry.ProjTildeFunctorial`
  (`lem-sc-p1-proj-tilde-functorial`).
- `Sheaf.Topology.SheafOfModulesFromBasis`
  (`lem-weil-pbc-sheaf-of-modules-from-basis`).

The proof needs neither an associated sheaf for the image module nor a comparison
between the additive-subgroup and homogeneous-submodule Proj models, canonical
stalk charts, their transport, or the splicing of two sheaf short exact sequences.
This is pruning below the unit level; `sk-thm-picard-duality` has no realization
entry requiring any of these nodes. It does not remove the graded-resolution or
sheafification steps of the unit. Dependencies remain relevant elsewhere in the
project; this report asserts only their absence from this proof.

## Where the brief, the DAG or earlier work was wrong

The previous plan is mathematically plausible, but its interfaces do not directly
implement it: `tilde_functorial` requires stalk identifications that the target
hypotheses do not supply, and its ring grading is an additive-subgroup grading.
`proj_sheafification_shortExact` requires both endpoint properties for each triple;
neither original middle triple is short exact. The proof therefore uses chart
morphisms directly and a genuine exact-pair localization statement. The latter is
strictly a part of the argument; it neither restates nor repackages the target.

The chart-map calculation does not need internality or degree-compatible scalar
multiplication for the indexed numerator subgroups: preservation of those subgroups
and the stated chart/range/scalar/restriction conditions suffice. Those unnecessary
binders were omitted from the new theorem. The original theorem is unchanged.

Sources read: Stacks 01M7 (functoriality and exactness) and 009U (modules on a basis),
and the existing localization/basis-exactness modules and Mathlib declarations.
LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder, Loogle,
Mathlib grep, the source library, the DAG and the blueprint index were searched.
The blueprint index returned the graded-resolution ancestor but no separate node
for either extracted interface. Ordinary localization exactness is already the
Mathlib leaf `lem-sc-p1-localization-short-exact` and is reused in the new plan.

Edge cases checked: the zero polynomial has zero away localizations; injective
chart maps then force zero chart groups. The empty open is handled by the sheaf
condition and the basis cover, with no nonempty-domain assumption. Zero modules,
zero maps with exactness, and noninjective first / nonsurjective second maps in an
exact pair are permitted: the endpoint assertions are conditional. Arbitrary fields
and the original universe are retained. The generalized pair lemma requires the
homogeneous-component lifting argument even when neither endpoint property holds;
the old short-exact theorem alone cannot be applied to either triple.

## New nodes

`lem-sc-p1-fixed-chart-map` records the proved chart-map construction in
`lean/Sheaf/AlgebraicGeometry/ProjectiveSpace/FixedChartMap.lean`. It supplies one
map for one graded linear map, with no exactness claim. Its proof uses ordinary
module localization, the existing standard-open properties and the Mathlib leaf
for morphisms on a basis.

`lem-sc-p1-away-degreezero-exact-pair` records the one remaining hole in
`lean/Sheaf/Algebra/Module/ProjAwayDegreeZeroExactPair.lean`. It isolates preservation
of exactness and conditional endpoint properties on one homogeneous localization.
Its source is Stacks 01M7 and the homogeneous-localization construction of 00JM.
No change record is needed: no existing definition or statement changed.

## Second reading by J3

1. **Visible contract: pass.** Read the complete diff against the repository module.
   The existing theorem signature and its docstring are byte for byte unchanged;
   `stage3_delivery.diff_module` reports no changed statement. No definition or
   target changed. The four removed imports and all new imports are proof-only;
   the existing public imports remain unchanged. The only new declarations are
   the two public interfaces and proved private helpers.
2. **Proof and trust: pass as a decomposition.** Independently compiled the three
   modules in import order (1.8, 17.7 and 17.0 seconds), with no errors or warnings.
   Read both helpers, the chart transport, restriction calculation, and the two
   applications in the chain proof. Explicit scratch `#print axioms` checks of
   `graded_chain_maps_exact`, `fixed_chart_map`, and
   `proj_away_degreeZero_exact_pair` each report only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The proved chart map still depends on the open
   standard-open-properties theorem. There is exactly one delivered `sorry`, in
   the named public localization theorem; no definition contains a hole, and no
   forbidden declaration or trust escape occurs. The choices in `fixed_chart_map`
   use the proved `hrange` assertion and are uniquely determined by injectivity of
   beta. The chain proof chooses chart data from its explicit hypothesis, not from
   an unproved existence theorem. One original hole closes and one new hole opens:
   net zero, not an independent proof of the target.
3. **Extracted statements: pass.** Read Stacks Tags 01M7, 00JM and 009U alongside
   the two new statements. The chart-map theorem needs precisely its injective
   range, scalar, restriction and degree-preservation conditions; internality is
   unnecessary for this construction. The exact-pair theorem retains internality,
   compatible scalar action and degree preservation, and imposes neither endpoint
   property on the pair. Its endpoint conclusions are conditional. For f=0 all
   away modules vanish, hence injective alpha forces zero chart groups. For a
   nonzero homogeneous f, the polynomial ring is a domain, so f^m has its unique
   degree m*d; this justifies identification with equal-degree fractions. Clearing
   a common denominator and a further annihilating power gives distinct numerator
   degrees in the independence argument. Taking the degree-zero component of a
   localized preimage proves the kernel and surjectivity clauses. Zero modules,
   negative grading components, noninjective phi and nonsurjective psi cause no
   missing case. Basis covers and sheaf separation handle the empty open too.
   The remaining lemma is strictly smaller than the sheaf-chain item.

   Independent searches used LeanFinder for exactness of the homogeneous degree-zero
   component functor, Loogle for `DirectSum.IsInternal`, and Mathlib grep for
   `homogeneous.*exact|exact.*homogeneous|degreeZero` (recorded in searches.jsonl).
   Also searched the repository and the upstream ProjectiveSpace/Modules sources.
   Mathlib supplies ordinary localization exactness and basis extension, already
   used in the plan/proof. Read the existing `ProjAwayDegreeZeroExact`,
   `ProjDegreeZeroLocalizationExact`, `GradedLocalizationExact`,
   `LocalizedHomogeneousPiece`, and `ShortExactGradedComponent` interfaces: the
   first and last require both short-exact endpoint assumptions, while the general
   graded-localization interface uses integer ring gradings and lacks the chart
   transport and endpoint clauses. No existing declaration directly closes this
   extracted interface in a few minutes; it remains the reported hole.
4. **Route and pruning: pass.** The actual route constructs three chart maps,
   applies exactness to two adjacent triples, and proves sheaf exactness by basis
   lifts. The removed old proof dependencies are exactly the four nodes under
   `No longer needed`; standard-open properties remain used. Every import of the
   proved modules supports either a signature, a localization scalar instance,
   basis extension, standard-open facts or local lifting. The unit record
   `sk-thm-picard-duality.realized` has empty statement and step arrays and requires
   none of the pruned nodes. The graded-resolution/sheafification route remains;
   only its implementation below the unit changes.
5. **DAG agreement: pass.** Compared the old and submitted item nodes: only its
   proof, proof_deps and proof_origin change. Its four steps match chart-map
   construction, two localization applications, basis local lifting and exact-chain
   assembly. Read the cited standard-open, basis-morphism, local-lifting and
   localization Mathlib-leaf records: they supply the facts used. Both new nodes
   have complete Lean signatures matching their modules, source and natural-language
   proofs, search records, creation metadata, blueprint ancestry and the item's
   chapter/unit. Their proof dependency lists equal the unions of their step uses.

**Changes made in second reading:** added the proof-only import
`Mathlib.Algebra.Module.LocalizedModule.Exact` to the remaining localization-hole
module, so that its cited Mathlib proof dependency is available as the plan requires.
Added this review. No proof, signature, definition or node statement was changed;
no further hole was closed or added.
