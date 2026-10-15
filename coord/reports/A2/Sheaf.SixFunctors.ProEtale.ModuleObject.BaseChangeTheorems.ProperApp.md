## What changed

Replaced the remaining proof hole in
`Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` by a compiling
integral reduction argument. The existing signatures, universes and visibility are
unchanged. The algebraic-closure component was already proved on the baseline and is
unchanged; its proof is not claimed as new work.

The continuous component chooses an integral model of the exchange arrow, proves its
integral exchange invertible by residue reduction and conservativity, applies derived
E scalar extension, and transports through the actual Arrow isomorphism. No inverse
is assumed in either realization statement. All existential witnesses are eliminated
inside proofs of propositions; no definition chooses data from a holed existence theorem.

Added five modules under `Sheaf.Paper`:

- `ContinuousIntegralCoefficients`: constructs the norm valuation ring, quotient by ℓ,
  continuous coefficient maps, and their existing derived extensions of scalars. The
  quotient is proved discrete and finite. The ring E is proved to be localization of
  its integral ring at ℓ; continuous functions on any compact space are also proved
  to have this localization description, with a uniform denominator. Continuous
  functions lift through the integral quotient. The actual sequence
  `O_E --ℓ--> O_E --> O_E/(ℓ)` is proved short exact in condensed abelian groups.
  It is also proved short exact as a sequence of internal integral module objects.
  All this data and these proofs are real.
- `IntegralReductionConservative`: the integral derived Nakayama obligation.
- `IntegralFiniteExchangeComparison`: the comparison between the reduced integral
  exchange and the image of an etale finite-coefficient exchange.
- `IntegralExchangeReduction`: a complete proof from that comparison and the existing
  `Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`. Finiteness of the residue
  ring proves the additive torsion hypothesis. Functorial preservation of isomorphisms
  and `MorphismProperty.arrow_mk_iso_iff` finish the proof.
- `ContinuousExchangeIntegralModel`: the constructible integral model and compatibility
  with scalar extension of the specified continuous E exchange.

The item's new imports are proof-only. New modules expose only imports needed for
statements and definitions; proof-specific Mathlib and etale proper imports are private.
The continuous component node now records the implemented three-step route.

## Proved and sorry left

One baseline hole closed:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_continuousMap_app`.
The item has no remaining `sorry`. Its other component was already proved.

Also proved:
`AlgebraicGeometry.ProEtale.CondensedRing.integralExchange_reduction_isIso`, the coefficient
ring instances, `continuousIntegralFunctions_isLocalization`, and
`integralResidue_functions_surjective`, `integralReduction_comp_zero`, and
`integralReductionSequence_shortExact` and `integralModuleReductionSequence_shortExact`
in the new coefficient module.

Three holes added, each with exactly `:= by sorry`, its own module, source, proof in
words, and node:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_reflects_isIso`
  (`lem-weil-pbc-integral-reduction-conservative`). Still needs the integral internal-module
  realization and its coefficient-dependent kernel/cokernel/extension closure, top-degree
  derived tensor cohomology, and the resulting sheafwise Nakayama argument. The ordinary
  valuation-ring Jacobson radical and finite-module Nakayama specializations were checked
  in a compiling scratch experiment; that does not supply the sheaf/derived bridge.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralFiniteExchange_comparison`
  (`lem-weil-pbc-integral-finite-exchange-comparison`). Still needs the constant finite
  coefficient/internal-module equivalence, bounded-below etale origin of the reduced
  complex, the derived form of the proved module-linear coefficient sequence,
  reduction/pushforward comparison, and compatibility of units, counits
  and the square. The residue's finite discrete topology, continuous quotient lifts and
  two-term coefficient sequence in internal modules are proved; its derived realization
  remains required.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousExchange_integral_model`
  (`lem-weil-pbc-continuous-exchange-integral-model`). Still needs constructible lattices
  and extension-class descent in the raw internal-module category, the uniformly
  bounded-below localization telescope comparison with qcqs pushforward, and its
  adjunction-mate compatibility. The scalar localization calculation itself is proved.

This is a decomposition: one baseline hole closed and three lower holes added, net -2
before any changes elsewhere in the target import closure. It is not an axiom-free proof
of the target. The finite reduction invokes the existing torsion theorem, retaining the
blueprint unit's projective-line, prime reduction and torsion assembly route.

## No longer needed

The continuous component no longer directly uses the planned
`thm-weil-pbc-finite-extension` or `prop-weil-pbc-qbar-condensed-two-colimit`; its direct
proof dependencies are the new integral model, integral finite reduction and reduction
conservativity. The general `lem-weil-pbc-condensed-e-realization` is replaced at this
interface by the narrower obligations, while relevant parts remain in their proof plans.
These nodes are not claimed globally unnecessary.

No existing import was removed from the item: its existing `ModuleObject.Colimit.TwoColimit`
import remains necessary for the already proved qbar component. No existing library module
is globally pruned or withdrawn. The new coefficient module imports `Condensed.ContinuousMap`
and Mathlib padic numbers in place of its exploratory `Condensed.EllAdic` import. Its constructible category alias uses the smaller
`ConstructibleSheaf.ProEtaleModule.DerivedCategory` import rather than the full six-functor
restriction module. The new conservativity module does not need the exploratory public `MorphismDefs` import. All
scratch modules were removed from `lean/` and retained only under `scratchpad/`.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox report described the previous qbar delivery. That delivery is
already on the baseline. This report counts only the continuous hole closed now.
The original continuous node's single proof step mixed the finite-E realization with
the algebraic-closure filtered two-colimit argument. The finite-extension and condensed-E
realization plan nodes have no Lean attachment; they could not simply be applied under
those names. The existing etale additive-torsion proper theorem is usable and is applied.

The ordinary internal-module bounded constructible definition imposes no derived
completeness. Consequently the completed-category statements in the DAG cannot be used
without a realization identification. The new conservativity and model obligations
explicitly retain that work. Likewise, the current triangulated-subcategory theorem
requires coefficient-dependent closure assumptions; noetherianity alone is insufficient.

Bhatt--Scholze Lemma 6.8.13 provides a constructible integral lattice, not necessarily a
global lisse integral lattice. The model's proof in words uses the constructible version.
The actual Section 6.8 source (arXiv:1309.1198v2), including Propositions 6.8.11 and 6.8.14,
and the reduction results of Sections 6.5--6.7 were read.

Exploratory simultaneous imports of the old pro-etale comparison interface and the
current module-object/etale interfaces produced duplicate declarations of
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»` between `ProEtale.UpperLowerStar.Defs` and
`ProEtale.FiniteCoefficient.UpperLowerStar.Defs`. No library interface or held module
was changed to work around it. The delivered comparison statement uses the current
etale interface and a functor into the actual internal-module residue category.

Mathlib searches are logged in `searches.jsonl`. Leansearch returned HTTP internal
server errors; those entries are recorded as unavailable, not as mathematical no-match
results. Leanfinder, qualified Loogle queries and local searches found generic
isomorphism transport and compact/discrete finiteness tools, but no exact continuous
proper-base-change or integral realization theorem.

## New nodes

`def-weil-pbc-continuous-integral-coefficients` records the concrete coefficient diagram
and its proved topology and localization properties. Its definitions use no `sorry`.

`lem-weil-pbc-integral-reduction-conservative` is a general conservativity statement for
maps of integral bounded constructible complexes, with no exchange or properness premise.

`lem-weil-pbc-integral-finite-exchange-comparison` only compares two arrows. It has no
properness or Cartesian premise and asserts no exchange invertibility.

`lem-weil-pbc-integral-exchange-reduction` is proved from the preceding comparison and
the existing etale torsion proper theorem.

`lem-weil-pbc-continuous-exchange-integral-model` only realizes the E exchange as a scalar
extension of an integral arrow and asserts no exchange invertibility. The three remaining
obligations are strict parts of the integral argument, rather than renamed copies of the
original theorem. No change record is needed: no existing statement, definition or public
import was changed, and no forced adaptation was made.


## Second reading by A2

1. **Signatures and accidental changes.** Compared every delivered module with the shared repository. The existing target declarations retain byte-for-byte signatures; the target proof only adds proof-only imports and a proof body. The added declarations are in new `Sheaf.Paper` modules and are recorded by matching DAG nodes. No change record is needed.

2. **Compilation and trust basis.** Compiled the complete sandbox with `lcompile.py --all`; it succeeds. Searched the delivered Lean sources for forbidden declarations and untracked `sorry`s. The three remaining `sorry`s are exactly the named split-off theorems in the report and their DAG nodes; no definitions contain `sorry`. Removed an exploratory probe file that duplicated a split theorem and contained an untracked `sorry`.

3. **Split statements.** Read each split-off statement and its docstring against its node. The conservativity, finite-exchange comparison, and integral-model statements are strict lower obligations and do not restate the target. Their hypotheses and conclusions are preserved in the node records, with source and proof plans. No existing Mathlib or library declaration duplicates them.

4. **Route and pruning.** The target proof follows the recorded integral model, residue exchange, conservativity, scalar extension, and arrow transport route. The proper-base-change unit remains realized by its existing torsion and bounded-below nodes; the new route is below the unit level. The report's no-longer-needed dependencies match the target proof; no existing import was removed. Public imports in new modules are limited to declarations appearing in their public signatures; exploratory proof imports are private.

5. **DAG agreement.** Checked the target node and all five added nodes against the Lean declarations, including proof dependencies, proof origins, split status, and module/declaration paths. The target node records the realized three-step route. The sandbox is ready for delivery.

### Changes made during second reading

Removed `lean/Sheaf/Paper/IntegralFiniteExchangeComparison__probe.lean`, an exploratory duplicate containing an untracked `sorry`; no theorem or public interface depended on it.
