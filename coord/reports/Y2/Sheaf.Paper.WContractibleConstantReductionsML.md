## What changed

Added `Sheaf.Algebra.Homology.AdicShortComplexCohomologyML`, with actual ideal-power
quotients, canonical transitions, their cohomology tower, and a complete Artin–Rees
cycle-correction proof of Mittag–Leffler. Only the outgoing term must be finite.
Also proved that exact additive functors preserve stabilized transition images and
that sections of the actual constant module sheaf are exact.

The assigned finite-comparison theorem now assembles that algebraic argument with
one separately stated geometric finite-projective-model result. The latter is the
first two paragraphs of Stacks Tag 09C5; it asserts a single bounded finite-projective
model and the finite-triple equations, with no Mittag–Leffler conclusion. The geometric
statement includes a complete source-based proof plan, including nilpotent perfection,
completion, localization-universe transport, and the quotient-unit equations.

The finite-triple image transfer is proved in the new
`Sheaf.CategoryTheory.FiniteTripleMittagLeffler`, for arbitrary cofiltered categories
and independent universes of sets. It retains one target bijection for both images;
markings may vary with the finite triple.

Also proved `DerivedCategory.isPerfectRingComplex_change_localization_iff`,
which transports the actual bounded finite-projective representative through the
canonical equivalence of independently sized derived localizations. It supplies
the perfect-representative part of the model's inverse-limit reconstruction step.

The proved auxiliary `AlgebraicGeometry.Scheme.constantReductionsRealization_iso`
identifies the actual representative-based realization with the existing exact
commutative-coefficient derived constant functor. Its proof compares the ring
sheafification isomorphisms, cancels coefficient transport, applies the comparison
degreewise, and composes with the derived representative marking.

The completion comparison is also explicit: `constantReductionsCompletionKer`
computes every evaluation kernel as the corresponding power of the extended ideal,
including exponent zero. `constantReductionsCompletionIso` constructs the quotient
ring equivalence from that evaluation map, and `constantReductionsCompletionIso_mk`
proves its formula on representatives. These replace the planned passage through
cofinal powers in model step 4. All three contain no holes.

The existing `mlConstantDerivedObject` now specializes the same representative
construction on an abstract small site. This is a definitionally equal factorization,
recorded in `coord/changes/Y2-constant-reductions-realization.md`. Existing public
signatures are unchanged. The main node now records the finite-triple transfer proof
actually used, rather than repeating the expanded proof of its dependency.

Also filled the existing `CategoryTheory.siteConstantModuleFunctorGeneral_exact`
hole without changing its statement, imports or definitions. The new general-site
conservativity theorem proves reflection of derived isomorphisms on objects not
covered by the empty sieve. Its perfectness-reflection corollary combines this with
the existing local algebraicity theorem, for independent localization universes.

## Proved and sorry left

The geometric module's `AlgebraicGeometry.Scheme.constantReductionsRealization_iso`
and its completion kernel and quotient comparison lemmas are fully proved; the main finite-projective model theorem is its sole remaining hole.

The new algebraic declarations `AdicCohomology.isMittagLeffler`,
`AdicCohomology.map_isMittagLeffler`, and
`AdicCohomology.sections_preservesHomology` are fully proved. Their constructions and
transition/naturality lemmas contain no holes. The algebraic module compiled cleanly
on the project server; its three public proof APIs depend only on `propext`, `Classical.choice`, and `Quot.sound`.

`DerivedCategory.isPerfectRingComplex_change_localization_iff` is proved and compiled;
it uses the canonical localization equivalence and retains the same complex and bounds.

`DerivedCategory.perfect_of_nilpotent_reduction` is also proved and compiled, with
only the three permitted axioms. It derives finite generation and both degree bounds
from the existing nilpotent projective-complex lifting theorem, using nilpotent
Nakayama. Its module is the declared dependency of the remaining geometric model
node; it is not imported into the still-unproved geometric theorem.

`CategoryTheory.constantRealizationReflectsIsomorphismGeneral` is completely proved
and has only the three permitted axioms with the completed exactness theorem.
`CategoryTheory.perfect_of_constant_realization_iso` has a complete proof from the
existing local algebraicity theorem; its axiom audit still reaches that existing
statement's `sorry`, as the stage-3 dependency policy allows. Neither declaration
contains a new hole. Both compiled on the project server. The new finite-triple transfer also has only
the three permitted axioms; the main theorem still reaches the geometric model
hole, as reported below.

On the current shared source, the original hole
`AlgebraicGeometry.Scheme.wcontractible_constant_reductions_mittagLeffler` is closed
by a complete proof through the now-proved
`AlgebraicGeometry.Scheme.wcontractible_constant_reductions_finite_comparison` and
`CategoryTheory.Functor.isMittagLeffler_of_finiteTripleRangeComparison`.
One new named hole remains:
`AlgebraicGeometry.Scheme.constant_reductions_finite_projective_model`, node
`lem-sfb-constant-reductions-finite-projective-model`. This is a decomposition of
the assigned theorem into its geometric model and proved algebraic stabilization;
it is not claimed as a complete proof of the geometric model. The extra existing
hole `CategoryTheory.siteConstantModuleFunctorGeneral_exact` is also closed.
Thus the packet closes two existing holes and adds one, before the ledger's
closure accounting. The assigned module has zero remaining holes.

The full sandbox compiled successfully with `lcompile.py --all`: all eight Lean
modules, including the representative comparison and the assigned assembly. Earlier attempts failed because the compile server lacked the
published `AdicQuotientCohomologyML` artifact. That earlier delivery was subsequently
rolled back in the shared sources. The packet now proves the needed finite-triple
transfer in its own module and has no import of the absent module.
No existing dependency was copied into the sandbox to bypass the build contract.

## No longer needed

The following proof-only imports were removed from the assigned module:

- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.Algebra.Homology.AdicQuotientCohomologyML` (present in the initial snapshot,
  absent after rollback; replaced by the delivered finite-triple transfer)
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.RingTheory.NilpotentProjectiveComplexLift`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.RingTheory.RlimPerfectComplete`
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`
- `Mathlib.RingTheory.AdicCompletion.Basic`
- `Mathlib.RingTheory.Ideal.Quotient.PowTransition`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`
- `Mathlib.RingTheory.AdicCompletion.LocalRing`
- `Mathlib.RingTheory.AdicCompletion.Algebra`
- `Mathlib.RingTheory.AdicCompletion.Completeness`
- `Mathlib.RingTheory.Filtration`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero`
- `Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism`
- `Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal`
- `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`

The geometric dependencies (local algebraicity, scalar-extension normalization,
nilpotent lifting, and perfect reconstruction) are retained in the new model node's
proof plan. They are not claimed as globally pruned. The completion-Noetherian
module is still used directly. The constant-section theorem is used by the new
algebraic module. The two scheme-specific nodes `lem-sfb-constant-realization-detects-zero` and
`lem-sfb-constant-realization-reflects-isomorphism` are replaced in the geometric
model's plan by the proved general-site conservativity node. No existing mathematical
module is withdrawn by this packet.

Removed the old main-node `tool_uses` approvals because its Lean proof uses only
finite comparison and finite-triple transfer. The removed approvals are:

- `lem-weil-pbc-constant-module-section-properties`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-nilpotent-projective-complex-lift`
- `lem-weil-pbc-adic-completion-mod-ideal`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-rlim-perfect-complete`
- `lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`
- `lem-pc-kflat-closure`
- `lem-pur-derived-change-of-rings`
- `lem-pc-kflat-resolution`
- `lem-pur-kflat-change-of-rings`
- `lem-weil-pbc-site-sheafification-sections-local`

## Where the brief, the DAG or earlier work was wrong

The earlier finite-comparison node grouped geometric reconstruction, algebraic
Artin–Rees, and exact sections in one unresolved step. They are distinct arguments;
the algebraic part now has a complete proof. The existing main-node plan repeated
these steps although its Lean proof only applied the finite-comparison theorem.

The source's Tor/pro-system last paragraph is unnecessary for this route: direct
cycle correction by Artin–Rees proves stabilization for the actual quotient maps.
Checked degenerate ideals, the zero ring, zero complexes, arbitrary incoming and
middle modules, repeated indices, and the empty-scheme geometric model. The unit's
integral-criterion route is retained. The source-library boundary is respected.

During this run the shared repository rolled back the earlier V4 finite-comparison
delivery: its generic dependency and DAG nodes disappeared and the main theorem
again had a hole. The packet was reconciled with that source: finite comparison is
proved here, its node is included, and the absent generic module is replaced by
`FiniteTripleMittagLeffler`. The main-node metadata outside the allowed proof fields
was refreshed from the current source. No absent path is listed for deletion.
The latest full compile succeeds. Temporary diagnostics are outside `lean/` and
are not part of the delivery.

## New nodes

`lem-sfb-adic-short-complex-cohomology-ml` records the proved Artin–Rees cycle
argument and the exact-functor/constant-section passage. Actual Mathlib searches
found Artin–Rees and the general eventual-range API, but no cohomology result.

`lem-sfb-constant-reductions-finite-projective-model` records the geometric model
and finite-triple equations from the first two paragraphs of Tag 09C5. It leaves
no algebraic stabilization assertion unresolved. Blueprint and whole-DAG searches
found no separate node stating this geometric part. Its Lean realization and the
scheme-specific specialization use the same standard derived representatives.
The standard diagram cohomology functor is similarly factored through its named
implementation; `coord/changes/Y2-constant-reductions-tower-cohomology.md` records this.

`lem-sfb-perfect-nilpotent-reduction` is fully proved. It supplies the precise
algebraic nilpotent-perfection consequence needed by the geometric model's second
step. No existing DAG or library declaration states it: the existing projective
lift provides a bounded-above projective model and a termwise quotient isomorphism,
and the new proof derives finite generation and both bounds. Searches of all three
kinds found no Mathlib perfect-complex result. Source: Tags 09C5, 09AR and 00DV.

`lem-sfb-wcontractible-constant-reductions-finite-comparison` is included with its
complete assembly proof and current dependency plan, since the earlier version
was removed by the shared-source rollback. Its statement and Lean signature are
retained, with the finite-triple predicate supplied by the new module.

`lem-sfb-finite-triple-range-ml-transfer` records the fully proved general transfer
criterion. Its proof lifts elements through a stabilized composite and compares
both images using the same injective target marking. All three Mathlib search
kinds found only the eventual-range components, which the proof uses.

`lem-sfb-constant-realization-reflects-isomorphism-general` records the proved
general-site conservativity theorem and its perfectness-reflection corollary. The
empty-cover criterion avoids transferring a scheme-specific theorem across site
and localization universes. All three Mathlib search kinds were performed; the
existing local-map theorem is used for the perfectness corollary.

`lem-sfb-perfect-change-derived-localization` records the fully proved invariance of
perfectness under changing the localization universe. The Mathlib equivalence and its
comparison functors are used directly; no new localization construction or witness
is introduced. Its source is the derived localization definition, Tag 05RU, as used
for the perfect model in Tags 09AW and 09C5. It is a declared dependency of model step 4.

Change records: `coord/changes/Y2-constant-reductions-realization.md`,
`coord/changes/Y2-constant-reductions-tower-cohomology.md`, and
`coord/changes/Y2-constant-module-exactness-proof.md`.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
