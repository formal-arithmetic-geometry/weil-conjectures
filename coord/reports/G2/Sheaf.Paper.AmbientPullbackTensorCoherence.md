## What changed

Second returned-delivery repair: landing fb958caf532 was rejected because its
consumers imported eight quarantined source modules. Main restored those exact eight sources verbatim, preserving their existing
attachments and dependencies. Main
restored the other missing transitive sources at 188066fac0c, following A2's root
trace proof repair at 1dad6f3ccd8. Compare and omit all 132 unchanged source copies and the already-landed root
node from this packet. No archive is deleted or made
empty. The source-restoration record is
`coord/changes/G2-quarantined-import-source-restoration.md`.

Repair: restore the private construction import and explicit evaluation-theorem
import in `StrictPullbackEvaluationConstructor`. The retained packet was recovered
from the returned landing, compared with current main, and keeps the maintainer's
DAG dependency correction from the independent review. The constructor also retains main's removal of one redundant proof import.
The returned importer recheck found that IntegralComparisonSequenceSystems no
longer imported the reviewed final coherence module. Restore that proof import
while retaining the complete generic proof simplifications. An exact synchronization
with main passed the importer check but took 79 seconds in the full check, so it
was not retained. The final file preserves the original declarations and public
imports; its proof-only imports include both the coherence module and the private
construction access required by the extracted proofs.


Decomposed `WeilConjectures.AmbientPullbackTensor.ambientPullbackTensorCoherence`
without changing its signature or any mathematical definition. Original site,
ring and module constructions move verbatim to `AmbientPullbackSiteData`;
original tensor constructions and normalized bundle uniqueness move verbatim to
`AmbientPullbackTensorData`. The item publicly reexports both. Every original
public import remains publicly reachable. This avoids a proof-import cycle.
No adopted source-library declaration is changed; exact archived modules are restored.

Proved `ringMap_composition` in `AmbientCoefficientComposition`: calculate the
constant-section coefficient unit cocycle, including quotient transitions, then
transfer it through the chosen ring-sheaf adjunctions by an abstract adjunct
calculation. In the item, proved private `compositor_unit` and
`compositor_generator` from the specified mate, its defining section formula,
semilinearity, naturality and restriction composition. Assemble the original
conjunction from these calculations, normalized tensor bundle existence, and
three strictly smaller independent component theorems.

The integral consumer retains its previously compiled generic helper proofs,
with the reviewed AmbientPullbackTensorCoherence proof import restored in place
of AmbientPullbackTensorData. The strict quotient tower relocation and importer
adaptations remain unchanged.

Change records: `coord/changes/G2-ambient-coherence-construction-modules.md`,
`coord/changes/G2-unary-whiskering-compilation.md`, and
`coord/changes/G2-quotient-coefficient-data.md`.

## Proved and sorry left

The original 23-module packet and the initial eight-source restoration compiled
successfully. The broad 155-module check later stopped at the unchanged upstream
KummerOrientation exceeding 60 seconds; it did not complete and is not claimed
as a passing check. The item and ambient modules passed before that stop. The
independently landed trace root and direct importer also passed their focused
check (0d02a0220dbe3be221469bfb). No upstream source proof is changed by G2.

Closed the original item hole
`WeilConjectures.AmbientPullbackTensor.ambientPullbackTensorCoherence`, adding
three lower holes. This is a decomposition, not a completed proof of the original
result: one closed, three added, net two additional holes. The coefficient cocycle,
unit and generator calculations are complete; all extracted construction and
generic helper proofs are complete. No definition contains sorry.

Zero holes remain in the item. The original proof packet has exactly three new unfinished components:

- `WeilConjectures.AmbientPullbackTensor.coefficientPullback_isIso`,
  node `lem-sf-ambient-coefficient-pullback-iso`, module `AmbientCoefficientPullbackIso`:
  invertibility of the actual finite or sequence coefficient adjunct.
- `WeilConjectures.AmbientPullbackTensor.pullback_compositionLaws`,
  node `lem-sf-ambient-pullback-composition-laws`, module `AmbientPullbackCompositionLaws`:
  the independent ordinary and derived associativity and identity laws.
- `WeilConjectures.AmbientPullbackTensor.normalizedTensor_composition`,
  node `lem-sf-ambient-normalized-tensor-composition`, module `AmbientTensorComposition`:
  ordinary, chain and derived tensor composition squares for arbitrary normalized
  bundles, assuming the already proved scalar generator formula.

Each is a named public theorem with source and complete proof in words, and each
is strictly part of the original conjunction. The tensor step omits coefficient
invertibility and composition, tensor normalization, unit characterization,
generator computation and composition laws. All three allow arbitrary horizontal
module transitions. No arbitrary data is chosen from a new unproved existence theorem.


The eight sources independently restored on main contain two existing holes:

- `commonStagePullback_comparison_data` in `DerivedPullbackTensorHom`.
- `commonStageDerivedInternalHom_existsUnique` in `DerivedPullbackTensorHom`.

They are not new split statements or claimed proofs. The other seven source modules contain zero textual proof holes. None of these
unchanged sources or their holes is newly delivered by G2.

## No longer needed

The repaired constructor preserves main's removal of the redundant proof import
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`.

No whole module is withdrawn. The repaired strict evaluation constructor now
imports the ambient site-construction module directly; its node replaces the
final coherence dependency by the construction node. Its proof never uses the
final coherence conjunction. Original public imports remain through the
construction reexport chain. Removed the unused proof-only imports
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` and
`Mathlib.CategoryTheory.Localization.Predicate` from the relocated construction code.
Tensor-construction proof imports move to the tensor construction module.

The main node's old planned direct uses of `lem-trf-constant-coefficient-composition`
and `lem-sf-proetale-tensor-composition-unit` are replaced by the proved concrete
coefficient cocycle and unit/generator calculations. The finite constant-ring
result `prop-weil-pbc-proetale-constant-ring-map` does not by itself identify the
selected whole-sequence adjunction; whole-sequence invertibility remains explicit.
Old direct uses of `lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
`lem-pur-proetale-inverse-image-tensor-comparison` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are replaced by normalized
bundle equations and the lower tensor-composition statement. Their lower
adjunction, total-complex, K-flat and localization arguments remain recorded in
the new nodes. This prunes the planned route, not those modules globally.
The blueprint unit route is preserved.

The integral consumer no longer directly imports the proof modules
`Sheaf.CategoryTheory.SystemScalarCoherence`,
`Sheaf.CategoryTheory.SystemScalarGenerators`,
`Sheaf.CategoryTheory.DerivedCategory.CochainHomotopyComparison`,
`Sheaf.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility`,
`Sheaf.Algebra.Homology.SheafRingDerivedHomComparison`,
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`, and
`Sheaf.Paper.ResolvingRepresentativeWhiskering`; the extracted proofs import them.
Both adapted consumers import `AmbientPullbackTensorData` instead of the unused
final ambient coherence theorem. Their nodes name the exact construction dependencies.
The strict tower module's proof-only `import all` dependencies
`ProEtaleCoefficientPullbackExact` and `CoefficientRingedSequenceSite` move to its
lower coefficient module. No public source-library import or declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier five-consumer audit missed two additional current ambient consumers.
The returned constructor relies on a private declaration and a proof-only import,
which public reexport does not preserve for `import all`. Explicit imports of
their defining modules repair this visibility issue.

No target or original statement is changed or disputed. A finite levelwise
coefficient theorem alone does not identify the selected whole-sequence
adjunction. The concrete cocycle and scalar generator calculations avoid that
unstated identification; whole-sequence invertibility remains unfinished.
The selected-adjoint and tensor constructions are expensive to elaborate together.
Abstract adjunction helpers and separate site/tensor modules preserve their exact
constructions without changing global irreducibility or instance attributes.

An audit found the pre-existing DAG cycle
`lem-weil-pbc-derived-exchange-termwise` ->
`lem-weil-pbc-derived-exchange-bounded-comparison` ->
`lemma-weil-pbc-derived-exchange-replacement` ->
`lem-weil-pbc-derived-exchange-termwise` below an unchanged dependency. Every edge
exists before this delivery; none of the delivered nodes is in a cycle. These
unrelated records are left untouched and reported for the maintainer.

## Forced adaptations

Source restoration: the eight modules named in the return and the transitive
source closure are restored on main at 188066fac0c and match the archived copies.
All unchanged copies are omitted. The broad 155-file check stopped at unchanged
KummerOrientation exceeding 60 seconds; the 31-file check stopped at unchanged
DerivedPullbackTensorHom (64 seconds; c09d1a4eb6b6092c4e361f04). Neither is claimed
as a passing check. No adopted source-library declaration is edited or removed,
and no rework archive or attachment is withdrawn.

Returned-delivery repair (landing 0cddc22b9): the importer recheck reported a
duplicate environment entry for AmbientPullbackTensor.moduleRingUnit while loading
StrictPullbackAdjointConstructor. Restore the reviewed coherence proof import in
IntegralComparisonSequenceSystems, retaining the complete generic proof refactor.
An initial exact synchronization passed the importer check but timed out in the
full set; it is not the final repair. A profiled refactored version compiled in
53.4 seconds. The clean final consumer and returned importer compile together
in 41.1 and 19.6 seconds (159ff997a4a9e5eeb8e42195). The temporary importer is
removed. All profiler options are removed from the final file. No public
signature, definition, attribute, or target statement changes.

Reviewer fix (2026-10-27, packet c03e3912): the private theorem
`SequenceDerivedProof.normalizedComparisonDescent` is restored verbatim in
`IntegralComparisonSequenceSystems`. The `import all` importer
`Sheaf.Paper.FiniteQuotientPullbackDescent` (line 88) calls it and failed with
`Unknown identifier` without it. The previous reviewer fix (packet 0cddc22b) had
restored it, and this re-delivery dropped it. With the theorem restored, the consumer,
that importer and StrictPullbackAdjointConstructor all compile.

Returned-delivery repair (2026-10-27): the global build failed in
`StrictPullbackEvaluationConstructor` with unknown identifiers
`AmbientPullbackTensor.sequencePushEvaluation` (line 107) and
`SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso` (line 118).
The errors at lines 141 and 144 are consequences of the missing direct-image
comparison: the identity-on-sections formula could not reduce. The former
identifier is a private definition relocated verbatim to `AmbientPullbackSiteData`;
the latter was supplied by a proof import that the final coherence module no
longer has. Replace line 8's `import all AmbientPullbackTensorCoherence` by
`import all AmbientPullbackSiteData` and add an explicit proof import of
`SequenceModulePullbackEvaluation`. Its node replaces the final coherence proof dependency by the site-construction
node, preserving all other fields. No declaration, signature, body, attribute,
instance, or public import of this consumer is changed. The consumer is unclaimed.
The repaired constructor compiles successfully, including the unchanged `rfl`
section formula. The complete sandbox compile and all six additional `import all`
consumer checks pass (exit code zero). Their unchanged temporary copies are removed.
All twenty module entries in the return report the same failing constructor;
this single forced import adaptation addresses their shared visibility failure.
The change record is `coord/changes/G2-strict-pullback-evaluation-imports.md`.


`IntegralComparisonSequenceSystems` is unclaimed. Its unchanged direct-consumer
compile failed at 63 seconds; profiles against the original library and overlay
also failed at 71 and 77 seconds. Extracting complete generic arguments,
constructing the unary inverse explicitly, and giving the resolution witness
explicit flatness types reduce concrete elaboration. Its fixed-model scalar
adjunction is now specialized from a generic normalization proof. Scalar
composition and identity simplify the tensor-section target and apply generic
fixed-model uniqueness lemmas, avoiding the concrete model equality rewrites. Every original public signature, public import, definition body,
instance and attribute stays identical. Original private theorem signatures are
retained. Only proof imports and proofs change. The final compilation of the two ambient
inverse-section lemmas and the integral consumer succeeds under the enforced
per-file limit, without warnings. The inverse section calculations specialize complete ambient lemmas, and
constant-map naturality reuses the identical existing ambient proof.
The detailed old signatures and
new proof descriptions are in the compilation change record.

`QuotientExpressionStrictKFlatTowers` is unclaimed. Its unchanged source failed
at 76 seconds and another plain compile at 75 seconds. Local instance priority
changes did not improve it. Original coefficient constructions and two complete
transition theorems move verbatim to the publicly reexported lower coefficient
module. Both resulting modules compile within the enforced limit. Its only two
direct importers, `QuotientExpressionKFlatModels` and
`CompletedComparisonQuotientRealizationDefs`, compile unchanged. Their temporary
copies are removed. Existing syntax and transition nodes retain their identities
and move only their Lean attachments. The strict quotient unit route is preserved.

The repair also changes only the proof imports of
`StrictPullbackEvaluationConstructor`, as explained below. These three are the
only changed existing Lean modules besides the assigned item.
No adopted source-library declaration is changed; exact archived modules are restored. The other three direct importers of
the item also compile unchanged. The original five direct consumers were checked. Two additional current ambient
consumers are included in the repair checks. No other
existing module is delivered merely for a compilation check.

## New nodes

`def-sf-strict-quotient-coefficient-comparisons` records canonical strict quotient coefficient comparisons, in `Sheaf.Paper.QuotientExpressionCoefficientData`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-ambient-coefficient-composition` records composition of the actual ambient coefficient maps, in `Sheaf.Paper.AmbientCoefficientComposition`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-ambient-coefficient-pullback-iso` records invertibility of finite and sequence coefficient inverse image, in `Sheaf.Paper.AmbientCoefficientPullbackIso`. This is one of the three unfinished components described above.

`lem-sf-ambient-normalized-tensor-composition` records composition of normalized tensor comparisons and their models, in `Sheaf.Paper.AmbientTensorComposition`. This is one of the three unfinished components described above.

`lem-sf-ambient-pullback-composition-laws` records associativity and identity laws for ambient pullback mates, in `Sheaf.Paper.AmbientPullbackCompositionLaws`. This is one of the three unfinished components described above.

`lem-sf-ambient-pullback-site-constructions` records canonical ambient ringed-site pullbacks and section-normalized comparators, in `Sheaf.Paper.AmbientPullbackSiteData`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-ambient-tensor-data-exists-unique` records unique normalized ambient tensor comparison, in `Sheaf.Paper.AmbientPullbackTensorData`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-kflat-unary-whiskering` records fully faithful restriction to K-flat representatives, in `Sheaf.CategoryTheory.KFlatUnaryWhiskering`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-normalized-derived-comparison-descent` records descent of normalized derived comparison from resolving representatives, in `Sheaf.CategoryTheory.NormalizedDerivedComparisonDescent`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-system-scalar-composition-unique` records unique generator-normalized scalar composition, in `Sheaf.CategoryTheory.SystemScalarCompositionUnique`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-system-scalar-ordinary-adjunction` records normalized ordinary adjunction of a fixed cochain scalar model, in `Sheaf.CategoryTheory.SystemScalarOrdinaryAdjunction`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-system-scalar-package-exists` records normalized scalar package with a fixed cochain model, in `Sheaf.CategoryTheory.SystemScalarPackageExists`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-system-scalar-tensor-section` records scalar tensor section and the sheafification unit, in `Sheaf.CategoryTheory.SystemScalarTensorSection`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-system-scalar-unit-unique` records unique generator-normalized scalar unit, in `Sheaf.CategoryTheory.SystemScalarUnitUnique`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-unary-whiskering-from-product` records unary full faithfulness from product precomposition, in `Sheaf.CategoryTheory.UnaryWhiskeringOfProduct`. Its constructions and proofs are complete; it adds no hole.

`lem-sf-fixed-scalar-composition-unique` records the complete normalized scalar
composition comparison for fixed cochain models, in `FixedScalarCompositionUnique`.
It transports the existing normalized package comparison abstractly, adding no hole.

`lem-sf-fixed-scalar-unit-unique` records the complete normalized scalar identity
comparison for a fixed cochain model, in `FixedScalarUnitUnique`. It transports
the existing package identity comparison abstractly, adding no hole.

`lem-sf-ambient-pushforward-composition-inverse-sections` records the complete
inverse section formula for the selected ambient composition comparison,
in `AmbientPushforwardCompositionSections`. It adds no hole.

`lem-sf-ambient-pushforward-identity-inverse-sections` records the complete
inverse section formula for the selected ambient identity comparison,
in `AmbientPushforwardIdentitySections`. It adds no hole.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
