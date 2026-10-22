## What changed

Filled the three remaining theorem proofs in
`Sheaf.Paper.ModuleRingedToposDerivedComparison`, using the existing declared
normalization lemmas prescribed by the DAG. Added a private proof import of
`Sheaf.Paper.SectionDerivedTensorNormalization`, which publicly imports
`Sheaf.Paper.SectionDerivedPushpullNormalization`.

`derived_homEquiv` specializes the seventh conjunct of
`sectionDerivedPushpullNormalization`; its `normalizationInternalAdjunction` is
definitionally the specified internal derived adjunction.
`delta_comparison` specializes the third conjunct of
`section_derived_tensor_normalization`; its monoidal tensor object is the existing
curried `CondensedRing.derivedTensor` object.
`composition_comparison` specializes the tenth conjunct of
`sectionDerivedPushpullNormalization` at the second morphism.

Added a private componentwise currying construction for the local tensor
comparison natural transformations in the two projection-mate proofs. Its
components are the specified tensor comparisons by reflexivity, avoiding the
identity components inserted by the previous composite of currying isomorphisms.
Added proved private lemmas for cancellation and inversion of tensor-comparison
squares and functor images of isomorphisms. The complete proper and open
projection-mate arguments are proved over general categories in private helpers;
the two public comparison theorems apply them to the normalization equations.
The proper comparison uses the normalization theorem's counit clause directly.
The ordinary open unit square follows from Mathlib's `unit_mateEquiv` and the
proved normalization property of the chosen extension comparison. It no longer
extracts that equation from the broad, still-unproved transport theorem.
A general private adjunction calculation transports the localized unit square
through the fixed right-adjoint isomorphism in `open_homEquiv`.
The ordinary tensor proof identifies the two comparison families by uniqueness,
then simplifies the local coherence proof and goal separately, replacing five
concrete simplifier passes. Direct existential elimination keeps its tensor and
unit witnesses as variables. The final tactic assigns the existing coherence
proof term to the goal directly: Lean's kernel performs the complete conversion
check, without repeating the expensive sheaf-associator conversion in the
elaborator. This uses no additional axiom or unchecked declaration. The complete
module, including this kernel check, compiled in 51.3 seconds with profiling and
a diagnostic 40,000-heartbeat elaboration cap; the delivery restores the normal
existing heartbeat settings and disables profiling.
The open Hom calculation similarly normalizes both its local proof and goal
before applying the resulting equality. These changes avoid repeatedly unfolding
sheaf constructions during categorical rewrites; no proof is postponed to a new
obligation.
A private conjunction lemma reduces repetition of large proposition arguments
in the tensor-normalization proof term. A proved
private lemma transfers one-sided tensor tests through symmetry, so the K-flat
clause uses the concrete signed symmetry only once. The open comparison
helper uses the existing derived-adjunction constants and explicit categories,
with functors inferred from their comparison maps. This avoids rebuilding their
large instance arguments. Local irreducibility guards for `upperStarFromPoint`,
its compositor and monoidal data follow the existing
`CompletedCondensedCoefficients` pattern, keeping the sheaf pullback choices
behind their API during elaboration.
All existing declaration signatures, definitions, global attributes and public
imports are unchanged.
The push-pull and tensor clauses follow the prescribed DAG route. Updated the
node's open clause to match the retained proof's direct localization of the
ordinary open-adjunction unit square. The unit route is preserved; no definition
or statement changes are made. The static command check requests a record for
the proof-local settings and irreducibility attributes; it is supplied as
`coord/changes/B6-module-ringed-derived-proof-settings.md`, including the
downstream consumer check. No downstream modules require adaptation.

## Proved and sorry left

Closed all 3 existing holes, in namespace
`AlgebraicGeometry.ProEtale.ModuleRingedComparison`:

- `derived_homEquiv`.
- `delta_comparison`.
- `composition_comparison`.

There are zero direct holes left in the item and zero holes added or split off.
The proofs use the existing normalization theorems and their DAG nodes:
`sectionDerivedPushpullNormalization`
(`lem-pd-section-derived-pushpull-normalization`) and
`section_derived_tensor_normalization`
(`lem-pd-section-derived-tensor-normalization`). The current push-pull module has
no direct `sorry`; tensor normalization retains its assigned one. This delivery closes
the item from its declared dependencies; it does not claim to finish tensor
normalization or eliminate all transitive uses of `sorryAx`.

## No longer needed

Removed the unused planned proof dependency
`lem-pd-section-derived-open-adjunction-normalization`
(`Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization`) from this node. The
`open_homEquiv` proof uses the normalized ordinary extension comparison and
`Adjunction.mapDerivedCategoryAdjunction_mate` directly. Its module is absent
from the item's transitive import closure. No module is withdrawn.

No original imports were removed. A redundant separate push-pull-normalization
proof import was omitted because tensor normalization publicly imports it.
The ordinary oplax normalization remains needed through tensor normalization.
All other declared dependencies remain needed by the retained ordinary and mate
arguments or by the normalization theorems.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The three missing clauses are
supplied exactly by the existing normalization statements. The DAG's fifth step
still cited a separate derived-open-adjunction normalization theorem even though
the existing Lean proof already localized the ordinary unit square directly. The
revised proof obtains that square from the chosen comparison's proved mate
normalization. The node records this route and removes the unused dependency.
The searches found generic ordinary pullback and adjunction lemmas; the existing project
normalization statements already match the required derived equations.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
