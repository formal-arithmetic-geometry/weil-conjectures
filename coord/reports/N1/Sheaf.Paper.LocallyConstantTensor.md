## What changed

Repair of the returned delivery: the three private helper theorems
`constant_preservesFiniteLimits`, `constant_preservesFiniteColimits`, and
`finite_module_homology` had been stated verbatim in both the item module and
`SiteFiniteFreeTruncationModels`. They are now public reusable declarations in
`SiteFiniteFreeTruncationModels`, and the duplicate declarations were removed
from `LocallyConstantTensor`; its proof imports and uses those declarations.
The target signature and proof result are unchanged.

Replaced the hole in `SheafOfModules.locallyConstantFiniteType_derivedTensor` by a
complete Lean proof from two smaller local interfaces, with its original signature
unchanged. The proof transports the hypotheses to the representatives, intersects two
covering sieves, computes a finite module tensor complex, proves its cohomology finite,
and supplies the covering-slice trivializations required by the definition.

Added four modules, each with its own node:

- `Sheaf.Paper.SiteBoundedTruncationModels`: the bounded constant-model interface in the
  actual ring-sheaf module encoding, for a good lower truncation on covering slices.
- `Sheaf.Paper.SiteFiniteFreeTruncationModels`: proved from the bounded model interface
  and the existing Noetherian pseudo-coherence criterion. The proof explicitly proves
  finite cohomology of the bounded module model and transports a finite-free replacement
  through the exact constant realization and exact slice restriction.
- `Sheaf.Paper.SiteTensorLocalModelComparison`: the comparison between the original
  K-flat tensor and supplied local finite-free models of the relevant good truncations.
  This theorem needs no Noetherianity or local constancy hypothesis.
- `Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`: proved the
  arbitrary-site encoding equivalence, preserving the underlying additive sheaf and
  naturally identifying the two constant-module realizations. This is a proved
  dependency of the bounded-model obligation, adapted from the scheme-specific proof.
  It accepts any locally bijective constant-ring unit, including the restricted unit
  on a slice, so no separate identification of the two ring sheaf constructions is needed.
  It also proves a natural isomorphism between constant realization on the slice and
  restriction of global constant realization, including compatibility with every
  module map. This comparison is available for transporting whole complexes.

The main file also proves, with private helpers, finite generation of each algebraic
tensor term using the finite interval `[i-bF,bE]`, finite generation of its homology
using Noetherian cycles, exactness of the constant presheaf functor by evaluation,
the resulting constant-realization homology comparison, exact restriction of homology,
and invariance of local constant finite type under isomorphism. Updated the original
node's proof route.

All five delivered modules compile together; every single file is
below the 60-second limit. The existing theorem's normalized signature is unchanged.
No existing definition, public signature, target, or unit realization was changed.
The change record `coord/changes/locally-constant-tensor-helper-commands.md` records
the new helper commands flagged by the preflight and lists both unchanged consumers.
Both original consumer files, `Sheaf.Paper.FiniteTensorConstructibleCohomology` and
`Sheaf.Paper.NilpotentReductionLissity`, compile unchanged against the sandbox overlay.

## Proved and sorry left

Closed the original hole:
`SheafOfModules.locallyConstantFiniteType_derivedTensor`
(node `lem-weil-pbc-locally-constant-tensor`). The assigned module has zero holes left.

The repair adds no holes and closes no additional target hole; all three consolidated
helpers are proved and compiled once in their defining module.

Also proved the new theorem
`SheafOfModules.exists_site_finiteFree_truncation_models`
(node `lem-weil-pbc-site-finite-free-truncation-models`). Its module has zero holes.
This proof uses the existing declared theorem
`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`; its existing hole
is unchanged and is an intended proof dependency.

Also proved `CategoryTheory.site_moduleSheaf_constantRing_equivalence`
(node `lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`), including the natural
comparison for constant modules. Its module has zero holes. Its use to transport the
bounded-model theorem is still part of the first obligation below.
The theorem includes the natural slice-realization comparison. Its proof restricts
the module-sheafification unit, uses the adjunction, and proves invertibility after
the conservative additive forgetful functor. Naturality follows from unit naturality.
An explicit `#print axioms` check reports only `propext`, `Classical.choice`, and
`Quot.sound` for this new theorem. Its signature takes the ring-unit local-bijectivity
instances explicitly, so it does not embed the existing unfinished instance proofs.

Added exactly two holes, each the entire proof of a named public theorem:

- `SheafOfModules.exists_site_bounded_truncation_models`
  (`lem-weil-pbc-site-bounded-truncation-models`). Still needs compatibility of the
  proved encoding equivalence with slice restriction, transport of good truncation
  and cohomology, and application of the existing
  `CategoryTheory.exists_site_bounded_constant_model` on slices. It asks only for a
  bounded finite-module model of one truncated factor, and says nothing about tensor
  products or finite-free replacement. The zero complex, an empty slice, and a cutoff
  above the upper cohomological bound all admit the zero model.
- `SheafOfModules.site_tensor_local_model_comparison`
  (`lem-weil-pbc-site-tensor-local-model-comparison`). Still needs the corrected
  truncation-window comparison, exact restriction/tensor comparison, independence of
  the supplied K-flat representatives, and the natural termwise finite-free tensor
  comparison including total-complex signs. Both sides are computed as homology of
  restricted complexes; exact restriction of homology is proved in the main file.
  The local models are hypotheses. It makes
  no finite-generation assertion about cycles and requires no Noetherianity. The bound
  dependent cutoffs and the zero/trivial-model cases were checked mathematically.

This is a decomposition: one original hole closed and two holes added, a net increase
of one among these declarations. It is not an axiom-free proof of the original theorem.
The two remaining statements are separate parts of the source argument; neither is the
original local-constancy conclusion under another name.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`
- `Sheaf.RingTheory.RingPseudoCoherent`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Paper.SiteBoundedConstantModel`
- `Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`

The duplicate helper declarations listed above are also no longer needed in the
assigned module; the imported declarations from `SiteFiniteFreeTruncationModels`
are the sole copies.

The bounded-model, pseudo-coherence, restriction, flatness, descent and tensor work
remains needed inside the new interfaces; those nodes are not claimed globally pruned.
The independent-coefficient/independent-universe wrappers are unnecessary for this
same-universe statement. Good truncation is supplied directly by Mathlib; this proof
uses no truncation-colimit interface.

`lem-weil-pbc-derived-tensor-truncation-window` is unnecessary as a separate interface:
the tensor-comparison obligation includes the window argument directly, using bounded
flat representatives of the removed lower pieces and their tensor term bounds. The
mathematical truncation step is retained; its unavailable separate module is not imported.

The node `def-sfb-site-derived-constant-module-functor` is no longer a proof dependency
of this argument. The delivered proofs construct exactness of the actual constant
realization and use Mathlib's exact-functor derived-category factorization directly.
Removed that obsolete entry from the original node's `tool_uses`, preserving all other
entries and their order. No new maintainer approvals were added.

The unit `sk-thm-properbasechange` and all of its realized statements and steps are
unchanged. The local bounded-model and finite-free route of Tag 094H is retained.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified an import-prune violation: the three
private helper statements were duplicate proofs across the two delivered modules.
Making the helper declarations reusable in `SiteFiniteFreeTruncationModels` and
removing the copies from the item module resolves that violation; the static
import-prune check now exits successfully.

Several node records point to modules absent both from this checkout and from the
compile server's published imports: `DerivedTensorTruncationWindow`,
`SiteDerivedTensorDescentIndependentCoefficients`,
`CommutativeSiteDerivedConstantModuleFunctor`, `LocalizedModuleExactForSystems`, and
`CochainTensorUniverses` (with their recorded namespace prefixes). The attempted import
of the truncation-window module reported a missing object file. The equal-coefficient
`SiteDerivedTensorDescent`, bounded-flat replacement, and exact slice-adjunction
modules are available and were read. The delivery does not edit these records or
manufacture a second declaration with their whole statements.

`SiteBoundedConstantModel` is available but states its result for
`Sheaf J (ModuleCat B)`, whereas the assigned theorem and its local-constant predicate
use `SheafOfModules` over the forgotten constant commutative-ring sheaf. These are
canonically equivalent presentations, not definitionally the same Lean type. The
bounded-model split isolates precisely the necessary transport and localization glue.
The existing scheme-specific module-sheaf equivalence does not directly specialize to
an arbitrary small site. Its argument has been adapted into the new proved arbitrary-site
declaration, with the additional natural constant-module comparison required here.

The source's uniform cutoff `i-1` cannot be used for arbitrarily shifted bounded-above
factors: on the point site take a nonzero field B and both complexes concentrated in
degree 2. Their tensor has nonzero H^4, whereas truncating both below 3 gives zero.
The existing DAG already corrects this to `i-bL` and `i-bK`; both new interfaces
and the compiled proof retain those corrected cutoffs. Finite free replacements are
bounded above, with no lower term bound or finite projective dimension claimed.

The queue's ownership column did not reflect the current claim on
`Sheaf.Paper.SiteLocallyConstantFiniteType`. The claim record showed A4 holds it, so
no edits to that module are included. No other group's module is adapted.

## New nodes

`lem-weil-pbc-site-bounded-truncation-models` is the single-factor bounded finite-module
local-model interface from Tag 094G on slices. Its new module and complete proof in
words distinguish the encoding/relocalization work from the existing module-valued
bounded-model theorem. The remaining work is listed above.

`lem-weil-pbc-site-finite-free-truncation-models` is proved from that interface and the
existing Noetherian criterion (Tag 066E). It retains the same covering sieve and uses
exact realization of the finite-free replacement. No new hole occurs in its module.

`lem-weil-pbc-site-tensor-local-model-comparison` states the truncation and tensor
comparison part of Tag 094H with supplied models, arbitrary coefficient ring, and no
local-constancy conclusion. Algebraic finiteness, the constant homology comparison,
and exact restriction of homology have been removed from this obligation and proved
in the main module.

`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence` is the proved arbitrary-site
encoding equivalence and its constant-module comparison. It supplies the transport
interface used in the proof plan of the bounded-model obligation, including its proved
natural compatibility of constant realization with restriction to a slice. It adds no hole.

Searches were run through `msearch.py` (LeanSearch, LeanFinder, Loogle, and source grep); the exact
queries and real results are recorded in the nodes. Blueprint searches for local
constant models and truncation were checked against the existing bounded-model and
truncation-window nodes. No duplicate of either whole statement is introduced. There
is one change record, `coord/changes/locally-constant-tensor-helper-commands.md`, for
the private-helper scope and notation commands conservatively flagged by the preflight.
It records the existing public signature verbatim before and after, and all consumers;
no existing definition or statement was changed.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
