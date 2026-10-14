## What changed

Replaced the hole in `AlgebraicGeometry.affineDirectLocalizedTensorSquare_core` by a
composition of two localization squares, keeping its statement unchanged. The proof
constructs the intermediate tensor coefficient map from the actual stalk maps,
proves both restrictions, and supplies the scalar towers. First-factor localization
uses `derivedTensor_first_localization_models`. The existing affine stalk coordinates
and `exists_baseDerivedTensorModel_quasiIso_comparison` transport the localized input
complex to the actual stalk complex. Private degreewise scalar-composition and tensor-coefficient definitions keep
large constructions abstract, with proved generator and restriction APIs. A generic
functoriality lemma composes squares without unfolding derived-model definitions.
Tensor associativity and equal-map transport
supply the coefficient chain isomorphism and its generator formula. The proof composes
the resulting square with the remaining base and second-factor square for every
supplied final chain isomorphism, cancelling beta with its inverse on the chain maps.

Added `Sheaf.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison`, stating only
the second half: its input is already the A-stalk complex, with a model over the
original base and second ring. It has no original model `n`, and proves no
first-factor localization. Its remaining proof includes comparison with the standard
stalk derived-category universes. Both module statements, their node records, and the
source Tags 0DJ8 and 06Y6 were read. The unit's realized statement/step lists are empty;
this refinement preserves the affine localization route within that unit.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.affineDirectLocalizedTensorSquare_core`
(node `new-affine-direct-localized-tensor-square-core`). Its proof body has no `sorry`.

Added one strictly smaller remaining hole:
`AlgebraicGeometry.exists_affineStalkBaseSecondLocalizationComparison`
(node `new-affine-stalk-base-second-localization-comparison`). This is a decomposition:
one upper hole closed and one lower hole added. These are declaration counts, not
a claim about the closure ledger. The first-factor
localization, coefficient-map construction, tilde/stalk transport, and composition
of the two comparison squares are written in Lean. The existing model constructors
are used; no new object is defined by selecting an unspecified existence witness.
No other new or remaining hole is delivered.

## No longer needed

Removed the unnecessarily broad public import of AffineBaseChangeTildeCoordinates
from the new theorem module, replacing it by the statement APIs
SingleComplexBaseChangeStalkCondition and Mathlib.AlgebraicGeometry.Modules.Tilde.
Removed the direct proof import
`Sheaf.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels` from the item.
It is also omitted from the new module: its hole does not use that import yet.
Node `lem-pc-derived-tensor-base-second-localization-models` is no longer a
direct proof dependency of the item; it remains a dependency of the new
second-half node. No entire dependency module is claimed pruned from the closure. The first localization and affine
stalk-coordinate nodes remain needed. Added the existing quasi-isomorphism model
comparison to the route. No blueprint unit or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan's two algebraic localization declarations require a common
derived-category universe. The item instead compares a supplied universe `wM` with
the standard stalk universe. It also needs explicit transport from the localization
of the module complex to the tilde stalk complex. The latter transport is now done
using the existing quasi-isomorphism comparison theorem; the former is isolated in
the base/second-factor lemma, rather than pretending that its models match directly.

The first localization scalar towers and tensor coefficient map cannot simply be
inferred from the affine square; the proof constructs them and proves their required
restriction equalities. Edge cases: zero complexes and identity localizations use
the same maps; a zero upper-left ring has no prime. The new statement imposes no
flatness of A over R or K-flatness of M, and does not assert invertibility of a
localized comparison map.

Searches: Lean Finder found spectrum-stalk/localization APIs, Loogle found
`ModuleCat.ExtendScalars.hom_ext`, and Mathlib grep found tensor-associativity and
homology-composition lemmas. LeanSearch returned Internal Server Error, recorded as
unavailable. Library searches found the two localization declarations, affine stalk
coordinates, and quasi-isomorphism model comparison used here; none directly handles
this base/second affine comparison across the two universe instances.

First-worker validation: the main module compiled through `lcompile.py` (56.5 s).
Second-reader validation and performance repair are recorded below.
Its original theorem signature is textually identical, and the new module contains
exactly one named theorem hole; the main module contains none.

## New nodes

`new-affine-stalk-base-second-localization-comparison` is the base and second-factor
localization step after the A-stalk input has been fixed. The statement, complete
proof in words, actual search records, and Lean signature are in its new DAG record.
It is strictly part of the original argument: the main proof must separately prove
first-factor localization and tilde/stalk transport, then compose the squares.
There are no existing statement changes or forced adaptations. The change record
`coord/changes/H4-affine-direct-local-tensor-instance.md` documents the local
Mathlib tensor-product instance command flagged by the static interface check.


## Earlier second reading (a previous round; superseded)

1. Compared the delivered core module and node against the repository versions.
   The original `AlgebraicGeometry.affineDirectLocalizedTensorSquare_core`
   signature is byte-for-byte identical. All added helpers are private;
   the tensor-product instance attribute is local. The existing public import
   is unchanged and all added proof imports are plain imports. No target,
   existing definition, visibility, or external statement changed. Verdict: pass.
2. Read the coefficient lift, its restrictions, scalar towers, scalar-composition
   and equality transports, first localization, stalk coordinates, model comparison,
   and final functorial square composition. The only delivered textual hole is
   `AlgebraicGeometry.exists_affineStalkBaseSecondLocalizationComparison`.
   No prohibited declarations or hollow definitions occur. Intermediate models
   use the established universal-counit model constructor: their cohomology,
   actions and comparisons are determined up to the isomorphisms used downstream.
   The initial repeated 60-second timeouts required a proof-performance repair:
   the tactic body finished, but the expanded model-dependent homology calculation
   was too expensive. The final local compilation and axiom checks are recorded below.
3. Read the new theorem, its complete proof docstring and DAG record, and checked
   Stacks Tags [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) and
   [06Y6](https://stacks.math.columbia.edu/tag/06Y6). Zero complexes, identity
   localizations, and a zero A' (no prime) cause no exception. The beta hypothesis
   guarantees that the indicated germs generate the intermediate extended complex;
   D-linearity extends the numerator formula to all tensors. The theorem holds
   the A-stalk input fixed and omits the original model n, so it is a strict
   base/second-factor subargument, not a renamed original hole. Independent
   Lean Finder search for universal derived-functor comparison found
   `Functor.leftDerivedUnique`; Loogle's attempted `Functor.IsLeftDerivedFunctor`
   identifier query had no hits; the fully qualified
   `CategoryTheory.Functor.leftDerivedUnique` query found the uniqueness API.
   Mathlib grep independently found that same API. Library
   searches found `exists_baseDerivedTensor_restricted_ring_comparison`, which
   handles distinct derived-category universes but still requires the separate
   localization and scalar-action transport. No existing declaration immediately
   closes this affine theorem. Verdict: acceptable decomposition, zero net holes
   closed by declaration count, not a completed proof of the import closure.
4. Checked the imported first-localization and quasi-isomorphism comparison
   declarations and affine stalk-coordinate API. No shorter direct application
   handles all remaining scalar actions and coefficient rings. The unchanged
   unit `sk-thm-picard-semicon` has empty realized statement and step lists;
   the affine localization route is preserved. The removed direct dependency
   and its retained role below the new node are explicitly listed in
   No longer needed. Verdict: pass; no entire closure module claimed pruned.
5. Compared the main node's proof steps and proof_deps with the actual Lean calls.
   The new node has its verbatim signature, source, searches, creation record,
   blueprint ancestry, chapter and unit. Repaired its universe-comparison step
   to use the existing restricted-ring comparison with identity equivalences,
   followed by tensor induction and localized_eq, rather than leaving that
   step attached only to a model-definition node. Verdict: pass after repair.

Second-reading changes: gave both intermediate model bindings explicit types
and kept their existing universal model constructor behind a private irreducible
definition to reduce elaboration work; replaced the large first-square
homology rewrite block by a proved generic categorical transport lemma; clarified the remaining theorem's
universe-comparison proof docstring and matching DAG dependency; completed the
pruning report; narrowed the new theorem module's public imports to
SingleComplexBaseChangeStalkCondition and Mathlib Tilde, the APIs its statement uses.
No theorem signature or construction changed, and no additional
hole was added. Closing the remaining theorem would require substantial scalar
and model transport, so it was not replaced by further holes.


Second-reader validation: `lcompile.py --all` compiled the new theorem (11.1 s),
the repaired core (51.7 s), a temporary unchanged copy of its sole direct importer
`Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquare` (8.6 s), and a temporary
axiom-printing module (1.5 s). Both reviewed declarations printed exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The single unused
`Category.assoc` simp argument reported in the new private helper was removed.
Temporary review sources were removed before delivery; no downstream file is
part of the delivery. The delivery tool's per-declaration axiom probes and
warning-free compile are the final gate.


## Second reading by H4

1. **Interface preservation — pass.** Read the complete diff of the core module
   and its existing node against the repository. Independently compared the original
   theorem signature byte for byte: identical. The added helpers are private;
   the tensor-product instance attribute is local. No existing definition,
   statement, visibility, or target changed. The original public import remains
   necessary for the original signature; added proof imports are plain imports.
   The change record correctly describes the local attribute and no forced adaptation.
2. **Proof and trust — pass as a decomposition.** Read the tensor coefficient
   lift and its restriction equations, scalar towers, coefficient associativity,
   equal-map transport, first-localization square, stalk coordinates, quasi-isomorphism
   transport, and both categorical square-composition lemmas. All new definitions
   are actual constructions. The intermediate models use the existing universal
   derived-counit model API, which determines their cohomology, scalar action,
   and comparisons up to the isomorphisms used here; no arbitrary existence witness
   is introduced. Fresh `lcompile.py --all` compiled the new theorem module in
   11.2 seconds and the core in 56.3 seconds, without warnings. A temporary
   axiom-printing module compiled in 1.7 seconds: both public declarations use
   exactly propext, Classical.choice, Quot.sound, and sorryAx. The unchanged
   sole direct importer compiled against the sandbox overlay in 9.0 seconds.
   The sole delivered textual hole is
   `AlgebraicGeometry.exists_affineStalkBaseSecondLocalizationComparison`;
   there are no prohibited declarations or holes in definitions.
3. **Remaining statement — pass.** Read its entire signature, proof docstring,
   and new node. Checked the affine localization identity in
   [Stacks Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) and independence
   of K-flat derived computations in
   [Stacks Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6).
   Localization of R and R' leaves the already localized Aq input fixed;
   the psi restrictions fix both coefficient actions. The beta hypothesis
   makes equality on the indicated germs sufficient: precompose with beta,
   use the generators 1 tensor x of D tensor_A M, and cancel beta.
   Zero complexes and identity localizations obey the same identities; zero A'
   has no prime. No flatness or comparison invertibility hypothesis is missing.
   This assertion omits the original model n and first-factor localization,
   so it is strictly part of the argument, not a renamed original hole.
   Independent Lean Finder search for derived extension/localization independent
   of derived-category universe returned general derived localization APIs;
   Loogle and Mathlib grep found Functor.leftDerivedUnique. Repository searches
   also found the proved ordinary-ring and restricted-ring comparison APIs;
   these still require localization and localized-counit transport and do not
   directly close this affine assertion. It cannot be closed in a few minutes
   by an existing direct application; no further holes were introduced.
4. **Route and pruning — pass.** The proof uses the existing first-localization,
   affine stalk-coordinate, and quasi-isomorphism comparison declarations.
   The old base/second-localization dependency is absent from the core's direct
   proof_deps and remains in the new node's plan, as No longer needed says.
   No entire module is claimed pruned from the target closure. All delivered
   imports have a statement or proof role. The unit sk-thm-picard-semicon has
   empty realized statement and step lists, and its affine localization route
   is retained. One original hole is closed and one lower hole added: this is
   a decomposition, with zero net holes closed by declaration count, not a
   completed proof of the target import closure.
5. **DAG agreement — pass.** Both node signatures occur verbatim in their Lean
   sources. The proof_deps of each are exactly the union of its proof-step uses.
   The core node follows the actual coefficient lift, first-localization,
   stalk transport, and final square composition. The new node records its
   source, full mathematical argument, searches, creation, blueprint ancestry,
   chapter, unit, and Lean attachment. Its restricted-ring comparison dependency
   supports the stated universe transport.

Changes in this second reading: appended this independent review and fresh
validation results; removed the leftover generated probe and the temporary
axiom-check and unchanged-importer sources. No delivered Lean proof, signature,
node, or change record required repair. The earlier second-reading section is
historical and its repairs were already present when this reading started.
