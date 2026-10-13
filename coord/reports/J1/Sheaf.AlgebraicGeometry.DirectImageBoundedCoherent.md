## What changed

Proved `AlgebraicGeometry.Scheme.directImage_isBounded_coherent`, with its entire
signature unchanged. The proof applies the truncation hypercohomology theorem to
a bounded-below representative. It transports coherence and proper support through
the cohomology comparison; applies coherent proper-support higher direct images;
propagates coherence through the page kernels and cokernels; and reconstructs
coherence from the finite filtration. The full/zero filtration endpoints give the
lower bound. For the upper bound, take the finite maximum of the per-row vanishing
bounds, prove every later page on those diagonals zero, and reconstruct the zero
abutment from its graded pieces.

Added the proved auxiliary module
`Sheaf.AlgebraicGeometry.ProperSupportHigherDirectImageBound`. Its theorem
`AlgebraicGeometry.Scheme.moduleHigherDirectImage_eventually_isZero` presents a
coherent module as the pushforward from a closed subscheme proper over the base.
Affine derived cohomology and the standard heart equivalence identify the derived
pushforward of its degree-zero complex with the original module in degree zero.
Derived composition and the uniform qcqs bound then prove eventual vanishing.
All constructions and extracted witnesses are local to theorem proofs.

Repair of the returned delivery: removed the duplicate private theorem
`AlgebraicGeometry.Scheme.property_of_filtration`. Added the proof-only
`import all Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh` and
applied its existing `AlgebraicGeometry.property_of_filtration` directly.
`import all` makes the private helper available without changing its visibility
or adapting its module. The auxiliary module likewise removes its duplicate
`AlgebraicGeometry.Scheme.qc_single`, imports
`Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact` with `import all`,
and applies the existing `AlgebraicGeometry.qc_single`. Both DAG records now
name the modules providing these reused helpers. The second-reading section below predates this repair
and will need the second reader to recheck the changed import and application.

Added proof-only imports of coherent closure, the ordinary direct-image/Grothendieck
interface, the new bound module, and integer finite intervals. Moved the uniform
bound import to the auxiliary module. No public import of the original module and
no existing statement or definition changed. Updated its node's proof, proof_deps
and proof_origin to reflect this route. No forced adaptations.

Second-reader repair: removed the remaining copied finite-filtration zero theorem
and page-vanishing induction. The upper bound now specializes the already imported
`AlgebraicGeometry.property_of_filtration` to `IsZero`, using Mathlib
`ShortComplex.Exact.isZero_of_both_isZero` for extension closure. It reuses
`BigradedExactCouple.page_zero` through a proof-only `import all` of
`Sheaf.CategoryTheory.HalfPlaneWeakConvergence`. Removed the auxiliary module's
unused proof import `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
Updated the original node's upper-bound step and dependency record accordingly.

Both modules compile with no warnings.
The source statements and arguments were checked at Stacks
[08E2](https://stacks.math.columbia.edu/tag/08E2),
[0CYS](https://stacks.math.columbia.edu/tag/0CYS), and
[08D5](https://stacks.math.columbia.edu/tag/08D5).

## Proved and sorry left

Original holes closed: 1, in
`AlgebraicGeometry.Scheme.directImage_isBounded_coherent`
(node `lem-pc-direct-image-bounded-coherent`).

New holes added: 0. The new theorem
`AlgebraicGeometry.Scheme.moduleHigherDirectImage_eventually_isZero`
(node `lem-pc-proper-support-module-higher-direct-image-bound`) is also proved.
No declaration in either delivered module contains `sorry`. These are proofs from
existing DAG declarations, some of which still depend on `sorry`; this is not a
claim that the target's complete axiom closure is now sorry-free.

The reused filtration, degree-zero quasi-coherence, and pointwise page-vanishing
helpers are fully proved. The remaining private page-coherence helper has no direct hole. The integer interval may be empty or
contain negative degrees: its natural-valued supremum defaults to zero and uses
N(q) + q.toNat as a conservative total-degree bound. Empty support and zero
coefficients are included. Independent source and target derived-category
universes of the original theorem remain unchanged; the auxiliary theorem has
no derived-category hypothesis and uses standard derived categories internally.

## No longer needed

Removed the original proof import
`Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction`, node
`lem-pc-direct-image-qc-support-reduction`. The proof never needs to restrict the
whole complex to one quasi-compact open. Removed the original direct import of
`Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound` from the item's
module; it remains used by the auxiliary theorem and is NOT globally pruned.

A source-import reachability comparison from this item, before/after the delivered
overlay, finds the following library modules no longer reachable by this item's
proof. This is local pruning; another target path may still need them:

- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen` — `lem-sc-derived-k-injective-restrict-open`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside` — `lem-sc-module-extension-by-zero-stalk-maps-inside`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps` — `lem-sc-module-extension-by-zero-stalk-maps`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMorphism` — `lem-sc-module-extension-by-zero-stalk-morphism`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitionCoherence` — `new-module-extension-by-zero-coherence`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitions` — `lem-sc-module-extension-by-zero-stalk-maps-transitions`
- `Sheaf.Algebra.Homology.ModuleRestrictionStalkComponents` — `new-module-restriction-stalk-components`
- `Sheaf.Algebra.Homology.ModuleRestrictionStalkLinear` — `lem-sc-module-restriction-stalk-linear`
- `Sheaf.Algebra.Homology.ModuleRestrictionStalkNaturality` — `new-module-restriction-stalk-naturality`
- `Sheaf.Algebra.Homology.OpenExtensionRestrictionIso` — `lem-pc-open-extension-restriction-iso`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage` — `lem-weil-pbc-closed-subset-proper-over-base-union-preimage`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperUniversallyClosedImage` — `lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` — `lem-pc-restrict-derived-direct-image-open`
- `Sheaf.AlgebraicGeometry.DerivedOpenLocalization` — `lem-pc-derived-open-localization-universe`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh` — `lem-pc-derived-open-restriction-qcoh-iff`
- `Sheaf.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover` — `lem-pc-derived-restriction-isIso-open-cover`
- `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` — `lem-pc-direct-image-qc-support-reduction`
- `Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen` — `def-pc-perfect-classes-small-on-open`
- `Sheaf.AlgebraicGeometry.PerfectGluingEndpointProperties` — `def-perfect-gluing-endpoint-properties`
- `Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall` — `lem-perfect-restriction-classes-small`
- `Sheaf.AlgebraicGeometry.ProperCoproduct` — `lem-weil-pbc-proper-coproduct`
- `Sheaf.AlgebraicGeometry.SupportedDerivedRestrictionZero` — `lem-pc-supported-derived-restriction-zero`
- `Sheaf.AlgebraicGeometry.SupportedOpenPushforward` — `lem-pc-supported-open-pushforward`
- `Sheaf.AlgebraicGeometry.SupportedOpenPushforwardComplementZero` — `lem-pc-supported-open-pushforward-complement-zero`
- `Sheaf.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons` — `lem-pc-supported-open-pushforward-local-comparisons-second`, `lem-pc-supported-open-pushforward-local-comparisons`, `lem-pc-supported-open-pushforward-local-comparisons-first`
- `Sheaf.AlgebraicGeometry.SupportedOpenPushforwardPerfectComponent` — `lem-pc-supported-open-pushforward-perfect-component`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`

No nodes are deleted. The pruning list was recomputed after adding the repair import,
including Mathlib transitive imports. No other original proof dependency is claimed pruned. The unused auxiliary proof import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` was also removed;
that module is still reachable through other imports and is not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The planned whole-complex support-reduction theorem has a stronger formal
interface than this item: it assumes derived-category instances at a common
universe for every scheme. This item has only instances for X and S, with
independent universes. Rather than changing that interface or a target statement,
the upper-bound argument applies proper-support reduction separately to each
cohomology module; only finitely many rows matter. The uniform bound still
appears in the resulting proof, on a genuinely proper closed subscheme.

The generic quasi-coherent direct-image spectral-sequence proof already in
`DerivedDirectImageBoundedBelowQCoh` provided the finite-filtration proof pattern.
The earlier claim that its private helpers cannot be imported was wrong:
Lean module-system `import all` exposes them to the importing proof. The repair
reuses the existing generic filtration theorem and removes the duplicate proof.
The DAG now records the module containing that helper as a proof dependency;
its geometric quasi-coherence theorem itself is not applied.

## New nodes

`lem-pc-proper-support-module-higher-direct-image-bound`, in
`dag/nodes/sec-picard-framework/`, records eventual ordinary higher-direct-image
vanishing for one coherent module with proper support. This is a strictly smaller
sheaf-level argument, and its Lean theorem is proved. It uses the proper-support
presentation, coherent/finite-type comparison, affine derived cohomology,
derived-image composition, and the existing uniform truncation bound. Its
blueprint ancestor is `lem-sc-finite-duality`, through this item's node.
LeanSearch was unavailable; LeanFinder returned generic t-structure/Ext lemmas;
Mathlib grep and the blueprint search found no exact match. No change record is
needed because no existing signature, definition or visibility changed.

## Earlier second reading (a previous round; superseded)

1. **Interface and scope — pass.** Read the full diff against the repository's
   `DirectImageBoundedCoherent.lean`. Extracted the text from `theorem
   directImage_isBounded_coherent` through its conclusion and checked byte-for-byte
   equality: the Noetherian base, locally finite type morphism, independent derived
   universes, boundedness, coherence, proper support, and both conclusions are
   unchanged. Existing public imports are unchanged. The other delivered module is
   new; there are no adapted modules or changed definitions and no change record is
   required.

2. **Proof and axioms — pass.** Compiled both delivered modules together with
   `lcompile.py --all`: clean, 10.7 and 31.9 seconds respectively. Compiled scratch
   copies with `#print axioms` for both public theorems and all five private helpers.
   The two public theorems and `coherent_pages` use only `propext`, `Classical.choice`,
   `Quot.sound`, and inherited `sorryAx`; the other four helpers use only the three
   permitted axioms. No delivered declaration has a direct `sorry`, and no forbidden
   declaration or kernel-check bypass occurs. In particular there is no definition
   hiding a chosen witness: the presentation, representative, comparison objects,
   and numerical bounds are eliminated locally inside proofs of propositions.

3. **Auxiliary statement — pass; no split-off holes.** Independently read Stacks
   [08E2](https://stacks.math.columbia.edu/tag/08E2),
   [0CYS](https://stacks.math.columbia.edu/tag/0CYS), and
   [08D5](https://stacks.math.columbia.edu/tag/08D5). The new sheaf-level theorem
   is strictly smaller than the bounded-complex theorem and is proved, not a
   restatement left open. Local finite type over the Noetherian base gives the
   locally Noetherian source needed to turn coherence into finite type and
   quasi-coherence. Checked the actual `module_support_proper_over_base` statement:
   it supplies exactly the closed immersion, proper composite, quasi-coherent G,
   and module isomorphism used. The affine comparison and heart equivalence identify
   Ri_*G[0] with M[0]; composition and the ordinary right-derived comparison give
   the required vanishing. Properness supplies qcqs, and Noetherian S supplies
   compactness for the uniform bound. Negative derived degrees of G[0] and positive
   ones are both zero; the bound uses N.toNat with 0 < N. The zero module, empty
   support/base, an affine identity, and a non-quasi-compact X do not invalidate
   any step: only the proper presentation is required to be quasi-compact.
   Repeated searches with `msearch.py` using "cohomological dimension" and
   "rightDerived proper" (grep), "finite cohomological dimension of a proper
   morphism" (LeanFinder), and `Functor.rightDerived, Limits.IsZero` (Loogle;
   identifier unresolved) found no exact replacement. Also searched project
   sources for eventual higher-image bounds and single-object quasi-coherence.
   The existing local uniform bound requires an additional finite-cover argument;
   the upstream base-change bound is still open and requires a composition
   comparison as well. The private `qc_single` helper in
   `AffineDerivedPushforwardTExact` is not importable. No duplicate public theorem
   or new unproved statement was introduced.

4. **Route and pruning — pass.** Read the spectral-sequence proof from its top
   declaration downward. Support and coherence are transported along the actual
   homology isomorphism; coherence of later pages follows from kernels and
   cokernels, and the finite filtration uses extension closure. The lower endpoint
   argument makes the filtration simultaneously full and zero below a. For the
   upper bound checked the inequality q <= q.toNat and the finite supremum of
   N(q)+q.toNat: outside [a,b] coefficient vanishing applies; inside it the first
   index reaches N(q). Negative first indices vanish separately. Zero page entries
   remain zero by subquotients; finite filtration endpoints then force the abutment
   zero. This also covers a > b and all-negative [a,b]. All newly added imports are
   proof imports except those needed by the auxiliary statement and its instances.
   Recomputed source-import reachability with the delivered overlay: the full
   removal set agrees exactly with `scratchpad/pruned.json` and `## No longer
   needed`. The old support-reduction dependency is absent; the old uniform-bound
   dependency remains used through the auxiliary module and is correctly not
   claimed globally pruned. Read `dag/units/sk-thm-picard-duality.json`: neither
   modified node is a realized unit statement or step; the unit's route is kept.

5. **DAG — pass.** Read both node files and the Lean declarations of their cited
   dependencies. For each node checked that `proof_deps` is exactly the union of
   the proof steps' `uses`. The original node records the spectral sequence,
   coherent higher images, coherent closure, and finite-row bound actually used.
   The auxiliary node records the coherent/finite-type equivalence, proper-support
   presentation, affine cohomology, composition, and uniform truncation bound
   actually used. Its natural-number statement matches Lean, and its source,
   searches, ancestry, chapter, unit, creation, and Lean records are present.

Changes by the second reader: added this independent review and search evidence
only. No Lean proof, signature, definition, import, or DAG repair was needed.
Scratch axiom probes were removed before delivery. Holes closed remain 1 original
hole, holes added 0; no split-off holes remain.


## Second reading by J1

1. **Interfaces — pass.** Compared the delivered main module with the repository
   using `diff`, and separately compared the complete text of
   `directImage_isBounded_coherent` from `theorem` through its conclusion:
   byte-for-byte identical. Its Noetherian base, locally finite type morphism,
   independent source/target derived universes, boundedness, coherence, proper
   support, and both conclusions are preserved. All original public imports remain.
   The auxiliary module is new; no existing definition, signature, visibility,
   target, or other claimed module is changed. No change record is required.

2. **Proofs and axioms — pass after repair.** Read both proofs and all helpers.
   Compiled both modules and scratch copies with `#print axioms` for both public
   theorems and the remaining private `coherent_pages`. Their axiom sets are
   contained in `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`.
   Source scans find no direct `sorry`, axiom, unsafe/opaque declaration, external
   implementation, or kernel-check bypass. All witnesses and bounds are local
   inside proofs of propositions; no definition chooses arbitrary data from an
   unproved existence theorem. This closes one original hole, adds none, and does
   not assert that the transitive proof closure is sorry-free.

3. **Auxiliary statement and searches — pass.** Read the statements and proofs of
   [Stacks 08E2](https://stacks.math.columbia.edu/tag/08E2),
   [0CYS](https://stacks.math.columbia.edu/tag/0CYS), and
   [08D5](https://stacks.math.columbia.edu/tag/08D5).
   The sheaf-level vanishing theorem is a proved, strictly smaller ingredient.
   Local finite type over Noetherian S gives locally Noetherian X; coherence gives
   the quasi-coherence and finite type needed by the actual support-presentation
   declaration. The affine comparison, heart equivalence, and composition identify
   Rg_*G[0] with Rf_*M[0]; the proper g supplies qcqs and S supplies compactness.
   The positive integer bound converts correctly to a natural bound. Checked zero
   M, empty support/base, an identity morphism, and non-quasi-compact X: only its
   proper presentation needs quasi-compactness. Repeated msearch queries with
   `cohomology.*proper|proper.*cohomology` (grep), `higher direct image coherent
   module proper support finite vanishing bound` (LeanFinder) found no replacement.
   Loogle found `ShortComplex.Exact.isZero_of_both_isZero`, now used. Project searches
   found two remaining copied helpers, repaired below. There are no split-off holes.

4. **Route, imports, pruning — pass after repair.** Read from the target downward.
   Homology isomorphisms transport actual coherence and stalk support; kernels and
   cokernels propagate coherent pages; finite filtrations reconstruct coherence and
   vanishing. The maximum of N(q)+q.toNat handles negative q, empty [a,b], and a>b;
   outside [a,b] the coefficient is zero. The existing generic filtration theorem
   works with the actual full step 0 and zero step max(0,n-a+1), including n<a.
   Reused both repaired `import all` helpers from the first worker and removed two
   further duplicates: `isZero_of_finite_filtration` already in
   `DegreewiseFilteredAcyclic`, and the page-vanishing induction already in
   `HalfPlaneWeakConvergence`. The first is replaced by the generic filtration
   theorem specialized to IsZero; the second by the existing pointwise page_zero.
   Removed the now-unused auxiliary quasi-coherence proof import. New imports are
   proof-only; no public import supplies merely proof machinery. Recomputed source
   reachability including Mathlib: the 28-module pruning list remains exact.
   The old support-reduction dependency is removed; the old uniform-bound dependency
   remains through the auxiliary module. Read `sk-thm-picard-duality.json`: these
   changes bypass no realized unit statement or step, and its route is unchanged.

5. **DAG — pass after repair.** Read both records and the Lean declarations they
   cite. Original statement fields remain unchanged; the new theorem's recorded
   signature matches its Lean text. Both `proof_deps` sets equal the unions of their
   steps' `uses`. Updated the upper-bound step to record both the generic filtration
   helper and the pointwise page-zero helper, explicitly distinguishing those helpers
   from their modules' geometric/convergence theorems. Added the latter's node to
   proof_deps and updated proof_origin. The new node retains source, searches,
   ancestry, chapter/unit, creation, and Lean records required by the standing brief.

Changes by this second reader: removed two duplicated private helpers; reused the
existing generic filtration and pointwise page-zero theorems; removed one unused
proof import; updated the original node's proof route and this report. Existing
statements and definitions are untouched. Proved and sorry left remains one
original hole closed (`AlgebraicGeometry.Scheme.directImage_isBounded_coherent`),
zero holes added, zero split-off holes; the new auxiliary theorem is also proved.
