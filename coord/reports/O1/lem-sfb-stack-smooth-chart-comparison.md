## Worker report

O1 states `lem-sfb-stack-smooth-chart-comparison` in
`lean/Sheaf/AlgebraicGeometry/StackSmoothChartComparison.lean`. Three named theorems have
exactly `sorry` proofs. The two chart predicates have real Prop-valued definitions.
The natural-language statement and accepted proof are unchanged. Six definition dependencies
are added for locality and the existing interfaces actually used. The H2 repair replaces
the two theorem-owner citations with their exact definition owners.

Sources read: Stacks `stacks-morphisms.tex`, lemma-local-source-target (06FM), including
its proof and final representable paragraph; `spaces-descent.tex`,
definition-local-source-target (06F8), all three clauses. The source and node use smooth
vertical maps in both conditions, comparison smoothness only in (A), and source
surjectivity only in (B). The node's scheme-chart strengthening is the cycle of atlas
refinements already in its proof. Its étale/fppf convention is retained via the existing
DM definition and the recorded étale-smooth-atlas descent proof dependency.

Hypothesis and clause correspondence:

- Base scheme: `{S : Scheme.{u}}`; spaces are the existing `AlgebraicSpace S`.
- A property of ordinary space morphisms: `P : MorphismProperty (AlgebraicSpace S)`.
  Isomorphism invariance is `[P.RespectsIso]`, rather than a predicate on chosen charts.
- Smooth locality: `hP : IsSmoothLocalOnSourceAndTarget P`. Its definition has exactly
  three conjuncts: smooth precomposition, smooth base change, and the pointwise iff.
  The first quantifies `f`, `g` and concludes `P (f ≫ g)`; the second quantifies an
  actual `IsPullback a f' f b` and concludes `P f'`. This permits every presentation
  of the fibre product, with no extra chosen pullback or existence assumption.
- In locality clause (iii), `r : X ⟶ Y` and `x : Point X.obj.obj` are arbitrary.
  Existential `U,V,a,b,h` satisfy `a ≫ r = h ≫ b`, both `MapIsLocally @Smooth`
  tests, `x ∈ pointImage a.hom.hom`, and `P h`. Membership is precisely existence of
  a source point class over `x`: `pointImage` uses field representatives modulo common
  extensions. Thus the existential point `u` has not been replaced by a rational lift
  over the original field. All three source clauses are present in the new definition.
- The stack morphism is `f : BasedFunctor F G`; `F` and `G` have independent object
  and morphism universes. `hF`, `hG` are `IsDeligneMumfordModuliStack` for those very
  based categories. There are no genus, level, finite-type or separatedness restrictions.
- In each chart predicate, `U,V : AlgebraicSpace S`, with actual maps
  `a : BasedFunctor (discreteModuli U.obj.obj) F`, `b` to `G`, and `h : U ⟶ V`.
  The specified based natural isomorphism
  `a.comp f ≅ (discreteModuliMap h.hom.hom).comp b` is the 2-commutative square.
  Mathlib's based natural isomorphisms are precisely natural isomorphisms over
  identity maps of the base, the same data as `ModuliTwoIso`.
- The vertical maps are smooth representable maps: `ModuliSpaceTest @Smooth a`
  and `ModuliSpaceTest @Smooth b`. This existing test quantifies all scheme base
  changes, supplies their actual algebraic-space projection and tests every étale
  scheme chart. In particular representability is part of the test, not omitted.
- (A) is `SmoothChartAll P (fun _ ↦ True) f`. It universally quantifies each
  diagram and its specified isomorphism `e`; the extra hypothesis is exactly
  `ModuliSpaceTest @Smooth (moduliTwoFiberLift a (discreteModuliMap h.hom.hom) e)`.
  This canonical functor sends an object to its two images and `e`'s comparison,
  retaining the actual induced map into the 2-fibre product. The conclusion is `P h`.
- (B) is `SmoothChartSome P (fun _ ↦ True) f`: existence of this diagram, smooth
  `a,b`, `IsSurjectiveModuliMap a`, and `P h`. It does not assume comparison
  smoothness or surjectivity of `b`. The existing surjectivity predicate is lifting
  after a field extension, with an isomorphism to the restricted target object.
- Scheme charts are the class `fun U ↦ U.obj.obj.IsRepresentable` in the same two
  predicates. A presheaf on `Over S` is representable exactly when it is isomorphic
  to `yoneda.obj T` for an `S`-scheme `T`. Thus these are actual scheme charts,
  allowing replacement by an isomorphic representable sheaf. Isomorphism invariance
  ensures this representation-independent formulation has exactly the node's meaning.
- `stack_smooth_chart_comparison` gives the conjunction `A_sp ↔ B_sp`,
  `A_sp ↔ A_sch`, and `B_sp ↔ B_sch`. This states equivalence of all four conditions.
- `space_smooth_chart_comparison` takes the ordinary map `r : X ⟶ Y` and its actual
  functor `discreteModuliMap r.hom.hom`; it explicitly gives each of the four
  chart conditions iff `P r`. No stack hypothesis is imposed on ordinary spaces.
- The additional arbitrary-base-change hypothesis is `[P.IsStableUnderBaseChange]`.
  `hfppf` is the iff for every target-cover family `b` satisfying `IsFppfCover b`:
  `P r` iff every actual pullback projection `q` has `P`. All pullback squares are
  quantified through `IsPullback`, not an unconstrained substitute projection.
  Cover indices range over the ambient site bound `Type (u+1)` (schemes and spaces
  are built over `Scheme.{u}`); there is no finite/nonempty index restriction.
  The existing cover definition uses chartwise flatness and local finite presentation
  and joint surjectivity on field-valued points, agreeing with the node's scheme test.
- `hf : IsRepresentableByAlgebraicSpaces f` is exactly the extra representability.
  The final iff quantifies every scheme `T : Over S`, map `t : h_T → G`, and every
  algebraic-space presentation `HasSpaceBaseChange f T t Z p`. Its conclusion is
  `P (ObjectProperty.homMk (⟨p⟩ : Z.obj ⟶ (schemeSpace T).obj))`: the specified
  projection to the actual Yoneda scheme space. No arbitrary map or existential
  choice replaces this canonical projection. Quantifying all presentations rather
  than choosing one is equivalent by `[P.RespectsIso]`. The main theorem also
  identifies this condition with (B) and both scheme-chart conditions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`, `ModuliTwoIso`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`, `IsDeligneMumfordModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, the sheaf/full-subcategory
  morphisms, `IsEtale`, and the chart representation convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: ordinary pullbacks;
  the categorical `IsPullback` expresses arbitrary space pullback presentations.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`, through the existing space API.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`, `PointRepresentative.Rel`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `moduliTwoFiberLift`.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsSurjectiveModuliMap` and the smooth/étale permanence proof statements.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus`: `IsFppfCover`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`.
- Plain proof imports include `EtaleSmoothAtlasFppfDescent` and
  `AlgebraicSpaceFibreProductsEtaleCovers`. The proof-only nodes
  `lem-sfb-dm-etale-atlas-calculus` and `lem-sfb-representable-pullback-over-space`
  have no recorded Lean module in the read clone, so there is no module to import
  for them. Their statements are not needed to type this delivery's statement.

Edge cases checked: empty source forces the locality detection condition to hold
vacuously, so the definition correctly forces `P(empty → Y)`. Empty chart members
are allowed; no chart index or chart space is assumed nonempty. Empty fppf index
sets are allowed by `IsFppfCover`, with its joint-surjectivity condition. Identity
vertical maps recover the ordinary-space assertion. General nonrepresentable maps
between DM stacks remain allowed in the main theorem; only the last theorem has
`hf`. No stack 2-fibre product is silently treated as a space. A field lift may
require extension, handled by the existing point classes and surjectivity predicate.
No site/coefficient universe equality or extra finiteness condition is introduced.

Searches: `msearch.py leanfinder` for “Smooth local on source and target properties of
algebraic spaces extend to Deligne Mumford stacks via smooth charts” returned eight
scheme smoothness/chart results, no comparison theorem. `msearch.py loogle` for
`MorphismProperty.IsLocal, MorphismProperty.RespectsIso` returned no hits (unknown
first identifier); the actual `MorphismProperty.RespectsIso` source was then read.
`msearch.py grep` for `smooth.local|SmoothLocal|smooth_chart` in AlgebraicGeometry
returned no hits. `rg` in `lean/WeilConjectures`, `lean/Sheaf` and the upstream name
index found no comparison declaration. `grep -rn` for the item id in
`lean/WeilConjectures` returned none. Additional locality searches with LeanSearch,
LeanFinder and Mathlib/project/DAG grep are preserved verbatim in the new node's
`mathlib_searches`; they found only ordinary scheme smoothness and the current node's
locally-finite-type specialization, not a definition of general smooth locality.
`tools/blueprint_refs.py search 'smooth local'` returned zero blueprint nodes;
its `ancestor` command reports the inherited `blueprint.from.node = None`.

No statement correction, false statement, unusable dependency record, or disputed
mathematical clause was found. The optional fppf hypothesis is retained even though
the node's accepted pointwise-locality proof does not need it. No proof is supplied.

Verification: both modules compiled cleanly through `scompile.py`. The `deliver2.py`
dry run printed `OK (dry run): commit bb15d33f29c passes the preflight and compiles;
nothing pushed`. When its local compiler encountered a full device, the prescribed
wrapper automatically confirmed compilation against the current server sources.

## New nodes

`def-sfb-space-smooth-local-source-target` supplies the exact three-clause property
of Stacks 06F8 in `SpaceSmoothLocalSourceTarget.lean` as
`AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalOnSourceAndTarget`.
It reuses `MapIsLocally`, `Point`, `pointImage`, and categorical pullback squares.
The data are the displayed quantifiers and conjunctions, with no postponed theorem
inside the definition. Searches above found no existing general definition: the
existing `lem-sfb-space-lft-smooth-fpqc-locality` is a specialization asserting
locality for local finite type and has no recorded Lean declaration, so it cannot
supply the definition for arbitrary P. Provenance retains the item's null blueprint
ancestor and its full supporting-input chain rather than inventing a blueprint unit.

`def-sfb-space-fppf-cover` records the existing
`AlgebraicGeometry.AlgebraicSpace.IsFppfCover` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus` with `existing: true`.
Its definition is exactly Stacks 03Y8: for each member, `MapIsFlat` and
`MapIsLocallyOfFinitePresentation`, together with `IsJointlySurjective` of the
underlying presheaf maps. The index has an independent universe `w`, with no
nonemptiness or finiteness assumption; empty members are permitted and an empty
family can cover only an empty target. Both constituent morphism properties and
field-extension-local joint surjectivity use their existing definition nodes.
LeanSearch and LeanFinder found only scheme covering notions; Mathlib grep found
scheme `fppfPrecoverage`; project grep found the exact existing definition at line
48, and the DAG definition-owner scan and blueprint search found no owner of it.
The new node therefore adds ownership metadata and no Lean module or declaration.

## Second reading by O1

No independent worker reading was performed: this dispatcher assignment requires
self-delivery and reserves independent review for the maintainer. The author's
clause check above reads the node against both modules. In particular, (A)'s smooth
comparison is the functor determined by its specified 2-isomorphism; (B) has no
extra comparison hypothesis; the scheme class is precisely representable sheaves;
the ordinary-space theorem spells out all four iff clauses; the final condition
uses the specified base-change projection. This check changed the ordinary-space
theorem from stating only the (A) iff to explicitly stating all four iff clauses.

## Retry verification, 2026-10-24

The saved packet was retained. The required initial `deliver2.py O1
lem-sfb-stack-smooth-chart-comparison --no-push` and a subsequent direct
`scompile.py` of both delivered modules each failed with the same server error:
`resource exhausted (error code: 28, no space left on device)` at
`sandbox Sheaf.Stage2.Sandbox1`. The locality module and preliminary compilation
steps succeeded. No Lean diagnostic identified a source repair; delivery was not
pushed. The earlier verification paragraph records the previous attempt, not a
passing verification on this retry. The saved node still changes only `lean` and
allowed added `stmt_deps`; the two Lean modules and node statement were reread,
and Stacks 06FM/06F8 were checked. No source or launcher tool was modified.

## Retained-packet retry, 2026-10-24

This retry began by reading the retained report and running the prescribed
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push` without changing
the packet. It again failed at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry listing both delivered modules failed at the same
step with the identical diagnostic. The locality module's private overlay,
preliminary, sandbox and library compile steps succeeded; no Lean source error
was reported for repair. Both Lean sources and node records were inspected and
retained. No launcher script or live repository file was modified, and nothing
was pushed. Delivery remains blocked by the compile-server storage failure.

## Latest retained-packet retry, 2026-10-24

The saved report was inspected before the required initial dry run. Both
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push` and the subsequent
direct `scompile.py` invocation listing both saved Lean modules failed again at
`sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
The locality module's private overlay, preliminary, sandbox and library steps
succeeded. Both saved Lean modules were reread; no source diagnostic was emitted
that could guide an authorized source repair. The packet is retained unchanged
apart from this report entry. No launcher script or live source was modified;
nothing was pushed.

## Dispatcher retry, 2026-10-24 10:46 UTC

Inspected the saved report and began with the prescribed unchanged-packet
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push`. It failed at
`sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`. A subsequent
direct `scompile.py` retry listing both saved Lean modules failed at the same
step with the identical diagnostic. The locality module's private overlay,
preliminary, sandbox and library steps succeeded. Both saved Lean files were
read, and comparison with the current local node confirms its statement is
unchanged and its only changed fields are `lean` and `stmt_deps`. No Lean source
diagnostic was reported to repair. All source and node files are retained; only
this report entry was added. No launcher tool or live repository file was
modified, and nothing was pushed. Delivery remains blocked by compile-server
storage exhaustion.

## Current dispatcher retry, 2026-10-24

Read the retained report before running the required initial unchanged-packet
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push`. It failed at
`sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`. A direct
`scompile.py` retry listing both delivered Lean modules produced the identical
failure at the identical step. The locality module's private-overlay,
preliminary, sandbox and library steps succeeded. Both retained Lean modules
were read, and the item's node was compared with the current read clone: the
statement and proof are unchanged; the changes remain the recorded `lean` and
added statement dependencies. No Lean source diagnostic was emitted to repair.
Local disk checks show available space; the failure is reported by the prescribed
server compilation wrapper. All Lean sources and node records are retained.
Only this report entry was added; no live source or launcher tool was modified,
and nothing was pushed.

## Storage-failure confirmation, 2026-10-24 10:56 UTC

Read the retained report and ran the required initial unchanged-packet
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push`. It failed at
`sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`. Retried
`scompile.py` with both saved Lean modules; it failed at the same step with
the identical diagnostic. The locality module passed its private overlay,
preliminary, sandbox and library compilation steps. Both saved Lean modules
were reread; comparison with the current item confirms only `lean` and
`stmt_deps` differ, and no repair note exists. No Lean source diagnostic
was emitted for repair. The packet remains retained, with only this report
entry added; no launcher tool or live repository file was modified and
nothing was pushed.

## Saved-packet validation retry, 2026-10-24 10:59 UTC

Read the retained report and ran the prescribed initial unchanged-packet
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push`. It failed
at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`. A direct
`scompile.py` retry with both saved Lean modules failed at the identical step
with the identical diagnostic. The locality module passed its private-overlay,
preliminary, sandbox and library steps. Reread both saved modules and compared
the saved item against the current read clone: only `lean` and `stmt_deps` differ;
no repair note is present and no source line exceeds 100 characters. No Lean
source diagnostic was emitted for an authorized repair. The source packet is
retained; only this report entry was added. No launcher tool or live repository
file was modified, and nothing was pushed. Compilation and delivery remain
blocked by the reported storage exhaustion.

## Prescribed retained-packet retry, 2026-10-24 11:02 UTC

Read the saved report and ran the initial unchanged-packet `deliver2.py O1
lem-sfb-stack-smooth-chart-comparison --no-push`. It failed at
`sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry listing both saved Lean modules failed at the
identical step with the identical diagnostic. The locality module passed
its private-overlay, preliminary, sandbox and library steps. Both saved
Lean modules were reread. Comparison against the current read clone confirms
that only `lean` and `stmt_deps` differ on the item; no repair note exists,
and neither module has lines over 100 characters. No Lean source diagnostic
was emitted for repair. The packet is retained; only this report entry was
added. No launcher tool or live repository file was modified, and nothing
was pushed. Compilation and delivery remain blocked by the reported storage
exhaustion.

## Retained-packet tool confirmation, 2026-10-24 11:04 UTC

Read the saved report and ran the required initial unchanged-packet
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push`. It failed
at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`. A subsequent
direct `scompile.py` invocation listing both retained Lean modules failed at
the same step with the identical diagnostic. The locality module passed its
private-overlay, preliminary, sandbox and library compilation steps. Both saved
Lean modules were reread. Comparing the item with the current read clone confirms
that only `lean` and `stmt_deps` differ; statement and proof remain unchanged,
no repair note exists, and neither Lean module exceeds 100 columns. No Lean source
diagnostic was emitted for repair. The source packet is retained; only this
report entry was added. No live source or launcher tool was modified and nothing
was pushed. Compilation and delivery remain blocked by reported storage exhaustion.

## Retained-packet verification, 2026-10-24 11:07 UTC

Read the saved report and ran the required initial unchanged-packet
`deliver2.py O1 lem-sfb-stack-smooth-chart-comparison --no-push`. It failed
at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`. Retried
`scompile.py` directly with both saved Lean modules; it failed at the same
step with the same diagnostic. The locality module passed its private-overlay,
preliminary, sandbox and library compilation steps. Reread both saved Lean
modules and compared the item against the current read clone: only `lean`
and `stmt_deps` differ, and no repair note is present. No Lean source diagnostic
was reported to repair. The packet is retained, with only this report entry
added; no live repository source or launcher tool was modified. Nothing was
pushed. Server compilation storage exhaustion still prevents validation and delivery.

## Saved-packet retry, 2026-10-24 11:10 UTC

Read the retained report and ran the required unchanged-packet `deliver2.py --no-push`.
It failed at `sandbox Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
A direct `scompile.py` retry listing both delivered modules failed at the same
step with the identical diagnostic. The locality module passed its private-overlay,
preliminary, sandbox and library steps. Reread both saved modules and compared the
item with the current read clone: only `lean` and `stmt_deps` differ; no repair
note exists and neither Lean file has lines over 100 characters. No Lean source
diagnostic was emitted to repair. All sources and node records are retained.
No live source or launcher tool was modified, and nothing was pushed.

## Successful saved-packet retry, 2026-10-24 11:14 UTC

The required initial unchanged-packet dry run now passed: `OK (dry run):
commit 33e24d96cf8 passes the preflight and compiles; nothing pushed`.
Both delivered modules passed the prescribed server checks. The earlier storage
failure entries are historical and no longer describe the current validation.

Self-check: reread both retained Lean modules and compared the saved item
with the current read-clone node. Its statement and accepted proof are unchanged;
only `lean` and the six documented additions to `stmt_deps` differ. The three
locality clauses, conditions (A)/(B), scheme restrictions, all four ordinary-space
equivalences, and the representable scheme-base-change clause match the current
node and the clause correspondence above. All variables and universes are
explicit under `autoImplicit false`; the two definitions have real data and
all three theorem proofs remain exactly `sorry`. Both modules meet the
100-column limit. No repair note is present. No Lean source or node change
was needed, and no live repository source or launcher tool was modified.

## Returned delivery repair: H2, 2026-10-24

The immutable returned head is `17ed3529a3d7`. Its two theorem nodes were used in
`stmt_deps` solely to access plain definitions. Reconstructed the item from the
current main-branch node, preserving all fields other than its authorized `lean`
and added `stmt_deps`. Replaced `lem-sfb-stack-chartwise-smooth-etale-calculus`
with the landed `def-sfb-surjective-moduli-map` (`existing: true`, declaration
`CategoryTheory.IsSurjectiveModuliMap`). Replaced
`lem-sfb-space-fppf-covering-calculus` with the new existing-definition owner
`def-sfb-space-fppf-cover`, as requested. Neither theorem node remains in
`stmt_deps`. The accepted `proof` and `proof_deps` are unchanged: the chartwise
calculus remains a proof dependency, and the fppf covering calculus is not used
by this proof. Both public imports remain necessary to expose the actual plain
definitions recorded by these definition nodes; no theorem conclusion or
`.choose` supplies data. No Lean signature or proof has changed.

Self-reading against the returned head and current sources confirms that the
new fppf definition node matches both the existing declaration and Stacks 03Y8
clause by clause: arbitrary family, flat and locally finitely presented members,
and joint surjectivity on point classes, including empty cases. The landed
surjectivity owner records exactly the existing field-extension lifting predicate
used by condition (B). All comparison, scheme-chart, ordinary-space and
representable-base-change clauses remain as independently accepted in the return.
This is an ownership repair, with no mathematical statement correction.

Repair validation: the prescribed `scompile.py` invocation listed both delivered
modules in dependency order and completed successfully, including the private
overlay, preliminary, sandbox and library checks. No Lean error or unexpected
warning was reported. JSON layout and the new definition node's exact
statement-citation/`stmt_deps` correspondence were also checked.
