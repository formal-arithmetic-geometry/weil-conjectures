## Worker report

The delivery states `CategoryTheory.flatConstantTensorProZeroCones` in
`Sheaf.CategoryTheory.FlatConstantTensorProZeroCones`. Its proof is `sorry`.
Every helper definition has actual data. There are no additional postponed theorems.
The natural-language statement and proof are unchanged. Two already-landed statement
dependencies are added to name the existing constant-module realization and scalar
extension presentations used by the statement. There are no new nodes or dependency
repairs.

Sources read: Stacks `proetale.tex`, lemma-naive-completion, Tag 099M, including its
Koszul-to-quotient pro-isomorphism argument; `sites-cohomology.tex`,
lemma-derived-limit-is-ok, Tag 0941, including its K-injective tower computation;
`sites-modules.tex`, definition-flat, Tag 03ER(3)--(4), and lemma-constant-exact,
Tag 093J. The node's nine proof steps are reproduced in the theorem docstring.
The dependency `strictPerfectConstantSheaf_exact` still cites 093U in its own docstring;
093J is the constant exactness lemma read here.

Hypothesis and clause correspondence:

- A small site is `C`, `Category.{v} C`, `J`, with
  `EssentiallySmall.{max u v} C`. The module coefficient universe is `max u v`.
  Sheafification and its locally bijective characterization are explicit technical
  instance parameters. They hold for small sites. Object and morphism universes remain
  independent; the pro-etale convention `u = t+1`, `v = t` is included.
- The commutative Noetherian ring is `A`, `[CommRing A]`, `[IsNoetherianRing A]`.
  Noetherianity is retained although this general transport argument does not need it.
- `R = underline A` is the already-defined `realizationRing J A`, namely
  `(constantSheaf J CommRingCat).obj (CommRingCat.of A)`. `O` is a commutative ring sheaf
  and `φ : realizationRing J A ⟶ O` is the given ring-sheaf map.
- Flatness is exactly `hflat : SheafOfModules.IsFlatOnSite ...`, applied to the unit
  O-module restricted through φ. This is flatness of O as an R-module, rather than
  flatness of its sections or degreewise flatness of P.
- The ordinary functor E is `flatConstantExtension J A φ`. It composes the existing
  `commutativeSiteConstantModuleFunctor` with the ordinary `.E` field of the existing
  `SheafOfModules.canonicalDerivedChangeOfRingsModel φ`. The helper abbreviation
  `flatConstantExtensionModel` chooses `HasDerivedCategory.standard` for the source
  internally. Its `obj_eq` and `map_eq` prescribe precisely `changeOfRings φ M` and
  `changeOfRingsHom φ M f`. Neither a model nor a source localization is a hypothesis.
  The model's derived field is unused.
- Strict inverse sequences are `X Y : ℕᵒᵖ ⥤ CochainComplex (ModuleCat A) ℤ`;
  `v : X ⟶ Y` imposes all strict commuting transition squares. The existing
  `HomologicalComplex.functorEquivalence` converts these to complexes of module towers.
- `hv : FlatConstantConeProZero v` says verbatim: for every `n : ℕ`, there exist
  `m : ℕ` and `h : n ≤ m` for which `DerivedCategory.Q.map` of the corresponding
  transition of the strict mapping-cone tower is zero. The cone is formed in the
  tower category, then evaluated. Thus the predicate retains its canonical transitions.
  It does not substitute acyclicity or zero cohomology maps for zero derived morphisms.
- `P` is an arbitrary ℤ-indexed complex of O-module sheaves;
  `hP : CochainComplex.IsKFlatIndependentCoefficients (R := O) P` is exactly the recorded
  K-flatness predicate. No termwise flatness or boundedness hypothesis occurs.
- `flatConstantTensorFunctor` is termwise E followed by the existing cochain
  `tensorLeft P`. The cochain monoidal tensor is the direct-sum total bifunctor tensor
  of `def-pc-tensor-complex-sheaves`, including its Koszul differential signs.
- The first conclusion `FlatConstantConeProZero (Functor.whiskerRight v ...)` gives
  exactly the transformed strict cone tower's pro-zero property in D(O).
- `RF` and `η` range over total right-derived pairs of termwise inverse limit on the
  abelian category of strict O-module towers. The hypothesis
  `RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ))` specifies that
  pair by its universal property. Its existence and K-injective computation are the
  recorded strict-tower dependency. `IsIso (RF.map (DerivedCategory.Q.map ...))`
  states invertibility of the image of the actual strict transformed map.
- The existential `i` explicitly exposes the ordinary canonical identification
  E(A) ≅ O used in the node's unit clause. `FlatConstantUnitNormalized` fixes it on
  local pure tensors by `s ⊗ underline x ↦ s * φ(x)`. The tensor and sheafification
  universal properties uniquely determine this map. Thus no arbitrary isomorphism
  is accepted as the coefficient identification.
- The optional units are `α : Δ(A[0]) ⟶ X`, `β : Δ(A[0]) ⟶ Y`, with
  `α ≫ v = β`. These are compatible chain maps at every level, with the specified
  commutation with v.
- `flatConstantTensorUnit` is the actual strict chain map
  P → P ⊗ E(A[0]): inverse right unitor, then inverse of the degree-zero extension of
  the normalized multiplication i. `flatConstantTensorCoaugmentation` applies the
  strict functor to α or β, using the canonical `Functor.constComp` comparison.
- `flatConstantStrictConeMap` is Q of the ordinary constant/limit adjunction unit
  followed by the strict cone's termwise inverse limit, and then `η`. Its composite
  with `DerivedCategory.Q.map (flatConstantTensorUnit ...)` has source Q(P), exactly
  as in the node. Naturality of η at a K-injective replacement j identifies this
  displayed map with Q(lim(jα)). `flatConstantUnitLimitMap` names this same composite
  so that the final equality has an explicit, manageable type. No coaugmentation or
  triangle filler is independently quantified in a derived category.
- The last equality says that the map from P induced by α, followed by the very same
  RF(v) asserted invertible above, equals the map from P induced by β.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent alias of `SheafOfModules`; the latter spelling is used in displayed types.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; mapping cones are
  `CochainComplex.mappingCone` and their strict transitions are obtained by forming
  the cone in the tower category and evaluating.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, its additive and colimit instances.
  `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` underlies
  the cochain tensor; `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` supplies
  the cochain monoidal interface and unitors.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, which
  supplies the total right-derived functor, its K-injective computation and pro-zero
  cone criterion. The theorem uses its universal right-derived interface so it does
  not fix a choice of representatives.
- Added landed node `def-sfb-site-derived-constant-module-functor`, module
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realizationRing`, `realizationRingUnit`, `commutativeSiteConstantModuleFunctor`.
  Their full signatures and docstrings, including their comparison with the original
  constant RingCat presentation, were read.
- Added landed definition node `def-zl-derived-change-of-rings-model`, module
  `Sheaf.AlgebraicGeometry.DerivedChangeOfRingsModel`:
  `SheafOfModules.canonicalDerivedChangeOfRingsModel`. Its prescribed ordinary `.E`,
  `obj_eq`, `map_eq`, and additive instance are inherited from
  `SheafOfModules.DerivedChangeOfRingsCochainModel`. Both declarations and their
  docstrings were read. The theorem `nonempty_derivedChangeOfRingsCochainModel`
  is used by the existing definition, not directly by this item or its proof, so
  `lem-pur-derived-change-of-rings` is not added to either dependency list.

All already-stated proof dependencies are imported, using ordinary non-public imports:
`strictPerfectConstantSheaf_exact` in `Sheaf.CategoryTheory.FiniteTypeConstantExact`;
`moduleSheaves_colimits_forgetful` in
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
`Functor.mapDerivedCategoryFactors` in
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
`CochainComplex.mappingCone.quasiIso_iff_acyclic` in
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`;
`CochainComplex.mapBifunctorMappingCone₂Iso` in
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`;
`Localization.lift` in `Mathlib.CategoryTheory.Localization.Predicate`;
`CochainComplex.IsKInjective.Qh_map_bijective` in
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
Dependencies already needed publicly for the signature are publicly imported.

Edge cases checked before and during writing:

- `m = n` is permitted: the localized identity transition may be zero when that
  cone is zero. There is no `n < m` requirement or uniform bound.
- The zero ring, zero complex P, zero towers, and empty site remain allowed.
  Unit normalization is also meaningful for a zero ring or empty site.
- Arbitrarily unbounded X, Y, and P are allowed; no finite-rank, finite-type,
  perfectness, flat-term, or exact-countable-product assumption was introduced.
- Unit compatibility is conditional on the supplied α and β. Without them the
  pro-zero and isomorphism conclusions remain, including for nonunital complexes.
- Distinct site object and morphism universes are retained. Derived localization
  universes for algebraic modules, constant sheaves, and O-modules remain explicit.
  The strict tower and O-module derived categories use the common localization
  size of the recorded strict-tower interface; this imposes no site-universe equality.

Searches for an existing statement:

- `msearch.py ... leanfinder "flat constant extension K-flat tensor preserve pro-zero
  cone towers derived inverse limits"`: eight hits, concerning flat algebraic tensor
  functors and limits; none states strict cone-tower transport or strict-unit compatibility.
- `msearch.py ... loogle "CochainComplex.mappingCone, SheafOfModules.restrictScalars"`:
  zero hits.
- `msearch.py ... grep "proZero|pro_zero|pro-zero" Algebra/Homology`: zero hits in
  that Mathlib directory.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  pro-zero/tensor combinations: found algebraic tensor-kernel pro-zero results,
  `KoszulQuotientConeIsIso` and Roos specializations. None states this general result
  for every flat constant extension and every K-flat complex.
- Name searches over Mathlib and both project roots found no collision for any
  declaration added by this module. Existing definitions were read and reused.

No statement dispute or source correction is needed. The unit normalization is
explicitly part of the formal conclusion so that its transport cannot conceal an
arbitrary map. Every new declaration has a source and the owning blueprint id.

Prior-packet validation: the retained version passed the initial delivery dry run
(commit 82a2a83b73c). The repair must pass its own compile and dry run before delivery.
The earlier worker recorded 58.2 seconds for the original module; this is not claimed
as validation of the repaired module.


## Returned-delivery repair (H2)

The return at immutable head 50021a33f438 identified a theorem-only statement
dependency: `lem-pur-derived-change-of-rings` supplied no construction used by the
statement because the old interface quantified a model `e`. This repair removes
that binder and its `[HasDerivedCategory.{wR} (realizationModules J A)]` instance,
and removes universe `wR`. The ordinary extension now uses the existing definition
`SheafOfModules.canonicalDerivedChangeOfRingsModel` from
`def-zl-derived-change-of-rings-model`; its source localization is supplied internally
by `HasDerivedCategory.standard`. The definition node replaces the theorem in
`stmt_deps`. The theorem is not needed in `proof_deps`, which remains unchanged.
The specialized helper abbreviation is recorded in `lean.declarations`.

Self-check of the repair against the node and current live base: the natural-language
statement, all nine proof steps and `proof_deps` are identical to the live node.
Only `stmt_deps` and `lean` differ. The new import is the recorded module of the
canonical definition; no new node or dependency module is needed. The module retains
exactly one postponed theorem, `flatConstantTensorProZeroCones`, with `sorry` and the
full proof docstring. Every helper definition has real data.

Re-reading hypothesis and clause correspondence after substitution: `C,J,A,φ` and
`hflat` retain the small site, Noetherian commutative coefficient ring, constant ring
sheaf, and flatness of O as an R-module. `X,Y,v,hv` retain strict towers and strict
cone transitions that vanish in D(A), with m = n allowed. `P,hP` retain arbitrary
unbounded K-flat P and the same total tensor as the recorded K-flat predicate. The
first conclusion remains pro-zero transformed cones in D(O). `RF,η` retain the
universal right-derived inverse limit and its asserted isomorphism. `i` and
`FlatConstantUnitNormalized` retain multiplication on local pure tensors; only its
`obj_eq` now comes from the canonical model. `α,β,α ≫ v = β`, the tensor unitor and
strict cone comparison retain the actual unit maps and their equality under the
same derived-limit isomorphism. Zero rings, zero complexes, empty sites, arbitrary
unbounded complexes, independent site universes, and conditional unit compatibility
remain covered. No mathematical statement correction is involved.

Validation attempt after the repair: `scompile.py Q07
lem-weil-pbc-flat-constant-tensor-pro-zero-cones <module>` and the delivery dry run
both stop while compiling the unchanged overlay dependency
`Sheaf.CategoryTheory.RingedSiteModules`, before compiling this module. The diagnostic
is `unknown module prefix 'Mathlib'`; the wrapper's server confirmation says
`Live published library is unavailable`. No source or launcher-tool workaround was
attempted, and nothing was pushed. The retained packet is ready for recompilation
when the published library is restored.


## Retry validation (2026-10-21)

The retained H2 repair was checked against the current read clone: only `lean` and
`stmt_deps` differ; the theorem signature is verbatim in the JSON record, `wR` and
the quantified model are absent, and the canonical definition node is cited.
The natural-language statement and proof dependencies remain unchanged.

As requested, the first action after reading this report was
`deliver2.py Q07 lem-weil-pbc-flat-constant-tensor-pro-zero-cones --no-push`.
It failed before compiling the delivered file, while loading the unchanged
`Sheaf.CategoryTheory.RingedSiteModules`: the object file for
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` does not exist. A separate
`scompile.py` invocation reproduced exactly this error. Both wrappers confirmed
against current server sources and printed `Live published library is unavailable`.
This is not a 60-second timeout or an elaboration failure of the saved packet.
No launcher script, shared source, or library artifact was changed; nothing was pushed.

## Dispatcher retry validation (2026-10-21)

The required first dry run on the saved packet again failed before reaching the
item: compiling the unchanged overlay `Sheaf.CategoryTheory.RingedSiteModules`
requires the missing published object file
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean`.
A separate prescribed `scompile.py` call reproduced the same failure. Both tools
performed server confirmation and returned `Live published library is unavailable`.
This is a missing published library artifact, not a busy-server timeout or a
statement elaboration failure. No library artifacts or launcher tools were modified.

The retained H2 repair was checked again: the signature matches `lean.statement`
verbatim, `wR` and the model parameter are absent, the canonical model definition
and helper declaration are recorded, and the unwanted theorem is absent from both
dependency lists. The mathematical statement, proof and proof dependencies agree
with the current shared node. The sandbox's stale `lean_audit` metadata was refreshed
from that read-only node; only `lean` and `stmt_deps` now differ from the current base.
The saved module remains unchanged. Nothing was pushed because compilation cannot
reach it until the published Mathlib artifact is restored.


## Current retry validation (2026-10-21, published-library failure)

The required first dry run was run on the retained packet. It passed dependency
preparation and reached the delivered module (42.8 seconds), then failed with
helper elaboration errors. Its truncated diagnostic includes applications of
`flatConstantExtension J A φ` and `flatConstantTensorFunctor J A φ P` whose inferred
helper signatures omit φ, followed by cascading errors in the unit-map helpers
and theorem. The first diagnostic was not present in the delivery wrapper's
5000-character tail, so a separate prescribed `scompile.py` run was requested to
obtain it. This is not a clean compile, and the repaired module remains unvalidated.

Three separate `scompile.py` attempts instead failed during import loading on the
server: the published object file
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.
The first two failures arose while loading the unchanged
`Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`; the last
reached this module's import loading and failed on exactly the same missing object.
Each attempt performed server confirmation and reproduced the missing artifact.
This is an import/artifact failure, not a busy-server timeout. The complete helper
diagnostic cannot currently be obtained, and a source change cannot be validated.

The H2 self-check was repeated: only `lean` and the two added landed definition
dependencies differ from the current read-clone node; the signature is verbatim,
`wR` and the model parameter are absent, the canonical model is used, the unwanted
theorem dependency is absent from both lists, all lines fit 100 characters, the
JSON layout is exact, and the sole postponed theorem has the nine-step proof
docstring. The current server source of the canonical model was also read using
`scompile.py --source`; it agrees with the read clone. The saved Lean and node
were left unchanged in this retry. No launcher tool, live source or library
artifact was modified, and nothing was pushed.


## Latest dispatcher retry (2026-10-21)

As requested, the retained packet was inspected and its first validation was
`deliver2.py Q07 lem-weil-pbc-flat-constant-tensor-pro-zero-cones --no-push`.
It failed before elaborating the item because the published object file
`Sheaf/Paper/StrictPerfectCoefficientPackage.olean` does not exist.
The separate prescribed `scompile.py` call reproduced that same missing object,
both locally through the authorized wrapper and in its current-server confirmation
(0.4 seconds on the server). This is an import-loading failure, not a timeout.
The helper elaboration errors recorded in the previous attempt remain unvalidated;
this retry cannot reach them. No clean compile or successful dry run is claimed.

The H2 self-check against the current shared node passed: only `lean` and
`stmt_deps` differ; the two additional dependencies are already-landed definition
nodes, including `def-zl-derived-change-of-rings-model`. The unwanted theorem is
absent from both dependency lists. The quantified model and `wR` are absent, and
`flatConstantExtensionModel` uses the existing canonical model with the standard
source localization. The theorem signature agrees verbatim with `lean.statement`,
the sole `sorry` is the main theorem, every line is at most 99 characters, and the
node JSON has the required layout. The saved Lean module and node remain unchanged.
No launcher script, shared source, or published library artifact was modified.

## Repair validation (2026-10-21)

The restored server library reached elaboration and reported that the explicit
`φ` argument had been omitted from the helper definitions, and that the source
derived-category instance needed by the canonical change-of-rings model was not
available through the reducible abbreviation. The repair makes `φ` an explicit
argument of `flatConstantTensorFunctor`, `FlatConstantUnitNormalized`,
`flatConstantTensorUnit`, `flatConstantTensorCoaugmentation`, and
`flatConstantUnitLimitMap`. It adds the real instance
`flatConstantSourceHasDerivedCategory`, selecting
`HasDerivedCategory.standard (realizationModules J A)`, and keeps
`flatConstantExtensionModel` as a noncomputable definition using the recorded
`SheafOfModules.canonicalDerivedChangeOfRingsModel`. The local additive
zero-morphism instance is enabled so the existing cochain functor API applies;
this introduces no hypothesis or statement clause. The helper is listed in the
node's `lean.declarations`.

`scompile.py` compiled the repaired module and its generated library declaration
with no errors or warnings. The final `deliver2.py --no-push` and push are now
run against this repaired packet; the prior dry run failure was the elaboration
diagnostic above, rather than a source or tool failure.

## Timeout-return repair (immutable head 2ae01143c95e)

The required initial dry run reproduced the returned defect: both its local compile
and server confirmation timed out after 60 seconds. The saved packet was retained;
no statement investigation was restarted and no limit was raised. Full-file scratch
profiling identified repeated `HasSheafCompose` inference, reconstruction of cochain
monoidal data, and unresolved coefficient-universe inference in repeated
`sheafCompose` expressions. Profiling was diagnostic only and is absent from the
final module.

The repair reuses four existing instance values through named local definitions:
`flatConstantHasSheafCompose`, `flatConstantCochainMonoidal`,
`flatConstantCochainMonoidalStruct`, and `flatConstantExtensionAdditive`.
The monoidal-structure instance is exactly the structure projection of the selected
existing cochain monoidal instance, so whiskering and unitors use the same tensor.
All four have actual data and source/blueprint docstrings; they add no hypothesis,
new mathematical notion, or postponed theorem. The scalar-extension model and
ordinary extension now have explicit result types. The already existing
`SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O`
abbreviation replaces the repeated forgotten-ring expression; its definition is
exactly that expression. The source declaration's universe order was checked and
is coefficient, site object, site morphism. No universe equality was imposed.
The previously missing model-helper docstring is supplied. Name searches with `rg`
over Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no collisions for the
four local helper names. All helpers are listed in `lean.declarations`.

The complete profiled candidate compiled as both the sandbox module (51.4 seconds)
and generated library check (56.3 seconds). Those runs had diagnostic profiling and
line-length warnings; they are not the final clean validation. Profiling was then
removed and the six long lines wrapped. The final source has maximum line length
99, exactly one `sorry` (the item's named theorem), and real data in every definition.
The final clean compile and delivery dry run are recorded below when completed.

## Second reading by Q07

This is the worker's final self-check; the maintainer supplies the independent
review. I compared the saved packet, the repaired file, and the current shared node.
Only `lean` and the two previously added landed definition dependencies differ
from the shared node. The node's mathematical statement, all nine proof steps,
and `proof_deps` are unchanged. `lean.statement` is the final signature verbatim,
and the JSON uses indent 1, Unicode, and a final newline.

Hypotheses remain the independent-universe small site `C,J`, commutative Noetherian
`A`, the constant ring sheaf `realizationRing J A`, its map `φ` to `O`, and exactly
flatness of the restricted unit O-module (`hflat`). `X,Y,v` still encode strict
towers and a strict commuting map. `hv` still demands actual zero localized cone
transitions with some `m ≥ n`, and `P,hP` still mean an arbitrary unbounded K-flat
complex. The tensor functor still applies the recorded constant-module functor,
the ordinary `.E` of the canonical change-of-rings model, and total left tensor by
P. No model is quantified and the removed theorem-only dependency remains absent.

The first clause is the same pro-zero condition on transformed cones. The second
asserts that the actual image of the transformed strict map under every total
right-derived limit pair `RF,η` is an isomorphism. The existential unit isomorphism
is still normalized by multiplication on local pure tensors, and the last equality
still transports the actual maps from `P` obtained from the strict compatible
coaugmentations `α,β`, tensor unitors, ordinary limit adjunction unit and `η`.
The new local instances are definitions reusing those same structures, not extra
assumptions. The earlier edge-case checks remain valid: zero rings/complexes,
empty site, unbounded complexes, `m = n`, absence of units, and distinct site
object/morphism universes are all retained. No mathematical correction or
statement dispute was introduced.

The first unprofiled validation of that version still timed out in both local and
server runs, so the earlier profiled timings were insufficient validation. Further
profiling isolated kernel checking of `flatConstantUnitLimitMap` as the largest
remaining cost (15.5--28.0 seconds in the profiled runs). The repair therefore also
adds `flatConstantPointedLimitMap`, a generic expression for the same composite:
localize an actual strict point `ι`, apply the ordinary constant/limit comparison
to the functor-applied strict coaugmentation, then apply `η`. The specialized
`flatConstantUnitLimitMap` supplies the existing tensor functor and the actual
normalized `flatConstantTensorUnit` to this helper. No new map is a hypothesis of
the main statement. Expanding the new helper yields exactly the previous body,
including `Functor.constComp` and `Functor.whiskerRight`; this merely moves the
categorical expression to a definition where its source category is a parameter.
The helper has actual data, a source/blueprint docstring and a declaration record.
The name was searched in Mathlib and both project Lean roots with no collision.

Cleanup also exposed a parser error from wrapping `.mapHomologicalComplex` onto
its own line. Both affected signatures now use the ordinary prefix application
`Functor.mapHomologicalComplex (lim : ...) (.up ℤ)`, with the identical type.
The node's signature record was updated verbatim. Neither adjustment changes a
mathematical hypothesis, clause, universe restriction, construction or proof step.

The corrected pointed-helper version passed the prescribed `scompile.py`: the
local attempt timed out, but current-server-source confirmation compiled the
complete generated library declaration cleanly in 39.6 seconds (nice 19, two
threads, unchanged 60-second limit). The tested source is byte-identical to the
saved delivery module. No profiling options, errors, or non-sorry warnings remain.
The delivery dry run is the next final validation.

The intermediate dry run passed both complete module compiles, then preflight
reported that its declaration scanner did not recognize the four declarations
written with `local instance`. The final repair writes the same values with the scanner-supported `instance`
syntax, removes each automatic global instance registration immediately with
`attribute [-instance]`, then registers it with `attribute [local instance]`.
This preserves local scope and Lean's standard instance reducibility while making
the declarations visible to the scanner. No launcher or
project tool was changed.

The final version also reuses Mathlib's canonical module-sheaf abelian structure
and ordinary countable inverse limits through `flatConstantModulesAbelian` and
`flatConstantModulesLimits`. Both are direct `inferInstance` aliases of the
existing Mathlib instances, not choices of new structures. In particular the
abelian instance is not obtained from an existence theorem. These avoid expanding
those structures while checking each derived-limit comparison. The complete
profiled version with these two aliases compiled in 18.2 seconds (sandbox) and
25.4 seconds (generated library check). Name searches over Mathlib and both
project Lean roots found no collisions. Both helpers have actual data,
source/blueprint docstrings, and `lean.declarations` entries. The final compile
and preflight are run after removing profiling and changing only the equivalent
local-instance registration syntax.

The intermediate plain-`def` syntax compiled in 32.4 and 30.8 seconds but produced
class-reducibility and proposition-definition warnings. The final `instance` syntax
with immediate global unregistration and local registration repairs those warnings
without disabling any linter or changing the instance values. Every final instance
remains real data; the only postponed theorem is still the item itself.

Final prescribed direct compile: the complete delivery module compiled cleanly as
`Sheaf.Stage2.Sandbox0` in 27.0 seconds and as
`Sheaf.CategoryTheory.FlatConstantTensorProZeroCones` in 25.7 seconds. There were
no errors or non-sorry warnings. A redundant second instance-unregistration line
was removed during the final self-check; the delivery dry run recompiles that
final source. All instance witnesses retain their intended local registrations.
The natural-language statement/proof remain unchanged, the signature record is
verbatim, and the module still has exactly one postponed theorem and no diagnostic
commands or profiling options.
