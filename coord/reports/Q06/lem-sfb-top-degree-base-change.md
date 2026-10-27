## Worker report

The module `Sheaf.AlgebraicGeometry.TopDegreeBaseChange` states Stacks 0EX3 as
`AlgebraicGeometry.topDegree_base_change`, with one postponed theorem and three
fully written helper definitions belonging to this same comparison assertion.
The live node is a reviewed stage-1 split with no Lean record, and is in
`coord/queue.tsv` at stage 2. The previous worker's stage-1 refusal is superseded
by the stage-handoff paragraph of `coord/brief-stage2.md` §0.

I read the complete source lemma and proof in `literature/stacks-project/limits.tex`,
lines 4668--4806. The statement is unchanged. The comparison in (c) is the source's
specified derived-to-ordinary comparison; no abstract replacement isomorphism is used.

Hypothesis and clause correspondence:

- The schemes and morphism h are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Quasi-compactness of X and Y is `[CompactSpace X] [CompactSpace Y]`.
  Quasi-separatedness is `[QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]`.
  These do not assume separatedness or properness of f.
- The nonnegative integer d is `(d : ℕ)`; no positive-degree restriction is imposed.
- The assumed vanishing for EVERY quasi-coherent module is `hvan`, quantifying
  `F : X.Modules`, `F.IsQuasicoherent`, `i : ℕ`, and `d < i`, and concluding
  `IsZero (((pushforward f).rightDerived i).obj F)`.
- Every base-change b:Y'→Y is `∀ (Y' : Scheme.{u}) (b : Y' ⟶ Y)`.
  The fibre product is `pullback b f`, its map to Y' is `pullback.fst b f`,
  and its map to X is `pullback.snd b f`. Reversing arguments only uses the
  canonical symmetry convention already used by TopBaseChangePresheaf.
- Clause (a), the first conjunct, quantifies every quasi-coherent F on that
  fibre product, not merely modules pulled back from X, and all `i > d`.
- Clause (b), the second conjunct, quantifies every such F and every quasi-coherent
  M on Y'. It supplies a morphism φ from `(R^d f'_*F) ⊗ M` to
  `R^d f'_*(F ⊗ tensorPullback f' M)`, asserts
  `IsTopDegreeTensorProjection f' F M d φ`, and asserts `IsIso φ`.
  The predicate specifies its action on every open U and all local cohomology
  classes: θ(x) tensor m goes to θ'(H^d(s↦s tensor f'*m)(x)). The θ's are
  the existing `topBaseChangeClass`, not independently chosen identifications.
  `topDegreeTensorSection` constructs that coefficient morphism from the right
  unitor, the actual `1 tensor m` pullback section, and the existing restriction
  tensor comparison. Pure tensors and cocycle classes generate the relevant
  sheaves locally, so this characterizes the canonical arrow. The existential
  is thus a canonical-map characterization, not a mere Nonempty isomorphism.
- Clause (c), the last conjunct, quantifies every such F and every further
  `(Y'' : Scheme.{u}) (c : Y'' ⟶ Y')`. Its map is
  `topDegreeOrdinaryBaseChange f' c F d hC`, with target higher image along
  `pullback.fst c f'` of ordinary tensor pullback along `pullback.snd c f'`.
  The helper takes the inverse ordinary adjunction equivalence of the existing
  `topBaseChangeAdjoint`, whose body is precisely H^d(δ)κ⁻¹ conjugated by
  the canonical total/classical higher-image comparisons. It concludes `IsIso`.
  The existential `hC` records that Rf'_*(F[0]) is ≤d, which is equivalent to
  (a)'s higher-image vanishing and supplies the bound required to type κ.
  It is a conclusion, not an added hypothesis. It precedes arbitrary c, so
  the same bound is used for every further base change.
- All higher images are the right derived functors of structure-module pushforward;
  every unadorned pullback is `Scheme.Modules.tensorPullback`.
- The explicit common `[∀ Y, HasDerivedCategory.{w} ...]` is the project's derived
  localization convention for constructing the stated canonical map. Universes
  u and w are explicitly declared; neither is identified with the other.
  No site universes are collapsed and no auto-implicit parameters are allowed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- The convention-only `def-pc-morphism-conventions` has no declaration;
  the Mathlib compact-space and quasi-separated-space definitions render qcqs.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly imports the existing
  `SheafOfModules.IsQuasicoherent` notion of `pqf-def-coherent`. Its other
  finite-type/coherent clauses are not hypotheses of this item.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`; its definition dependencies give
  `RingedSpace.moduleCohomology`, `RingedSpace.moduleDirectImage`, and ordinary
  `Functor.rightDerived`. The signature and docstring identify total-derived
  module cohomology with these right derived functors.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; schemes have the existing pullbacks instance.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionAdjunction`.
  This is the recorded normalized interface, not an arbitrary adjunction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, retaining the existing tensor.
  The scheme's tensor sections use the upstream `tmulSection` implementation
  of this same sheafified tensor, rather than a second tensor definition.
- Added existing dependency `def-sc-tensor-power-open-restriction-comparisons`:
  `WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN`,
  `AlgebraicGeometry.Scheme.Modules.openRestrictionTensorIso`; its inverse
  is uniquely characterized on pure tensor sections.
- Added existing dependency `def-pc-derived-category`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategory`, `schemeDerivedCategory`.
- Added existing definition dependency `def-sfb-top-base-change-canonical-maps`:
  `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf`, `topBaseChangeRestrictedUnit`,
  `topBaseChangeClass`, `topBaseChangeDelta`, and `topBaseChangeAdjoint`.
  I read the full signatures, docstrings and constructions. The theorem
  `lem-weil-pbc-top-base-change-presheaf` remains solely a proof dependency.
- Added existing dependency `def-pc-derived-direct-image`:
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`,
  `AlgebraicGeometry.schemeDerivedDirectImage`, used in hC and the ordinary
  base-change helper. Its universe parameters remain independent.
- Added existing dependency `def-pc-restricted-resolution-sections`:
  `WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices`,
  `AlgebraicGeometry.Scheme.Modules.RestrictedResolutionSections`, used by
  `IsTopDegreeTensorProjection`; read all five fields and their docstrings.

All already stated proof-dependency modules are imported, directly or publicly
through these interfaces. The unstated module-functor exercise has no module to
import; the affine permanence, qcqs permanence and tensor-right-exact nodes have
Mathlib matches instead. No proof is supplied in this stage. The theorem docstring
records all eight steps of the accepted split, including the two-kernel argument,
the affine push-pull unit normalization, and the presheaf identification of γ.

Edge cases checked before writing:

- d=0: vanishing begins at i=1; κ uses degree zero and the right-exactness argument
  still applies. The identity f and arbitrary nonflat c are included.
- Empty schemes and zero modules: no nonempty assumptions or chosen generators;
  unitor, sheaf restriction, tensor, and local class maps remain defined.
- Nonflat base change, e.g. R→R/I: neither b nor c has a flatness binder;
  no exactness of ordinary pullback is assumed.
- Y' and Y'' may be non-qcqs. Compactness and quasi-separatedness are only
  hypotheses on X and Y. Local affine reduction in the proof is not added
  as a global restriction.
- F need not descend from X and M need not be invertible or finite type.
  This excludes reusing the stronger-hypothesis upstream projection formula.
- No properness, Noetherian, finite-presentation or coefficient characteristic
  restriction was introduced. Every object and universe is explicitly bound.

Searches for an existing exact assertion:

1. `msearch.py ... leanfinder` with query
   “For a quasi compact quasi separated scheme morphism whose higher direct images
   of quasi coherent modules vanish above d, the degree d direct image commutes
   with arbitrary base change and tensor products”: eight hits on pushforward and
   adjunctions (`Scheme.Modules.pushforward`, `instAdditivePushforward`,
   `pullbackPushforwardAdjunction`, `pushforwardComp`, etc.), no matching theorem.
2. `msearch.py ... leansearch` with query “highest higher direct image commutes
   with tensor products of quasi coherent sheaves”: eight unrelated tensor/direct
   limit/quasi-coherence hits, no matching assertion.
3. `msearch.py ... loogle 'higherDirectImage, projectionHom'`: unknown identifier;
   repeated with `SheafOfModules.IsQuasicoherent`: twelve hits identifying the
   existing quasi-coherence class and its propagation, not this theorem.
4. `msearch.py ... grep 'higherDirectImage|topCohomology|cohomolog.*baseChange'
   AlgebraicGeometry`: zero Mathlib matches.
5. `rg` on the same concepts in `lean/WeilConjectures/AlgebraicGeometry` and
   `lean/Sheaf/AlgebraicGeometry`: found TopBaseChangePresheaf and
   DerivedPullbackTopCohomology, which are used, and the upstream
   `higherDirectImageTensorObjPullbackIso`, which assumes M.IsInvertible and
   does not cover this statement. Read that full signature and docstring.
6. `rg`/`grep -rn` for the exact item id in `lean/WeilConjectures` and `lean/Sheaf`:
   no existing implementation. Searching the new full declaration names in
   both trees also found no collision.
7. DAG lookup located the already recorded open-restriction tensor comparison;
   it was reused, not redefined. The repair adds a definition-node binding for
   the existing four canonical maps, with no new Lean notion.

Validation: `scompile.py Q06 lem-sfb-top-degree-base-change <module>` passed both
sandbox and library module-mode checks (about 3.5 seconds each). No errors or
unexpected warnings. All Lean lines are at most 100 characters. No statement
correction, dependency repair, or STATEMENT-DISPUTED flag is needed.

## New nodes

`def-sfb-top-base-change-canonical-maps` records the four existing definitions
`topBaseChangeRestrictedUnit`, `topBaseChangeClass`, `topBaseChangeDelta`, and
`topBaseChangeAdjoint` from `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf`
with `existing: true`. No module is added or duplicated. Its source is Stacks
0EX3 (the definition of gamma before the proof), with 01E4, 01FB and 08HY for
its local class, restricted unit and derived-mate constituents. Its statement
introduces the schemes, square, module, resolutions, opens and cohomological
bound, then specifies each construction. The bound is required only for the
adjoint. The statement makes no presheaf compatibility or invertibility claim.
The only proof used by the inverse in that construction is
`derivedPullback_topCohomology`, whose conclusion determines the inverse.
The distinct compatibility theorem remains in the item's `proof_deps`.

Searches: `blueprint_refs.py search topBaseChange` returned zero blueprint
nodes. DAG grep found only the theorem node listing these as helper declarations;
there was no definition node for the notion. LeanSearch with query
"canonical top degree base change map adjoint cocycle class map for higher direct
image sheaves" gave eight unrelated differential/dual/group-cohomology hits.
Loogle `"topBaseChange"` and Mathlib grep
`topBaseChange|cocycle.*[Cc]lass` in AlgebraicGeometry both returned zero hits.
Project grep found these four definitions only in the existing Sheaf module,
with no upstream duplicate. The unabridged search outputs are recorded in the
new node's `mathlib_searches`.

## Return repair

The return on immutable head `233246571b05` identified H2 dependency ownership.
The saved packet passed the initial dry run as `1dfc8855a20`, but still contained
that semantic defect. I replaced the theorem in `stmt_deps` by
`def-sfb-top-base-change-canonical-maps`, and added
`def-pc-derived-direct-image` and `def-pc-restricted-resolution-sections`.
The theorem remains in `proof_deps`, with all eight proof steps unchanged.
The natural-language item statement and all Lean bytes are unchanged. This is
a definition-node and dependency repair, not a statement correction.

## Second reading by Q06

This is a separate second pass by the same worker; the dispatcher expressly
forbids starting other agents. I reopened the source, node and delivered file.
The initial and base-changed quantifiers match all three clauses of 0EX3. In
particular I checked the F quantifiers occur separately in (a), (b), (c), the
nonflat and d=0 cases, and the unrestricted Y' and Y'' binders. The tensor
comparison uses the actual local section rather than an arbitrary arrow.
The base-change comparison is the inverse ordinary adjunction applied to the
recorded adjoint, hence is exactly its specified γ. The bound hC is provided
as a conclusion, never required as an extra hypothesis. The tensor-section
formula first restricts to the inverse-image open, then applies the inverse
of the tensor restriction isomorphism, so its codomain is the restriction of
the GLOBAL tensor coefficient used by R^d f'_*. This avoids silently changing
the coefficient object. The three existing statement prerequisites used in
these helpers were added to stmt_deps, and no other field of the accepted
stage-1 split was changed. No mismatch remained after this reading.


Repair self-check: I reopened all four canonical definitions and their bodies,
plus the derived-direct-image abbreviation and the restricted-resolution
structure. The new node's restricted unit is exactly the restriction/composition
of the ordinary unit; its theta is exactly `resolutionSectionClass` followed by
`I.isoRightDerivedObj`; its delta is the derived mate followed by
`pinnedModulePullbackComparisonAt`; its adjoint is the normalized ordinary
adjoint of H^q(delta) kappa inverse, conjugated by the total/classical comparisons.
There is no use of `top_base_change_presheaf` in these definitions. Its separate
proof use is retained. I checked the new node's referenced prerequisites against
the live DAG, its existing-record signature verbatim against the existing file,
and the item against current main by JSON comparison: only `lean` and the
authorized `stmt_deps` differ. The saved Lean module is retained unchanged, as
requested by the return. The initial dry run already compiled it on the live
server, and the final dry run validates the repaired packet.

The repaired-packet dry run required `import_flags` on the new definition node;
I added the empty list required by the live schema, and expanded grouped
prerequisite citations into individual bracketed ids. No import defect is flagged.
