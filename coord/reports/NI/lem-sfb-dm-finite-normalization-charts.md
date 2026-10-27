## Worker report

Maintenance commit `6ecc4f743596f131f49e1555366d0bc220f5047b` registers both worker-authored definitions as
existing, unstated DAG prerequisites (`lean: null`) and supplies their required
maintainer-owned `import_flags: ["unreachable"]`. The parent item has the same
accurate flag: it is outside the closure of all current/former targets.

Deliver `def-sfb-formal-moduli-quotient` and
`def-sfb-moduli-normalization-tests` as dependency modules with their retained
Lean bindings and the added `lean.note`, preserving the base's other metadata.
Keep both in the item's `stmt_deps`. Their source, statement, dependencies,
searches and all three Lean modules are unchanged. The historical new-node and
BLOCKED entries below describe the old base. Run the unchanged normal delivery
dry run and delivery; independent stage-2 review remains required.

NI, stage 2, 2026-10-22. This is a Lean statement delivery, not a stage-1 re-split.
The preceding worker's stale-dispatch conclusion conflated these stages: Q61's
independently reviewed split is retained verbatim, and the live node had no `lean`
record. No existing split, source, proof, status, review or unit statement is changed.
The prescribed sandbox had no retained report or Lean delivery when this run began.

The item module is `Sheaf.AlgebraicGeometry.DmFiniteNormalizationCharts`. Its only
theorems are `AlgebraicGeometry.exists_dm_finite_normalization_charts` and
`AlgebraicGeometry.dm_finite_normalization_formal_chart`, both with `sorry` proofs.
The two new definition modules contain actual predicates, a coherent action
structure, a geometric fibre object and the induced action on atlas points. No
definition chooses data from a postponed existence theorem. Each theorem's docstring
contains its corresponding steps of the existing nine-step proof, with source and
DAG identifiers.

The node has two mathematical paragraphs. The first declaration states the global
construction and scalar extension. The second states its formal-chart clause for
an algebraically closed coefficient field. The first declaration's chartwise scalar
compatibility identifies that normalization with the base change of the original
one. Thus working over Ω in the second declaration includes every Ω/k and every
perfect original k; it does not assume the original k algebraically closed or drop
the scalar-extension assertion.

Hypotheses and conclusions of the global paragraph:

| Node clause | Lean rendering |
|---|---|
| k is a field | `(k : Type u) [Field k]` |
| X is a DM stack | `X : BasedCategory ... (Over (Spec (.of k)))`, `hX : IsDeligneMumfordModuliStack X` |
| X is smooth of finite type over k | `hXs : HasSmoothFiniteTypeModuliAtlas X`, the already recorded étale surjective atlas with `Smooth`, `LocallyOfFiniteType`, and `QuasiCompact` structure map |
| U is an open substack, dense in X | `j : BasedFunctor U X`, `hU : IsModuliStack U`, `hj : IsDenseOpenModuliMap j`; each scheme test is an open immersion and every étale chart has dense inverse image |
| V is a stack and V → U is representable finite étale | `hV`, `v`, `hv : IsRepresentableFiniteModuliMap v`, `hve : IsEtaleModuliMap v`; no surjectivity is assumed |
| Stacks and 2-fibre products have the recorded meanings | `BasedCategory`, `BasedFunctor`, `IsDeligneMumfordModuliStack`, `moduliTwoFiberProduct`, `ModuliTwoIso`, from the existing dependency interface |
| Integral closure in all generic field factors | `IsModuliChartNormalization (v.comp j) ν i e.symm`; its chart model is Mathlib's `Scheme.Hom.normalization`, lifted to `Over S` by the existing `AlgebraicGeometry.Over.normalization` |
| These chart models and descent arrows define N | existential `N`, `ν`, `i`, `e`; the chart-normalization predicate compares not only models but the specified maps from the entire cover, which fixes the descent comparisons |
| N is normal and DM | `IsNormalModuliStack N` and `IsDeligneMumfordModuliStack N` |
| ν is representable finite | `IsRepresentableFiniteModuliMap ν` |
| Formation commutes with étale charts | the universal quantifiers in the recorded `IsModuliChartNormalization`: every normal finite-type étale scheme chart is represented by its relative integral closure, with its projection and dominant cover map |
| Canonical N ×_X U ≃ V over U | `(moduliTwoFiberLift v i e).toFunctor.IsEquivalence`; the functor is the specified map to the actual 2-fibre product, whose first projection is v |
| k perfect implies arbitrary field scalar extension compatibility | `PerfectField k → ModuliNormalizationScalarCharts (v.comp j)`; every field homomorphism k → k′ and every Cartesian model of T ×_k k′ is included |
| All generic components after extension | the target model is `(pullback.snd p.left q).normalization`, formed anew in the full pulled-back E, with no choice of an original generic factor; its isomorphism to the pullback of the old normalization respects both structural and dominant maps |

The use of relative normalization is intentional. I read `Mathlib.AlgebraicGeometry.Normalization`
in full at its construction and canonical maps. It takes the integral closure of
Γ(T,W) in Γ(E,p⁻¹W), not the absolute normalization of E. For the normal finite étale
cover of the dense open in this item, this equals the closure in the product of
all generic fields: every integral rational element belongs to every normal local
ring of E, hence is a regular section; conversely a section integral over the base
is integral in that rational algebra. This is precisely Steps 1–3 of the retained
node. The same argument applies to the completed regular chart. Thus the existing
relative-normalization declaration says the intended construction, without a
second function-field or integral-closure definition.

Hypotheses and conclusions of the formal paragraph:

| Node clause | Lean rendering |
|---|---|
| Algebraically closed Ω over the original field | the second declaration is over `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`; the scalar-chart clause of the first transports the original normalization to Ω |
| The normalization under discussion is N → X | `ν`, `i`, `e`, `hN`, `hn`, `hν`, `hchart`; these are the outputs of the first declaration after that identification, not an added assumption on the original X or cover |
| R is a complete regular Noetherian local Ω-algebra | `[CommRing R] [Algebra Ω R] [IsRegularLocalRing R]` and `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`; Mathlib's regular-local class extends both `IsLocalRing R` and `IsNoetherianRing R`, so these are not repeated overlapping instances |
| Effective Spec R → X with its Ω-structure | `Q`, `qR : Q.left ≅ Spec (.of R)`, `hQR`, and `f`; hQR identifies the given base structure with the specified algebraMap Ω R |
| Residue field identified with Ω and geometric point x | `σ : Over.mk (𝟙 (Spec (.of Ω))) ⟶ Q` and `hσ`; this is an Ω-valued closed point, equivalently the stated residue identification. The point x is `moduliChartMap σ f` |
| Formal chart [Spf R/H] | `H`, `[Group H] [Finite H]`, `ρ`, `θ : ModuliAtlasAction ρ f`, and `hf : IsFormalModuliQuotient ...` for support the closed point and completion along the residual gerbe of x |
| H is Aut(x) | this follows already from the full arrow clause of hf at σ: every automorphism is uniquely a group label, and the local ring action fixes its closed point. Thus H is identified with Aut(x), rather than a new unrelated group acting on R |
| Torsor meaning of quotient | `IsFormalModuliQuotient` uses local lifting on arbitrary covering sieves and the unique group-labelled isomorphisms; it includes descent of nontrivial torsors, not only globally trivial torsors or orbit sets |
| R° and E = V_Ω ×_U R° | `E`, `p`, `c`, `hc` represent the entire `Q ×_X V`. Since v factors through j, this is exactly that cover on the inverse image of U; no choice of a component or of a punctured principal open is imposed |
| B is the integral closure in all generic fields of E | the explicit model is `AlgebraicGeometry.Over.normalization p`. It is pinned by the relative integral-closure construction. Since the theorem asserts `IsFinite p.left.fromNormalization`, it is affine over Spec R and its affine coordinate ring is the stated B |
| B is complete, so Spf B is the indicated formal atlas | the explicit `IsAdicComplete` conclusion uses the extension of m_R along R → Γ(normalization p,⊤), namely ΓSpecIso.inv followed by qR.hom.appTop and fromNormalization.appTop |
| This model is the actual pullback of N | `b`, `β`, and the `moduliTwoFiberLift ... b β.symm` equivalence, with the specified projection to Q |
| Compatibility with the original cover and descent action | the additional `ModuliTwoIso` compares the map on all E through `Over.toNormalization p` with `c.comp (moduliTwoFiberMapRight f i e)`; `(ρB h).hom ≫ fromNormalization = fromNormalization ≫ (ρ h).hom`, and the following square requires β to intertwine θB with θ |
| No arbitrary comparison in that square | the existential equality ε only identifies the functors induced by these equal composite scheme maps; `eqToHom ε` is identity transport, not a separately chosen natural equivalence |
| Completed N above the entire gerbe equals [Spf B/H] | `IsFormalModuliQuotient ρB b θB` with support the full inverse image of the closed point and predicate `ModuliCompletionAt (moduliChartMap σ f) (t.comp ν)` |
| Geometric automorphism group above x is the stabilizer | the final universal z is an Ω-valued point of the full closed fibre. `Aut (moduliChartPoint (moduliChartMap z b)) ≃* MulAction.stabilizer ... z` uses Mathlib's subgroup, with the actual induced `moduliChartPointAction ρB`; its arrow condition identifies each automorphism with the actual inverse atlas-action arrow of its group label |
| Closed points b versus Ω-valued z | finiteness over the local R implies every closed b lies above m_R and has residue field finite over the algebraically closed Ω; its Ω-valued lift is unique. Thus the quantified z are exactly the closed points in the node |

The morphism p is supplied with `QuasiCompact` and `QuasiSeparated` instances solely
because Mathlib's relative-normalization construction takes these. They hold for
every representative of the specified cover: R is Noetherian and the cover is finite
étale over its open subset. The arbitrary representative E, the arbitrary affine
presentation Q ≅ Spec R, and the displayed base-change equivalences retain every
case; they do not strengthen the geometric hypotheses.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `CategoryTheory.IsModuliStack`,
  `IsDeligneMumfordModuliStack`, `IsRepresentableByAlgebraicSpaces`, `SpaceMapIsEtale`,
  `HasSpaceBaseChange`, `moduliTwoFiberProduct`, `ModuliTwoIso`, `discreteModuli`,
  `discreteModuliMap`, `moduliFiberMap` and their underlying `BasedCategory` interfaces.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `CategoryTheory.IsModuliChartNormalization`,
  `IsSchemeModuliBaseChange`, `IsEtaleModuliMap`, `moduliTwoFiberLift`,
  `moduliTwoFiberMapRight`; `AlgebraicGeometry.Over.normalization`, `fromNormalization`,
  `toNormalization`. Its main predicate and full docstring were read before use.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`: `CategoryTheory.IsRepresentableFiniteModuliMap`.
- `Sheaf.AlgebraicGeometry.ModuliStackProperties`: `CategoryTheory.HasSmoothFiniteTypeModuliAtlas`.
- Mathlib: `Field`, `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsFinite`, `IsIntegralHom`, `Etale`, `Smooth`, `IsOpenImmersion`,
  `PerfectField`, `IsRegularLocalRing`, `IsAdicComplete`, `MulAction.stabilizer`.
  The recorded definitions, full signatures and relevant docstrings were read.

All recorded proof-dependency modules are imported privately. The three still-unstated
proof prerequisites `lem-sfb-finite-schemes-etale-stack-descent`,
`lem-sfb-effective-formal-chart-completed-atlas`, and
`lem-sfb-finite-formal-quotient-pullback` have no module to import. They are proof
prerequisites, not notions necessary to type the two statements, and remain named
in the proof docstrings. No dependency module is repaired or silently replaced.

Edge cases checked before and after drafting:

- Empty X and empty chart: all chart and point assertions are vacuous as appropriate.
- V empty, including over a nonempty U: the relative integral closure is the zero
  algebra and its spectrum empty. Neither v nor ν is required surjective. The formal
  atlas can be empty and the final stabilizer assertion has no z.
- U = X and V = U: the original finite étale normal model is unchanged.
- Disconnected normal T and disconnected V: no integral-source or selected-factor
  hypothesis occurs. New generic factors after scalar extension are retained.
- k′ = k and an arbitrary Cartesian lift T′: both normalization arrows are compared;
  the formulation has no omission of identity or non-chosen pullback models.
- Imperfect k: the global normalization still exists; scalar compatibility is
  conditional on PerfectField. Over Ω the latter is automatically available.
- Wild finite H: no invertibility of its order or freeness hypothesis is used.
- Empty test schemes: group labels there are not unique, which is why the arrow
  uniqueness clause explicitly uses a nonempty test. Étale covers can have empty
  members. On nonempty tests even a trivially acting H retains its automorphisms.
- Arbitrary residue extensions and nontrivial H-torsors: completion tests quantify
  all algebraically closed extensions, and quotient tests permit étale local lifts.
- Scheme and stack universes: all universes are explicitly bound; the three input
  groupoids have independent size variables and the output is in their maximum
  with the scheme universe. No field/site universe equality is imposed.

Searches were actually run through the required msearch wrapper. The command-generated
`searches.jsonl` remains in the sandbox; each new node records the genuine tool, query,
hit count, returned names and digest. LeanFinder on finite normalization returned
`Scheme.Hom.normalization` and its canonical maps, which were read and reused through
the existing chart node. LeanSearch on dense opens returned ordinary scheme open
immersions and dominant maps; LeanFinder on dense open normal stacks returned the
same scheme notions. LeanSearch on formal quotient completions returned adic
completion and formal-smoothness ring results. The second LeanFinder quotient query
returned categories of finite group sets and topological covering maps. None is the
stack assertion or the missing tests. Loogle `"normalization"` returned Aesop
normalization infrastructure. Mathlib grep for Deligne/formal-completion names found
only a bibliographical mention; the exact new names returned zero matches. `rg` in
both `lean/WeilConjectures` and `lean/Sheaf`, the item-id search in WeilConjectures,
DAG grep and blueprint_refs searches were also run. The two blueprint searches
`formal quotient` and `dense open substack` returned zero matches. Existing chart,
finite-map, and smooth-atlas nodes were read and cited instead of duplicated.

Sources read: local spaces-morphisms.tex at 0ABP and 0BB0; varieties.tex at 038O;
spaces-groupoids.tex at the quotient-stack definition, action groupoid, stabilizer,
and quotient 2-Cartesian square. The tag table was checked, correcting the labels
in the new definition node: 044Q is the quotient definition, 0444 the action
groupoid, 0447 its stabilizer, 04M9 the 2-Cartesian square, and 044W the Isom
criterion. The primary [Pikaart--de Jong paper](https://arxiv.org/pdf/alg-geom/9501003),
Proposition 2.3.6 proof, printed p.11, was opened and read online: it describes the
finite complete normalization algebra on the effective chart and the quotient
formal completion. The item generalizes that formal argument as its existing source
record explicitly says. No new mathematical correction or disputed statement was found.

## Dependency modules

`def-sfb-formal-moduli-quotient`: `6ecc4f743596` registered this definition
without a Lean record. This delivery supplies `FormalModuliQuotient.lean`, its
original declarations and its `lean` record. The `lean.note` explains the absent
interface and the coherent atlas action/formal completion/quotient notions supplied.

`def-sfb-moduli-normalization-tests`: the same commit registered this definition
without a Lean record. This delivery supplies `ModuliNormalizationTests.lean`,
its original declarations and its `lean` record. The `lean.note` explains the
absent interface and the dense-open, normality and scalar-chart tests supplied.

The following original new-node section retains the source and search rationale.
Both definitions are existing prerequisites on the current base.

## Originally new definitions: source and searches

`def-sfb-moduli-normalization-tests` owns
`Sheaf.AlgebraicGeometry.ModuliNormalizationTests`. It supplies the previously
missing dense-open and normal-stack scheme tests, and the chartwise scalar-extension
compatibility of the existing relative-normalization construction. Its source is
0ABP/038O and the standard stack scheme tests. It introduces no new normalization,
finite-map or smoothness predicate. It cites the recorded chart-normalization node
and the existing scheme definitions. Its searches are retained as actual results.

`def-sfb-formal-moduli-quotient` owns
`Sheaf.AlgebraicGeometry.FormalModuliQuotient`. It defines coherent atlas actions,
completion along a residual gerbe, and the local objects-and-arrows test for a formal
torsor quotient. The helpers give the actual geometric fibre object and induced
point action. Stabilizers use Mathlib's `MulAction.stabilizer` directly. The source
is the action-groupoid/quotient-stack definitions in spaces-groupoids.tex and the
formal chart in Pikaart--de Jong §2.3.6. Searches found no corresponding Lean or DAG
notion. The missing support and action interfaces are real definitions; no existence
or equivalence is asserted by definition.

The item also gains the already-landed definition nodes
`def-sfb-moduli-chart-normalization`, `def-sfb-finite-stack-scheme-tests` and
`def-sfb-moduli-stack-properties` in `stmt_deps`. This is reuse of their published
interfaces, not a dependency replacement. The new nodes have no proof dependencies.

## Validation

The required scompile wrapper compiled the modules separately in dependency order
against the live server sources and published build. Initial elaboration fixes were
ordinary missing import/name errors and identity transport in the equivariant
comparison; the overlapping local/Noetherian instances were removed since they are
already fields of IsRegularLocalRing. The final required compile, dry run and
push results are recorded below when completed.

## Second reading by NI

A fresh self-reading of the node and all three files was performed; no independent
worker was started, as the dispatcher forbids that. The maintainer's independent
review remains required. This reading caught the missing cover-map comparison in
the formal clause, and added the `ModuliTwoIso` through `Over.toNormalization p`.
It also replaced a hand-written subgroup carrier by Mathlib's stabilizer under an
explicit induced action, and pinned the group identification to the actual action
arrow, rather than an unspecified abstract group isomorphism. The formal equivariance square uses identity transport of
equal functors. Every hypothesis and clause is matched in the tables above. There
is no assertion of surjectivity, chosen generic factor, tame stabilizer, originally
algebraically closed base field, or global trivialization of torsors. Both theorem
proofs remain sorry, and every new definition has real data.

The final dry run returned `OK (dry run): commit bf75495a8b5 passes the
preflight and compiles; nothing pushed`. All three delivered Lean modules passed
separate server compilation; only the expected theorem `sorry` warnings remain.
The first dry run's citation/dependency formatting failures were repaired before
this successful rerun. The final delivery is performed with the prescribed
`deliver2.py` wrapper; its resulting commit is reported in the worker's delivery
answer.


## Repair of the returned delivery

Return L on immutable head `5bb4823e5b7d` identified two unreachable
prerequisites without the required metadata: `def-sfb-formal-moduli-quotient`
and `def-sfb-moduli-normalization-tests`. Maintenance commit `6ecc4f743596`
has now registered both definitions on the current base with `lean: null`
and `import_flags: ["unreachable"]`. Both sandbox copies preserve that
base metadata exactly and change only `lean`. The requested reachability
repair therefore remains in force without delivering maintainer-owned fields.

The first prescribed saved-packet dry run in this session compiled all three
modules, then diagnosed the newly registered nodes as dependency modules:
both required `lean.note`, and the report required `## Dependency modules`.
The retained packet now has both explanatory notes and that section above.
Its modules and mathematical statements are unchanged. These are real
interface/report repairs relative to the returned head, not an unchanged re-push.

Self-check: both dependency records differ from the current read clone only in
`lean`; both base records have no usable declaration and carry the required
unreachable flag. The item reuses these definitions and the three published
chart/finite-map/smooth-atlas interfaces. All definitions retain actual data;
only the two theorem proofs use `sorry`. The clause-by-clause statement and
edge-case checks above remain applicable. The prescribed wrapper supplies the
current-base rebase and recompiles every delivered file before preflight.

Final repaired dry run: `5ff8da32ee0` passed server preflight and compiled
all three modules cleanly, apart from the expected theorem `sorry` warnings.
The item copy was also refreshed to preserve current maintainer-owned metadata;
its only delivery changes remain `lean` and the documented `stmt_deps` additions.
