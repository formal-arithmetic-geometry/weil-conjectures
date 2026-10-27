## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothCoverFlatLfpDescent` states
`CategoryTheory.smooth_cover_flat_lfp_descent`, with its entire proof postponed as `sorry`.
It introduces no definitions. The source is Stacks Tag 06M2,
`stacks-properties.tex`, lemma-check-property-after-precomposing, specialized separately
to flatness and local finite presentation. I read that lemma and the source-locality
statements in `spaces-descent.tex`, Tags 06ET and 06EV. The docstring reproduces all
four proof steps of the node, including their named inputs.

Correspondence of every hypothesis and conclusion:

| Node text | Lean rendering |
| --- | --- |
| Base scheme S | `{S : Scheme.{u}}` |
| Algebraic stacks A, B, C over S | Three `BasedCategory (Over S)` binders, with `hA`, `hB`, `hC : IsAlgebraicModuliStack ...` |
| A → B → C | `h : BasedFunctor A B`, `g : BasedFunctor B C` |
| Both maps representable by algebraic spaces | `hh : IsRepresentableByAlgebraicSpaces h`, `hg : IsRepresentableByAlgebraicSpaces g` |
| h smooth | `hsmooth : ModuliSpaceTest @Smooth h` |
| h surjective, with field-extension lifting | `hsurj : IsSurjectiveModuliMap h` |
| If gh flat then g flat | First implication `ModuliSpaceTest @Flat (h.comp g) → ModuliSpaceTest @Flat g` |
| If gh locally of finite presentation then g likewise | Second implication with `@LocallyOfFinitePresentation` |
| The assertions are separate | Conjunction of implications; neither composite property is assumed by the other implication |
| No quasi-compactness of h | There is no quasi-compactness binder or restriction on h or its charts |
| Algebraic stack means étale stack, space diagonal, smooth surjective scheme atlas | Exactly the three clauses of the existing `IsAlgebraicModuliStack` predicate |
| Stack maps and 2-fibre products retain groupoid data | `BasedFunctor`, `HasSpaceBaseChange`, and `ModuliTwoIso` in the recorded dependency module |
| Properties checked after scheme base change on étale scheme charts | Exactly the existing `ModuliSpaceTest P`; it gives an algebraic-space presentation of each actual 2-base change and tests P after every representable étale scheme chart |
| Surjectivity after extension of every field-valued point | The existing `IsSurjectiveModuliMap` quantifies K, an object over Spec K, L, a field map K → L, and a lift with a 2-isomorphism to the restricted original object |

The stacks have independent object and morphism universes `v₁,w₁,v₂,w₂,v₃,w₃`.
Schemes and field tests use the fixed scheme universe u, following the dependencies;
there is no extra equality between any stack universe and u.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.BasedCategory`, `BasedFunctor` (Mathlib types reexported there),
  `IsModuliStack`, `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `SpaceMapIsEtale`, and `SpaceMapIsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, and `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose
  affine-local definition agrees with stalkwise flatness by `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `CategoryTheory.IsAlgebraicModuliStack`
  and its `SpaceMapIsSmooth` and `IsSmoothModuliAtlas` components.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `CategoryTheory.ModuliSpaceTest`.
  Despite its module name, this definition takes arbitrary based categories, not DM
  hypotheses, and is precisely the source-local test needed here.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `CategoryTheory.IsSurjectiveModuliMap`, `stack_chartwise_smooth_etale_calculus`,
  `stack_chartwise_comp`, and `surjective_moduli_iff_chartwise`.

The three already landed owning nodes for `IsAlgebraicModuliStack`, `ModuliSpaceTest`,
and `IsSurjectiveModuliMap` are appended to stmt_deps. These are
`def-sfb-algebraic-moduli-stack`, `def-sfb-dm-stack-morphism-properties`, and
`def-sfb-surjective-moduli-map`. The surjectivity definition node records the plain
predicate in `StackChartwiseSmoothEtaleCalculus`; the theorem node remains solely
in proof_deps. No mathematical statement, proof,
or other existing-node field is changed.

The available proof-dependency modules are imported privately:
`SchemeEtaleSourceTargetProperties`, `SpaceEtalePresentationPropertyCriterion`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat` (the existing proved
`Flat.of_comp_of_flat_of_surjective`), and
`Morphisms.LocallyOfFinitePresentationFppfSource`
(`locallyOfFinitePresentation_iff_of_fppf_source_family`).
The chartwise calculus and algebraic-space definitions are already public imports
because their declarations occur in the signature. The proof node
`lem-sfb-representable-pullback-over-space` has no recorded Lean module in the read
clone, so there is no import for it; no signature notion depends on its theorem.

Edge cases checked before writing:

- An empty A cannot cover a nonempty B: field-lifting surjectivity excludes that
  case, rather than giving descent from a vacuous property of the empty composite.
  If B is empty, the conclusions are vacuous scheme-chart properties as they should be.
- If h is the identity, each implication reduces to the corresponding identity
  implication. If g is the identity, its two properties hold without extra hypotheses.
- An infinite disjoint union of copies of a nonempty scheme mapping to that scheme
  is a smooth surjection which need not be quasi-compact. It is admitted by the
  signature; the proof uses source-local descent, not a global quasi-compact cover.
- Flatness of the composite alone does not imply local finite presentation, nor
  does its local finite presentation imply flatness. The conjunction of independent
  implications never makes either inference.
- No restriction on characteristic, separatedness, finite type of the base, or
  nonemptiness is introduced. Field extension in surjectivity is an arbitrary
  unital field map, with the actual base-change 2-isomorphism retained.

Searches for an existing statement (raw remote results also recorded by msearch.py
in searches.jsonl):

- LeanFinder: “For representable morphisms of algebraic stacks, flatness and local
  finite presentation descend through a smooth surjective source cover”. Eight
  scheme/algebra hits, including fppf descent of morphism properties and smooth
  implies flat/locally finitely presented; no stack source-descent theorem.
- Loogle: `"Smooth", "Surjective", "Flat"`. Two hits: scheme smoothness descent
  along a flat quasi-compact surjection, and an unrelated formally smooth ring lemma.
- LeanSearch: “Flatness and locally finite presentation descend after a smooth
  surjective morphism of algebraic stacks”. Eight scheme/ring hits, no stack result.
- msearch grep in Mathlib AlgebraicGeometry:
  `smooth.*(descent|[Ff]lat|[Ff]inite[Pp]resentation)|[Ff]lat.*of_comp`.
  Nine hits about scheme smoothness/flatness and local finite presentation; no match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the statement name,
  smooth-cover descent, and `ModuliSpaceTest.*of_comp`: no existing theorem matching
  this node. rg for this node id in `lean/WeilConjectures`: no result.
- Searches for `SpaceMap`, `IsAlgebraicModuliStack`, `ModuliSpaceTest`, and
  `IsSurjectiveModuliMap` found the existing canonical vocabulary used above, so no
  new helper notion or dependency module is needed.

There is no statement dispute or source correction.

## Second reading by NO

I reread the JSON statement and final Lean signature directly after writing them.
This is a separate self-check, not an independent agent review: the dispatcher
explicitly forbids starting other agents, and the maintainer performs the independent
review after delivery.

The rereading matched S and all three algebraic stacks, the ordered pair of maps,
the two representability assumptions, smoothness and field-extension surjectivity
of h, and both independent conclusions. I inspected `ModuliSpaceTest` to check
that it retains the actual projection of each scheme 2-base change and tests all
étale charts, and inspected `IsSurjectiveModuliMap` to check its extension and
2-isomorphism. I checked `BasedFunctor.comp` usage against the existing chartwise
composition theorem: `h.comp g` is the composite A → C. The stack universes remain
independent; no quasi-compactness or DM hypothesis is hidden in the signature.
No mismatch was found and no statement correction was needed. Only the three
already landed owning nodes were added to stmt_deps to account for the vocabulary.

Validation: `scompile.py NO lem-sfb-smooth-cover-flat-lfp-descent` compiled the
file successfully both as a sandbox module and under its final library name
(3.8 s and 3.5 s respectively), without compiler diagnostics. The prescribed
`deliver2.py ... --no-push` passed the server preflight and per-file compilation.


## Returned delivery repair

H2, returned immutable head `21b9728fb2f8`: replaced the added statement dependency
`lem-sfb-stack-chartwise-smooth-etale-calculus` with the landed definition owner
`def-sfb-surjective-moduli-map` (Q87, existing:true). I opened this live definition
node and the declaration at `StackChartwiseSmoothEtaleCalculus.lean:69`: its
`CategoryTheory.IsSurjectiveModuliMap` is the same plain field-extension-local
predicate used in `hsurj`, with no theorem conclusion or `.choose` involved.
The chartwise theorem remains unchanged in proof_deps. Updated lean.note and the
owning-node paragraph above. The Lean module is unchanged from the returned head.
Compared the retained node with current main: all fields apart from lean and the
authorized added stmt_deps agree. The delivery wrapper rebases onto current main.

Repair rereading: the signature still has exactly the hypotheses and two separate
implications checked by the maintainer. Each of the three newly added stmt_deps
now names a landed definition node: `def-sfb-algebraic-moduli-stack`,
`def-sfb-dm-stack-morphism-properties`, and `def-sfb-surjective-moduli-map`.
The statement/proof dependency distinction in H2 is therefore repaired without
changing any mathematical content or Lean source.
