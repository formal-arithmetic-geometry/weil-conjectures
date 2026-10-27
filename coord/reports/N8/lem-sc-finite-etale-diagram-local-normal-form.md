## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleDiagramLocalNormalForm` states
`AlgebraicGeometry.finiteEtaleDiagramLocalNormalForm`, with its only proof `sorry`.
It introduces no definitions and requires no dependency repair or statement correction.
The module docstring cites Stacks 0BN9; the theorem docstring contains all five proof
steps of the node, including construction of inverse trivializations and the
functor-law argument on the nonempty refined neighbourhoods.

Clause-by-clause reading:

- The scheme Y is `(Y : Scheme.{u})`.
- The finite indexing category is `{I : Type v} [SmallCategory I] [FinCategory I]`.
  Mathlib's `FinCategory` supplies finitely many objects and finitely many arrows in
  each hom-set, hence finitely many arrows in total. The index universe v is independent
  of u; finite indexing categories in any universe are allowed.
- The diagram of finite étale Y-schemes is
  `(D : I ⥤ (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y)`.
  This is exactly the specialization prescribed by def-weil-pbc-finite-etale-category.
  Its morphisms are all scheme morphisms over Y, without an extra condition on arrows.
- A set-indexed family is `∃ (Λ : Type u) (U : Λ → Scheme.{u})
  (a : ∀ l, U l ⟶ Y)`. The statement asserts existence of a small family, not a
  bound on any input family: indexing a choice of neighbourhood at each point of Y
  suffices, and the node's finite construction likewise uses only sets in Type u.
- Every covering map is étale: `(∀ l, Etale (a l))`.
- The images cover Y: `(∀ y : Y, ∃ (l : Λ) (x : U l), (a l) x = y)`.
  This asserts joint surjectivity and imposes no surjectivity on individual maps.
- For each cover member the functor is `∀ l : Λ, ∃ S : I ⥤ Type u` and finite
  values are `(∀ i : I, Finite (S.obj i))`. Functor laws are part of `S`.
- The objectwise isomorphisms are `∃ e : ∀ i : I,
  pullback (D.obj i).hom (a l) ≅ ∐ (fun _ : S.obj i ↦ U l)`.
  The pullback is the specified D(i) ×_Y U_l, with the specified factor order.
- Being isomorphisms of U_l-schemes is the equation
  `(e i).hom ≫ Sigma.desc (fun _ : S.obj i ↦ 𝟙 (U l)) =
  pullback.snd (D.obj i).hom (a l)`. A scheme isomorphism commuting with structure
  maps has inverse commuting with those maps as well, so this states precisely an
  isomorphism over U_l, without an extra choice or hypothesis.
- The arrow condition universally quantifies `(i j : I) (f : i ⟶ j) (s : S.obj i)`.
  The conjugated arrow, precomposed with `Sigma.ι ... s`, equals
  `Sigma.ι ... (S.map f s)`. The intervening map is exactly the `.left` scheme map
  of `(MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ (a l)).map (D.map f)`.
  Equality of these scheme morphisms asserts identity on the base copy, not just
  a condition on its image or underlying points.
- The finite sets may vary with l: S is existentially bound inside `∀ l`. No constant
  rank, connectedness, nonemptiness, quasi-compactness, or separatedness is assumed.

Dependency declarations read and used:

- def-weil-pbc-finite-etale-category is a Mathlib match: `MorphismProperty.Over` in
  `Mathlib.CategoryTheory.MorphismProperty.Comma`, and `MorphismProperty.Over.pullback`
  in `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`. These are used directly
  with `@IsFinite ⊓ @Etale` and top arrow property.
- def-galois-finite-limits-colimits records `CategoryTheory.Limits.HasFiniteLimits` and
  `HasFiniteColimits` in `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`; their
  signatures specify `SmallCategory` and `FinCategory`. We import that module publicly
  and use its finite-category notion, not a replacement definition.
- lem-weil-pbc-scheme-coproduct-family matches the scheme coproduct instance,
  `AlgebraicGeometry.sigmaOpenCover`, and `disjoint_opensRange_sigmaι` in
  `Mathlib.AlgebraicGeometry.Limits`; its chosen coproduct `∐`, coprojections `Sigma.ι`,
  and universal map `Sigma.desc` occur directly in the statement.
- def-weil-etale-morphism is `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, used on the covering maps.
- Proof imports are `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`
  (`AlgebraicGeometry.finite_etale_etale_local_split`),
  `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`
  (`AlgebraicGeometry.coproductCopiesMorphismsClopen`), and
  `Mathlib.CategoryTheory.Extensive`
  (`CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts`).
  The étale composition/cancellation dependency is in the publicly imported Etale
  module (`Etale.etale_comp`, `Etale.of_comp`, and the open-immersion instance).
  def-pc-fibre-product is `CategoryTheory.Limits.pullback`, with `pullback.fst` and
  `pullback.snd`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  publicly supplied by the imported scheme limits and over-adjunction modules.

Sources read: `literature/stacks-project/pione.tex`, the whole statement and proof of
`lemma-finite-etale-covers-limits-colimits` (0BN9), and the current blueprint
`literature/blueprint/latest/blueprint/sec-curve-estimates/sk-thm-br/lem-fet-finite-limits`
(statement and proof). The current blueprint has a revised finite-group quotient
route, while this auxiliary node retains its independent 0BN9 finite-diagram extension.
No source discrepancy affects the auxiliary statement.

Edge cases checked before drafting and again against the Lean:

- Empty Y: Λ may be empty; coverage is vacuous; no witness S or e is demanded.
- Empty I and nonempty Y: the identity covering works; S and e have empty domains,
  and all arrow equations are vacuous. `FinCategory` does not require nonemptiness.
- A degree-zero object: its S.obj i may be empty; the coproduct is the empty scheme,
  and the arrow clause over its source has no s.
- A nonempty sheet set cannot map into an empty target on a nonempty cover member;
  this follows from existence of the original arrow and is not a new hypothesis.
- Disconnected Y with distinct degrees on its components: each l has its own S,
  so no false global degree equality results.
- Empty cover members are permitted; no point is required on every U l.
- Identity and composite arrows are included and the finite-set functor laws are
  imposed, rather than independent arbitrary sheet functions.
- Arbitrary universe v for the finite category; values S.obj i and cover indices
  can be represented in Type u since the former are finite and Y has a Type u point set.

Searches (2026-10-24), all through the prescribed msearch.py or read-only rg:

- LeanFinder: "Every finite diagram of finite etale schemes is etale locally a diagram
  of constant finite sets". Eight hits: smallEtalePretopology, smallEtaleTopology,
  Scheme.instCategoryEtale, Scheme.instHasPullbacksEtale, etalePretopology,
  etaleTopology, an étale postcomposition instance and FormallyEtale.instForallOfFinite.
  None states simultaneous normalization of a diagram.
- Loogle: "AlgebraicGeometry.Etale, CategoryTheory.Functor". No hits.
- LeanSearch: "Finite diagrams of finite etale schemes simultaneously split etale
  locally with all arrows induced by maps of finite sets". Eight hits, including
  the étale sites, Etale, Scheme.Etale, FintypeCat.finiteLimitOfFiniteDiagram and
  ExistsHomHomCompEqCompAux; none is this assertion.
- Mathlib grep: `finite.*diagram|diagram.*finite|locally.*trivial|FiniteEtale`,
  AlgebraicGeometry directory. Four unrelated hits in Properties.lean and
  ColimitsOver.lean; no match.
- Project rg: `finite.*diagram|diagram.*finite|FiniteEtale|finite_etale.*local`
  in both `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`.
  Reviewed the local-splitting module, the finite-limits module, and relevant finite
  étale interfaces; none asserts a simultaneous finite-diagram normal form.
- Project rg for the exact node id and both anticipated names
  `finiteEtaleDiagramLocalNormalForm|finite_etale_diagram_local_normal_form` in
  `lean/WeilConjectures` and `lean/Sheaf`: no matches before creating the sandbox file.

Validation: scompile.py N8 lem-sc-finite-etale-diagram-local-normal-form compiled
this single file on the server in both sandbox and library module modes, cleanly
(1.6 seconds each). `set_option autoImplicit false` binds every variable explicitly.
No new nodes, dependency modules, statement faults, or STATEMENT-DISPUTED flags.

## Second reading by N8

A second in-thread reading opened the node and the delivered signature after compilation.
The dispatcher explicitly forbids starting another agent; independent mathematical
review is performed by the maintainer as specified in this assignment. This section
records the worker's own second pass, not a claim of an independent second worker.

The pass rechecked all node clauses: the actual FEt over-category, finite indexing
category, jointly covering étale family, one finite-valued functor per member, scheme
coproducts of the same member, isomorphisms over that member, and the precise identity
map on every designated target summand for every arrow and source sheet. In particular,
the equation uses `(e i).inv` followed by the canonical base-changed D.map f and
`(e j).hom`, in the same order as the node's conjugation. The structural equation
ensures this is over U l. The quantifier order permits varying degrees and retains
all empty cases. No mismatch was found and no correction was made.
