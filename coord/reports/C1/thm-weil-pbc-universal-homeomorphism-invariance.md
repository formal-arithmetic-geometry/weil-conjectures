## Worker report

The module `lean/Sheaf/AlgebraicGeometry/UniversalHomeomorphismInvariance.lean`
states `AlgebraicGeometry.Etale.universalHomeomorphism_invariance`, with one
`sorry` and no new definition. The item's statement, dependencies and proof are
unchanged; only its `lean` record is set. The theorem collects the topological
invariance input and the identity, composition and cartesian-square compatibility
specified by this node, rather than redefining any of its functors or maps.

Sources read: the item's full node and all seven statement-dependency nodes;
their recorded source declarations and docstrings; the blueprint module at
`literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/thm-weil-pbc-universal-homeomorphism-invariance.md`
(read on the server, since literature is not populated on this machine);
[Stacks 04DZ](https://stacks.math.columbia.edu/tag/04DZ) and
[Stacks 03SI](https://stacks.math.columbia.edu/tag/03SI).
The blueprint states the full compatibility assertion, and its proof explicitly
identifies inverse/direct image with the equivalence, its unit/counit with
isomorphisms, and its base-change square with inverse-image functors.

Hypotheses and clauses, in the order of the Lean conjunction:

- `X X' : Scheme.{u}`, `u : X' ⟶ X` and `[IsUniversalHomeomorphism u]`
  render exactly the scheme morphism and universal-homeomorphism assumption.
  There is no finiteness, separation, Noetherian, field, or coefficient-torsion
  hypothesis. The universe identifier `u` and the morphism identifier `u` are
  in Lean's separate universe and term namespaces.
- `u.Etale.IsEquivalence` states the equivalence of the underlying small etale
  categories induced by the morphism of sites: the functor is the recorded
  scheme-theoretic base-change functor, not an arbitrary equivalence.
- For each `I : Type w`, `V`, `Vᵢ` and `a : ∀ i, Vᵢ i ⟶ V`, the covering-sieve
  equivalence for `Sieve.ofArrows Vᵢ a` and the family `u.Etale.map (a i)`
  renders preservation AND reflection of covering families. Membership in
  `smallEtaleTopology` means joint surjectivity of that family. Independent
  `w` permits arbitrary set-indexed families, not just finite families.
- The existential `E : Sheaf X.smallEtaleTopology (Type (u+1)) ≌
  Sheaf X'.smallEtaleTopology (Type (u+1))` is the displayed equivalence of
  small etale topoi. `E.functor = Scheme.etaleSetPullback u` and
  `E.inverse = lowerStar (Type (u+1)) u` specify its inverse and direct images.
  Equalities here pin down the functors themselves; their unit/counit are part
  of the equivalence structure.
- `IsIso` of the unit and counit of
  `upperStarLowerStarAdjunction AddCommGrpCat.{u+1} u` renders the same
  inverse/direct-image equivalence on abelian sheaves, with the recorded
  adjunction and its specified unit and counit. This is the abelian form used
  for the cohomology clause, not a replacement of the set-valued topos clause.
- For every abelian sheaf `F` and `q : ℕ`,
  `Function.Bijective (cohomologyMap u F q)` says that the specified cohomology
  pullback is an isomorphism of abelian groups in every nonnegative degree.
- Identity compatibility: the four `Nonempty` natural-isomorphism clauses
  identify set-valued and abelian inverse/direct images of `𝟙 X` with their
  identity functors. The equality
  `Sheaf.H.map ((upperStarId ... X).hom.app F) q
    (cohomologyMap (𝟙 X) F q x) = x`
  asserts identity compatibility of the cohomology map using the CANONICAL
  identity comparison, for every `F`, `q`, and class `x`.
- Composition compatibility: for any `v : X'' ⟶ X'` that is a universal
  homeomorphism, the four natural-isomorphism clauses identify inverse image
  of `v ≫ u` with inverse image of `u` followed by inverse image of `v`, and
  direct image with direct image of `v` followed by direct image of `u`, for
  sets and abelian groups. In Lean `v ≫ u` is the paper's `u ∘ v`.
  The final equality in this block uses
  `(upperStarComp AddCommGrpCat v u).inv.app F` to identify the iterated
  inverse image with the composite inverse image; it states that applying
  `cohomologyMap u` and then `cohomologyMap v` gives `cohomologyMap (v ≫ u)`.
- Pullback compatibility: for arbitrary `g : Y ⟶ X`, use
  `Y' = pullback g u`, `u' = pullback.fst g u`, and `g' = pullback.snd g u`.
  The first four clauses record that the base-changed morphism is a universal
  homeomorphism with the same abelian inverse/direct-image and cohomology
  equivalences. The next four natural-isomorphism clauses are the square
  `u^{-1} ⋙ g'^{-1} ≅ g^{-1} ⋙ u'^{-1}` and its quasi-inverse form
  `g'^{-1} ⋙ u'_* ≅ u_* ⋙ g^{-1}`, for sets and abelian groups.
  The final equality maps the two iterated cohomology pullbacks to the SAME
  group for `(pullback.fst g u ≫ g)^{-1} F`, using the canonical inverses
  of the two `upperStarComp` isomorphisms. `pullback.condition` is passed
  only to identify the two composite scheme maps; it is not asserted as a
  tautological conclusion. This equality is the cohomology square in proof
  step 5 of the node, for every `F`, `q`, and class `x`.

For sheaf compatibility, `Nonempty` of a functor isomorphism means a natural
isomorphism, not an unrelated objectwise identification. The cohomology
identities use the recorded canonical comparisons, so they do not merely
assert that some abstract group isomorphisms exist.

Dependency declarations used:

- `def-weil-pbc-scheme-conventions` is a convention record, not a declaration.
  Its universal-homeomorphism entry points to the source's
  `AlgebraicGeometry.IsUniversalHomeomorphism` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`:
  integral, universally injective and surjective, equivalent to the stated
  base-change definition (Stacks 04DF). Its composition/base-change instances
  are inherited through the main import.
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.Etale` and
  `AlgebraicGeometry.Scheme.smallEtaleTopology`,
  `Mathlib.AlgebraicGeometry.Sites.Etale`. The declaration
  `Scheme.ofArrows_mem_smallEtaleTopology_iff` verifies the covering encoding.
  `Scheme.Hom.Etale`, provided upstream, is its base-change functor.
- `def-weil-pbc-etale-sheaves`: `CategoryTheory.Sheaf` and the landed
  `AlgebraicGeometry.Scheme.etaleSetPullback` in
  `Sheaf.AlgebraicGeometry.EtaleSheaves`. The recorded module was read in full;
  its other predicates are not needed by this node.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and
  `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in that
  same module. Its derived direct image is not part of this theorem.
- `def-weil-pbc-etale-cohomology` records the derived `Etale.cohomology` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`. As explicitly
  allowed by that record and the cohomology-pullback record, this theorem
  uses `CategoryTheory.Sheaf.H F q`, the existing Ext model used by upstream
  PBC statements. Agreement with the K-injective-resolution model is the
  shared stage-3 bridge mentioned by those records. No duplicate cohomology
  definition or extra import of the unused derived construction is introduced.
- `def-weil-pbc-cohomology-pullback`: `AlgebraicGeometry.Etale.cohomologyMap`
  in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.
  Also used: `CategoryTheory.Sheaf.H.map` from Mathlib's sheaf cohomology;
  `Etale.upperStarComp` from `UpperLowerStar.Defs` and `Etale.upperStarId`
  from `UpperLowerStar.Coherence`. Their full signatures and orientations
  were read; the comparison `(v ≫ u)^* ≅ u^* ⋙ v^*` is inverted when mapping
  the cohomology of the iterated pullback to that of the composite pullback.

Edge cases checked before and during writing:

- Empty schemes are allowed. All equivalences and pullback expressions still
  make sense; no nonempty scheme assumption appears.
- `I = Empty` is allowed: the empty family covers precisely an empty etale
  object, and universal homeomorphism preserves and reflects that case.
- Singleton and arbitrary infinite covering families are covered, with no
  restriction on their index universe.
- The zero abelian sheaf and degree `q = 0` are included; bijectivity and the
  identity/composition equations then have their usual literal meanings.
- Identity morphisms, nilpotent thickenings and purely inseparable extensions
  all satisfy the same hypothesis. No characteristic is excluded.
- Arbitrary `Y` and `g`, including the empty scheme and non-etale `g`, appear
  in the cartesian-square block. The functors are defined for arbitrary scheme
  morphisms; only `u` (and `v` in the composition block) is assumed to be a
  universal homeomorphism.
- Scheme universe `u` is explicit throughout; values are sets and abelian
  groups in `u+1`, as prescribed by the existing site/sheaf declarations.

Searches (using `/home/ubuntu/weil-launcher/msearch.py`, group C1, this item):

- LeanFinder: `universal homeomorphism invariance of etale topoi and cohomology
  compatible with composition and base change`: eight hits, on etale schemes,
  sites and morphisms; no statement of the full node.
- Loogle: `AlgebraicGeometry.Etale.cohomologyMap,
  AlgebraicGeometry.Etale.upperStarComp`: zero hits, upstream identifier not
  known to the Mathlib search service.
- Mathlib grep: `universal.*[Ii]nvariance|cohomologyMap.*comp|upperStarId`:
  zero hits.
- LeanSearch: `universal homeomorphism induces equivalence of etale sheaves
  compatible with composition and pullback on cohomology`: service unavailable
  (Internal Server Error), recorded as unavailable, not a negative search.
- Source `rg` for `cohomologyMap.*comp|cohomologyMap.*id|upperStarId` found
  the upstream identity/composition isomorphisms and individual cohomology
  results, but no full invariance theorem with the compatibility clauses.
- Source `grep -rn` of the item id found no declaration for this node.
- Project `rg` for `cohomologyMap`, universal-homeomorphism names and
  invariance found citers and other cohomology nodes, not this statement.
- Full proposed declaration-name search in Mathlib, upstream, `lean/Sheaf`
  and `dag/lean_names_upstream.json` found no collision;
  `tools/lean_names_upstream.py show` was consulted too. The node's own
  upstream audit has no declarations.

Validation: server single-file compile succeeded in 2.4 seconds with no
warnings. Initial compiler errors were the implicit arguments and equality
orientation of `pullback.condition`; both were repaired. There are no
`#check` lines, local notation, local instances, auto-bound variables or
hollow definitions. No node fault or disputed statement was found.
The independent second reading is left to the next worker.

## Second reading by C1

Independent reading of the sandbox node and module, all seven statement-dependency
records, their relevant declarations, and the original blueprint. I read the
blueprint and Stacks `etale-cohomology.tex` on the server (the local literature
files are absent), specifically `section-topological-invariance` (04DY),
`theorem-topological-invariance` (04DZ), and
`proposition-topological-invariance` (03SI). The section imposes no additional
ambient hypothesis: 04DZ assumes integral, universally injective and surjective,
and 03SI assumes precisely a universal homeomorphism. The following is my
object/hypothesis/conclusion checklist, made against the actual Lean signature.

- Objects: arbitrary schemes X and X', and a morphism u from X' to X.
  Lean: `{X X' : Scheme.{u}} (u : X' ⟶ X)`. Verdict: exact. The universe and
  term named u occupy separate namespaces; no variable is auto-bound.
- Hypothesis: u is a universal homeomorphism. Lean:
  `[IsUniversalHomeomorphism u]`. Verdict: exact. I opened the source class:
  it extends `IsIntegralHom`, `UniversallyInjective`, and `Surjective`, the
  equivalent characterization used in 04DZ; it is not just a homeomorphism
  of the original underlying spaces. No Noetherian, finite presentation,
  separatedness, nonemptiness, field, or torsion hypothesis is added.
- Sites and their induced morphism: Lean `u.Etale.IsEquivalence` uses the
  scheme base-change functor on `X.Etale`, not an arbitrary categorical
  equivalence. The category and topology are the recorded Mathlib
  `Scheme.Etale` and `Scheme.smallEtaleTopology`. Verdict: exact.
- Preservation and reflection of covering families: Lean universally
  quantifies I, V, Vᵢ, and a, and states the iff of membership of
  `Sieve.ofArrows Vᵢ a` and of the base-changed family in the two topologies.
  I read `Scheme.ofArrows_mem_smallEtaleTopology_iff`: that membership is
  exactly joint surjectivity, for arbitrary index types. Verdict: exact,
  including reflection; it does not replace the family by a finite cover.
- Small etale topoi: Lean `∃ E : Sheaf X.smallEtaleTopology (Type (u + 1)) ≌
  Sheaf X'.smallEtaleTopology (Type (u + 1))`. Verdict: exact with the
  dependency's chosen set universe. The two following equalities identify
  E.functor with `Scheme.etaleSetPullback u` and E.inverse with
  `lowerStar (Type (u + 1)) u`. I read the former's landed body (Kan extension
  followed by sheafification) and the latter's upstream body (restriction
  along base change). Verdict: these are the specified inverse/direct images.
  Equality of the functors is harmless: an equivalence structure can use
  these adjoint quasi-inverse functors themselves.
- Abelian inverse/direct image compatibility: Lean asserts `IsIso` of the
  unit and counit of `upperStarLowerStarAdjunction AddCommGrpCat u`.
  I read `upperStar`, `lowerStar`, and the adjunction in `UpperLowerStar.Defs`.
  Verdict: exact abelian-sheaf equivalence, with the recorded adjunction,
  rather than an unrelated pair of equivalences.
- Cohomology: for every abelian sheaf F and every q : ℕ, Lean asserts
  `Function.Bijective (cohomologyMap u F q)`. The source signature makes this
  map an additive homomorphism from `Sheaf.H F q` to the cohomology of the
  specified inverse image, so bijectivity is precisely a group isomorphism.
  Verdict: exact in the shared Ext encoding accepted by both cohomology
  dependency records. Their bridge to the K-injective/derived-global-sections
  model remains shared stage-3 work, not a new definition in this delivery.
- Identity compatibility: four `Nonempty` functor-isomorphism clauses cover
  inverse/direct images for sets and abelian groups. The equality using
  `(upperStarId ... X).hom.app F` says that the cohomology map is the identity
  after the canonical identity comparison, for each F, q, and x.
  Verdict: exact. I checked the identity comparison's orientation in Coherence.
- Composition compatibility: for X'' and a universal homeomorphism v, the
  four `Nonempty` clauses compare the functors of `v ≫ u` to the successive
  inverse/direct images in their correct orders. The cohomology equality
  uses `(upperStarComp ... v u).inv.app F` to map the iterated pullback to
  the composite pullback. I read its full signature and construction from
  conjugation of `lowerStarComp`. Verdict: exact; Lean's v ≫ u is u ∘ v.
- Pullback compatibility: g : Y ⟶ X is arbitrary. Lean's Y' is `pullback g u`,
  u' is `pullback.fst g u`, and g' is `pullback.snd g u`. The first four
  clauses assert universal homeomorphism, abelian unit/counit isomorphisms,
  and cohomology bijectivity for u'. The next four natural-isomorphism
  clauses state the square of inverse images and of their quasi-inverses,
  for sets and abelian groups. The final equality compares the two iterated
  cohomology maps in the same cohomology group using the inverses of the
  canonical `upperStarComp` comparisons. I checked that `pullback.condition`
  supplies `(u' ≫ g) = (g' ≫ u)` with the required orientation. Verdict:
  exact; no assumption that g is etale or a universal homeomorphism.

Edge cases: I = Empty is admitted, and its sieve covers precisely the empty
etale object. Arbitrarily infinite I and an independent index universe w are
admitted. Empty schemes, zero abelian sheaves, q = 0, identity morphisms,
nilpotent thickenings, and purely inseparable extensions are all included.
No characteristic restriction occurs. Schemes use arbitrary universe u, and
sets/abelian groups use u+1 exactly as the landed dependency declarations do;
no extra smallness instance is required from the caller. All additional
schemes in the composition and square clauses use the same scheme universe.

Independent searches with different wording from the worker:

- LeanFinder via msearch: `equivalence of sheaves along radicial integral
  surjective scheme maps commutes with change of base`. Eight hits, mainly
  structure-sheaf module pullback/pushforward comparisons. These are other
  categories and do not state this node.
- Loogle via msearch: `CategoryTheory.Functor.IsEquivalence`. Generic
  equivalence declarations, not this theorem.
- Mathlib grep via msearch: `radicial|topological.?invariance|cohomologyMap`.
  No hits.
- LeanSearch via msearch: `small etale topos equivalence for integral
  universally injective surjective morphism compatible with base change`.
  Service unavailable (Internal Server Error); not counted as a negative result.
- Independent rg throughout the upstream WeilConjectures and project Sheaf
  trees for `universalHomeomorphism_invariance`, universal-homeomorphism
  compatibility, and cohomologyMap composition/identity names found the
  upstream partial results, including TopologicalInvariance, Coherence,
  CohomologyMap and EdgeMap, and project citers. None states the whole
  conjunction with this cartesian-square cohomology equality. No duplicate
  notion or full-statement declaration was found.

There are no new definition nodes or dependency modules in this delivery and
no `statement_change`. No mismatch requiring repair was found. I left the Lean
and node unchanged and appended this independent review only. The imports
provide respectively the cohomology/adjunction constructions and set-valued
pullback. There is one named theorem with proof `sorry`, no definition or
embedded data hole. The module/declaration docstrings name the sources and
blueprint id, and the proof docstring follows all five node proof steps.
Every line is at most 92 characters. Direct extraction confirms that
`lean.statement` equals the file's signature verbatim. Independent scompile
completed cleanly on the server in 2.2 seconds, with no warnings or errors.
