## Worker report

The module `Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem` states
`RingHom.exists_limit_module_essentially_finite_presentation_over_system` with one `sorry`.
It defines no new notion. The concrete localization presentation is supplied as data, using
Mathlib's existing `Algebra.FinitePresentation` and `IsLocalization`, as in the landed module
`Sheaf.RingTheory.EssentiallyFinitePresentationOverIntermediate`; no private predicate for
essential finite presentation is introduced. No node statement or dependency list changed.

Source read: Stacks Tags [00QV](https://stacks.math.columbia.edu/tag/00QV) and
[00QX](https://stacks.math.columbia.edu/tag/00QX). The repository's cited `algebra.tex` is not
present on this machine. Tag 00QV constructs polynomial quotients localized at inverse-image
primes over a given base system; Tag 00QX descends a finite presentation matrix over that
construction. The node spells out the verifications left to the reader. Its six proof steps
and dependency identifiers are in the theorem docstring.

Hypotheses, individually:

- The nonempty directed set is `{I : Type w} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Preorders match the project's directed-set convention.
- The given local rings and their ring homomorphisms are `F : I ⥤ CommRingCat.{u}` and
  `[∀ i, IsLocalRing (F.obj i)]`. `F.map (homOfLE h)` is the transition. Functor laws give
  the identity and composition laws; uniqueness of preorder arrows supplies the stated
  compatibility independent of proofs of inequalities.
- Every transition is local by `hF`; the local colimit ring is `c.pt` with
  `[IsLocalRing c.pt]`, its maps are `(c.ι.app i).hom`, local by `hcLocal`.
  Cocone naturality is the equation with these transitions. `hc : IsColimit c` is the
  colimit universal property in commutative rings, rather than a chosen isomorphic carrier.
- The target local ring is `T : CommRingCat.{u}` with `[IsLocalRing T]`, and its local
  base homomorphism is `τ : c.pt →+* T` with `[IsLocalHom τ]`.
- Essential finite presentation is given by `P : Type p`, `[CommRing P]`,
  `[Algebra c.pt P]`, `[Algebra.FinitePresentation c.pt P]`, `W : Submonoid P`, and
  `f : P →+* T` with `hf : f.comp (algebraMap c.pt P) = τ` and
  `hT : letI := f.toAlgebra; IsLocalization W T`. This says that the given `T`, with its
  original base map, is the localization of this finitely presented algebra. Supplying
  witnesses for the existential presentation does not add an assumption.
- The module is `N : AddCommGrpCat.{max u v}` with `[Module T N]`.
  Its finite presentation is the supplied `s t : ℕ`,
  `H : (Fin s → T) →ₗ[T] (Fin t → T)` and
  `hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N)`.
  A quotient by the image is the cokernel. A finite function module is the finite direct
  sum in the source. The same supplied ranks `s,t` appear at every output stage.

Output data and each conclusion:

- `∃ i₀ : I` and the subtype `{i : I // i₀ ≤ i}` give the tail. It contains `i₀` and is
  directed by the inherited preorder and directedness of `I`.
- `B` is the ring functor on the tail, with stage local-ring predicates and local transition
  predicates. `τ₀ i : F.obj i.1 →+* B.obj i` gives the local stage base maps.
  The equality involving `B.map`, `τ₀`, and `F.map` is precisely their base compatibility.
- `β : B ⟶ (Functor.const _).obj T` is the cocone to the actual ring `T`.
  `κ i` agrees pointwise with `(β.app i).hom` and is local. Naturality therefore gives
  `κ j ∘ t_ji = κ i`. The equation `(κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom`
  is compatibility with the limit base map.
- `D` is the abelian-group functor on the same tail. Its maps are the additive maps `n_ji`.
  The quantified family of `Module (B.obj i) (D.obj i)` gives the stage module structures.
  The explicit smul equation with `D.map` and `B.map` is semilinearity of `n_ji`.
  Both functors give identity and composition laws automatically.
- `δ : D ⟶ (Functor.const _).obj N` is the cocone to the actual group `N`.
  The additive maps `ν i` agree with its components, so their composition compatibility
  follows from naturality. Their displayed smul equation is semilinearity over `κ i`.
- Clause (1): `Nonempty (IsColimit (Cocone.mk T β))` and
  `Nonempty (IsColimit (Cocone.mk N δ))` give exactly the ring and abelian-group colimits.
  `Nonempty` expresses existence of the universal-property data inside a proposition.
- Clause (2): `∀ i, (τ₀ i).EssFiniteType` is essential finite type over the correct base.
- Clause (3): for each `i` there is `H₀` with domain `Fin s → B.obj i` and codomain
  `Fin t → B.obj i`, and a linear equivalence between its image quotient and `D.obj i`.
  `∀ i, Module.Finite (B.obj i) (D.obj i)` states the ensuing finite generation explicitly.
- Clause (4), rings: algebras on `B.obj i` and `F.obj j.1` come respectively from `τ₀ i`
  and the specified base transition. The ring map `φ` out of their tensor product is
  required to send `x ⊗ y` to `t_ji(x) τ₀ j(y)`. Pure tensors generate the tensor product,
  so this specifies the canonical map, not an arbitrary map or abstract isomorphism.
  Under `φ.toAlgebra`, `∃ U, IsLocalization U (B.obj j)` is localization at a multiplicative
  subset, exactly the node's three elementwise localization conditions.
- Clause (4), modules: the algebra on `B.obj j` comes from the specified ring transition.
  The linear equivalence `e` from `B.obj j ⊗[B.obj i] D.obj i` sends `y ⊗ x` to
  `y • n_ji(x)`. This is the node's canonical map with tensor factors exchanged, via the
  canonical symmetry over a commutative ring. It is a module equivalence over `B.obj j`.
- Clause (5), rings: algebras use `τ₀ i` and the original colimit leg. The tensor ring map
  sends `x ⊗ y` to `κ i(x) τ(y)`; its induced algebra structure makes `T` an
  `IsLocalization` at some submonoid of this tensor ring.
- Clause (5), modules: the algebra on `T` is induced by `κ i`. The `T`-linear equivalence
  sends `y ⊗ x` to `y • ν i(x)`, again the canonical map after tensor symmetry.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`, recorded
  `CategoryTheory.Limits.colimit`, with `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit` explicitly recorded as associated declarations.
  This statement needs a colimit at a given carrier and uses the latter two declarations,
  with their full definitions read in `Limits.Cones` and `Limits.IsLimit`.
- `def-weil-pbc-finitely-presented-algebra`: the Mathlib leaf names
  `Algebra.FinitePresentation`, `Mathlib.RingTheory.FinitePresentation`, used directly.
- `def-weil-pbc-essentially-finite-type-algebra`: the Mathlib leaf names
  `Algebra.EssFiniteType` and its ring-map form `RingHom.EssFiniteType`,
  `Mathlib.RingTheory.EssentialFiniteness`, used with the specified structure homomorphism.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, used directly (available through the finiteness imports).

Edge cases checked before writing: an empty index set is excluded by the source's explicit
nonemptiness; a singleton or constant system is allowed; no antisymmetry is imposed. Local
rings are nonzero in the usual Stacks sense, matching `IsLocalRing`. The zero module is
allowed, including `s=t=0`; either presentation rank may separately be zero. There is no
Noetherian, characteristic, finite base-ring or injectivity hypothesis. `W` is an arbitrary
submonoid, not assumed finitely generated, and the conclusions do not demand finite
presentation of the stage rings, only essential finite type. The indexing universe (reviewer fix: now `u`, see below) and
presentation algebra universe `p` are independent. Rings use one arbitrary universe `u`
as for Mathlib ring diagrams; module carriers use `max u v`, so finite free stage cokernels
fit even when a module universe would otherwise be smaller than that of the scalar ring.
All variables and universes are explicit; no auto-bound implicit is used.

Searches for a duplicate statement and declaration:

- `msearch.py ... leanfinder "Descend a local algebra essentially of finite presentation
  and a finitely presented module along a directed colimit of local rings"`: eight hits,
  including `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` and
  `exists_comp_map_eq_of_isColimit`, and preservation of finite presentation under
  localization. They factor maps or localize algebras, not descend the algebra/module system.
- `msearch.py ... loogle 'Module.FinitePresentation, Algebra.EssFiniteType'`: only
  `Algebra.FormallySmooth.instFinitePresentationKaehlerDifferentialOfEssFiniteType`;
  unrelated to descent.
- `msearch.py ... grep 'EssFinitePresentation|essentially of finite presentation'`: six
  hits, chiefly `RingTheory.Smooth.Fiber`, explicitly noting the absence of a class and
  taking a finitely presented algebra plus localization witnesses instead.
- `msearch.py ... leansearch 'A finitely presented module over a local algebra essentially
  of finite presentation descends along a directed colimit of local rings'`: unavailable,
  Internal Server Error. No conclusion is drawn from this unavailable search.
- `rg -n 'limit.module.essentially|EssFinitePresentation|essentially of finite presentation'`
  over `WeilConjectures` and `lean/Sheaf`: no declaration of this descent statement.
  The later broader search found `EssentiallyFinitePresentationOverIntermediate`, which
  concerns changing the base through an intermediate algebra, not descent to stages.
- `grep -rn '<item id>'` over `WeilConjectures`: no hits.
- `rg -n 'exists_limit_module_essentially_finite_presentation_over_system'` over
  `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures` and `lean/Sheaf`: no collision.

Validation: server `scompile.py` succeeds with no errors or warnings. The only proof is the
stage-2 `sorry`. No disputed statement, dependency fault or statement correction was found.

## Second reading by G1

I opened the node statement, its Stacks source (Algebra, Tags 00QV and 00QX), and the complete
Lean declaration. The correspondence is as follows.

- The nonempty directed index set $(\Lambda,\le)$ is rendered by `{I : Type w}` with
  `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`; no antisymmetry is added.
- The local-ring system $(A_\lambda)$ and transition maps are `F : I ⥤ CommRingCat.{u}`,
  `[∀ i, IsLocalRing (F.obj i)]`, and `hF` for every `F.map (homOfLE h)`; functor laws
  render identity and composition.
- The local colimit $(A,\pi_\lambda)$ is `c : Cocone F`, `hc : IsColimit c`,
  `[IsLocalRing c.pt]`, and `hcLocal`; the legs are `(c.ι.app i).hom`.
- The local target and map are `T : CommRingCat.{u}`, `[IsLocalRing T]`, `τ : c.pt →+* T`,
  `[IsLocalHom τ]`.
- Essential finite presentation is rendered by `P`, `[Algebra c.pt P]`,
  `[Algebra.FinitePresentation c.pt P]`, `W`, `f`, `hf`, and `hT`; `hf` preserves the
  specified map from the original colimit ring and `hT` makes the actual `T` the stated
  localization.
- The finitely presented module is `N : AddCommGrpCat.{max u v}`, `[Module T N]`, ranks
  `s,t`, presentation map `H`, and `hN` identifying its cokernel with `N`; zero ranks and
  the zero module are included.
- The existential tail and its ring system are `i₀`, `B`, `β`, and `κ`. The displayed
  equalities identify `κ` with the cocone legs; the local-ring and local-map predicates,
  transition locality, and the colimit clause match the node.
- The base maps `τ₀` have locality, essential finite type, compatibility with `τ` and the
  original legs, and transition naturality exactly as in the node.
- The module system is `D`, `δ`, `ν`, and the family of `Module (B.obj i)` instances.
  The two semilinearity equations, additive colimit, finite generation, and the cokernel
  presentation with the same `s,t` are all present.
- Clause (4) has the ring tensor map on pure tensors and a localization witness, followed
  by the canonical module tensor linear equivalence and its pure-tensor formula.
- Clause (5) has the corresponding tensor map to `T`, localization witness, and module
  base-change equivalence. The `letI` algebra structures are induced by the displayed maps,
  so the tensor products and localization predicates use precisely the node's maps.

I found no mismatch and made no statement or dependency change. In particular, the Lean
formulation uses `Nonempty (IsColimit ...)` for the two colimit assertions, which is the
propositional existence form of the node's colimit clauses. The subtype tail is nonempty
because it contains `i₀`, and inherits directedness. Empty systems are excluded exactly by
`[Nonempty I]`; singleton and constant systems are allowed. The zero module and `s = 0` or
`t = 0` are allowed. No Noetherian, characteristic, finite-base, or injectivity assumptions
appear, and the universes `u,v,p,w` do not exclude the node's cases.

I repeated the duplicate searches with `msearch.py` (LeanFinder, Loogle, and LeanSearch
queries for descent of finite presentations/modules), `rg` in `WeilConjectures`, `Mathlib`,
and `lean/Sheaf`, and the upstream-name index. They found only factorization/localization
lemmas and the unrelated intermediate-base module; no declaration of this statement or of a
single essentially-finite-presentation predicate exists. The dependency declarations recorded
by the node (`colimit`/`Cocone`/`IsColimit`, `Algebra.FinitePresentation`,
`Algebra.EssFiniteType`, and `Module.Finite`) are the ones used by the file; no private copies
or dependency modules are needed. The file compiles cleanly with `scompile.py`; its only proof
is the required `sorry`.

## Reviewer fix (R-lme1114, stage 2)

The index type was `{I : Type w}` with `w` independent of the ring universe `u`. For `w` above
`u`, `hc : IsColimit c` in `CommRingCat.{u}` is weaker than the node's "colimit in the category
of commutative rings": the set-theoretic colimit of a large system can be large while a small
local ring is still its colimit among `u`-small rings (e.g. index the small subsets of a large
field `L`, stages `k + m_S` for valuation rings with value group ℚ; the only small nonzero quotient
of the union `k + m` is `k`, so `k` is the colimit in `CommRingCat.{u}` with local legs, yet `t`
dies in `k` at no stage). The elementwise description used in proof steps 2 and 6 then fails, and
the statement is stronger than the node. Fixed to `{I : Type u}` (the objects' universe, as the
sibling `LocalRingColimitEssentiallyFiniteType` produces its system and as M1 d2371fc68 reads
limits); `universe w` removed. Nothing else changed.
