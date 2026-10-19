## Worker report

Record the existing declaration
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel`
in `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`.
No module is written, no proof is changed, and no definition or theorem is duplicated.
The declaration docstring explicitly identifies this blueprint node and Stacks Tag 0F03.
Read its full signature, docstring and proof in the read-only upstream checkout and
verified the same source using `scompile.py --source` on the current published server.
The recorded signature is verbatim from `theorem` to before `:=`, including line breaks.

Hypotheses and objects, matched individually:

- The schemes `X, S` and morphism `f` are upstream section variables `X, S, p`.
- The coefficient domain `n ≥ 1`, invertible on `S`, is specialized by setting
  `Λ := ULift.{u + 1} (ZMod n)`. These are exactly the coefficients used by the
  recorded dependency, not an arbitrary extra coefficient hypothesis. The upstream
  theorem works for every commutative coefficient ring, so its existing declaration
  covers this whole domain without requiring positivity or invertibility for its proof.
- `q ≥ 1` is `{q : ℤ} (hq : 1 ≤ q)`. Every positive integer is covered, and there
  are no negative-degree instances satisfying `hq`.
- The universal, single-degree hypothesis is
  `huniv : Etale.UniversalBaseChangeProperty Λ p (q - 1)`. There is no cumulative
  hypothesis and no assumption in smaller degrees.
- `S' → S`, the base change `X' → S'`, and its projection to `X` are `a, p', b`,
  with `hp : IsPullback b p' p a`. Any chosen fibre product has this property;
  any square with this property is canonically isomorphic to the fibre product.
- `g : T ⟶ S'` has precisely `[QuasiCompact g] [QuasiSeparated g]`.
  No hypothesis is imposed on `a` or on its composite with `g`.
- The projections `e, h` from `Y` are recorded by `sq : IsPullback e h g p'`.
- Abelian sheaves annihilated by `n` are exactly sheaves of modules over `ZMod n`,
  and the lift of this ring changes only its universe. The coefficient category is
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, as in the recorded BC predicate.

Conclusions, matched individually:

1. The first conjunct is `∀ F, Mono (Etale.baseChangeHomologyMap Λ sq q F)`.
   The source and target functors are the existing homology presentations of
   `p'⁻¹ R^q g_* F` and `R^q h_* e⁻¹ F`. A monomorphism in these sheaf categories
   is exactly an injective sheaf morphism.
2. The second conjunct quantifies over `F, G, α : F ⟶ G` and `[Mono α]`, and asserts
   `Mono (cokernel.map ...)`. The map is induced by the source and target functors
   applied to the same `α`, with `baseChangeHomologyMap_naturality` as its square.
   This is the specified canonical cokernel inclusion, not an existential embedding.
3. The third conjunct adds `[Injective G]` in the category of coefficient-module
   sheaves, and asserts `Mono (cokernel.desc ...)` into the target functor at `G`.
   The defining map is the target functor applied to `α`; the vanishing witness is
   the existing `baseChangeHomologyMap_comp_map_eq_zero_of_injective`.
   No injectivity of the underlying abelian sheaf is assumed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty`:
  `AlgebraicGeometry.Etale.CumulativeUniversalBaseChangeProperty`, the recorded
  declaration for `sbc-def-base-change-property`. Its docstring specifies that
  fixed-degree BC and universal fixed-degree BC reuse the following upstream predicates
  with `ULift (ZMod n)`; the cumulative predicate itself is not the hypothesis here.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`:
  `AlgebraicGeometry.Etale.BaseChangeProperty`,
  `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`,
  `AlgebraicGeometry.Etale.baseChangeHomologyMap`,
  `AlgebraicGeometry.Etale.baseChangeSourceFunctor`,
  `AlgebraicGeometry.Etale.baseChangeTargetFunctor`, and
  `AlgebraicGeometry.Etale.baseChangeHomologyMap_naturality`.
  Their full signatures and docstrings were read. These are the same notions used by
  the dependency record and by the existing theorem; there is no dependency repair.

Edge cases: `q = 1` needs only universal degree-zero BC, as required. `q = 0` is
excluded by the source and by `hq`. For `n = 1`, all coefficient-module sheaves are
zero, and the three monomorphism assertions hold. The empty scheme, zero sheaves,
identity base change, identity inclusion, and the zero subsheaf are all allowed.
The source of the module-injective acyclicity is the coefficient-module category,
not the category of abelian sheaves. Schemes have universe `u` and module values
universe `u + 1`, exactly as in the recorded dependency. There is no restriction
on the morphism `S' → S` or any characteristic beyond the coefficient domain.

Searches made:

- `msearch.py leansearch`: “Universal base change in degree q minus one implies
  injectivity of the base change morphism and monotonicity of its cokernel”:
  service unavailable, Internal Server Error.
- `msearch.py leanfinder`: “Injectivity of the etale cohomology base change map and its
  induced cokernel maps under universal base change in the preceding degree”:
  eight unrelated cotangent-complex hits, none matching.
- `msearch.py loogle`: `mono_baseChangeHomologyMap, baseChange_injectivity`:
  zero hits, unknown identifier `mono_baseChangeHomologyMap`.
- `msearch.py grep`: `baseChangeHomologyMap|mono_cokernelMap|mono_cokernelDesc`
  under Mathlib/AlgebraicGeometry: zero hits.
- `rg` in upstream `WeilConjectures` for this node id and for
  `baseChange.*[Ii]nject|[Ii]nject.*baseChange`: found `Injectivity/CriticalMap.lean`,
  including its aggregate theorem explicitly tagged with the node id.
- `rg` in `lean/Sheaf` for the node id and aggregate declaration name: zero hits.

Source checked: the complete blueprint node
`sec-smooth-base-change/sk-prop-injectivity/sbc-lem-bc-injectivity.md`, including its
proof. The upstream theorem follows precisely the injective embedding, long-exact
comparison and common-injective cokernel argument described there.
No statement correction, new nodes, dependency modules or disputed statement.

Validation: the delivery dry run checks the existing declaration on the server
by importing its module and running `#check @` on its full name. No delivered Lean
module needs compilation. The independent second reading is left to the next worker.

## Second reading by NU

I independently opened the sandbox node, the complete blueprint source and proof,
Stacks `etale-cohomology.tex`, labels `remark-base-change-holds` (0F02) and
`lemma-base-change-q-injective` (0F03), and the upstream aggregate theorem with its
section variables, three component theorems, and their proofs. I also retrieved
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap` with
`scompile.py --source`; its signature and surrounding source agree with the local
upstream file. A literal extraction from `theorem` to before `:=` agrees with the
sandbox's `lean.statement` including newlines.

My object/hypothesis/conclusion checklist, with verdicts:

1. Arbitrary schemes `X,S` and `f : X → S`: section variables
   `{X S : Scheme.{u}} {p : X ⟶ S}`. Verdict: same schemes and morphism;
   no finite type, Noetherian, separated, smooth, or field hypothesis.
2. Integer `n ≥ 1` invertible on `S`, with coefficients `Z/nZ`: instantiate
   `Λ : Type (u + 1)` and `[CommRing Λ]` by `ULift.{u + 1} (ZMod n)`.
   Verdict: exactly the coefficient specialization already prescribed by the
   dependency's Lean record and module. The general existing theorem does not need
   positivity or invertibility; using it on this prescribed domain adds no
   hypothesis to the node and loses no case. It does not assert that the node has
   been changed to arbitrary coefficients.
3. Degree `q ≥ 1`: `{q : ℤ} (hq : 1 ≤ q)`. Verdict: exactly positive integral
   degrees, including `q = 1`, with the natural/integer degree identification.
4. Universal BC in the single degree `q-1`:
   `huniv : Etale.UniversalBaseChangeProperty Λ p (q - 1)`.
   Verdict: exact. I opened `sbc-def-base-change-property` and its recorded module
   `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty`, as well as
   `Etale.BaseChangeProperty` and `Etale.UniversalBaseChangeProperty` in upstream
   `SmoothBaseChange.Defs`. The dependency explicitly reuses these fixed-degree
   predicates. The cumulative predicate is not substituted here. Stacks 0F02
   uses cumulative universal BC, while this blueprint explicitly extracts the
   single-degree hypothesis; the two left vertical maps in the source proof
   need precisely this degree. No hidden throughout-section assumptions occur.
5. Arbitrary `S' → S` and its base change `f'`: `{a : S' ⟶ S}`,
   `{b : X' ⟶ X}`, `{p' : X' ⟶ S'}`, `(hp : IsPullback b p' p a)`.
   Verdict: the correct pullback square, with the correct orientation. Specifying
   any pullback square is equivalent to using the displayed fibre product;
   there is no restriction on `a` or on `a` composed with `g`.
6. A qcqs `g : T → S'` and the projections `e,h` of `Y`:
   `{g : T ⟶ S'}`, `[QuasiCompact g] [QuasiSeparated g]`,
   section variable `{e : Y ⟶ T}`, `{h : Y ⟶ X'}` and
   `(sq : IsPullback e h g p')`. Verdict: exact; no extra square or morphism property.
7. Every abelian sheaf `F` killed by `n`, and injectivity of its critical map:
   the first conjunct quantifies over
   `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and asserts
   `Mono (Etale.baseChangeHomologyMap Λ sq q F)`. Verdict: exact under the
   canonical equivalence of `n`-annihilated abelian sheaves with `ZMod n`-module
   sheaves and the coefficient universe lift. I read the actual constructions
   `baseChangeSourceFunctor`, `baseChangeTargetFunctor`,
   `baseChangeHomologyNatTrans` and `baseChangeHomologyMap`: their objects are
   homology of `p'⁻¹ Rg_* F[0]` and `Rh_* e⁻¹ F[0]`, and the arrow is homology
   of the canonical derived exchange, not an independently chosen map.
8. For each inclusion `F ⊆ G` with `G` also killed by `n`, injectivity on
   cokernels: the second conjunct quantifies over the same module-sheaf category
   and `(α : F ⟶ G) [Mono α]`, then asserts `Mono (cokernel.map ...)`.
   Verdict: exact. Its two legs are the source and target functors applied to
   this same `α`, and its commuting square is `baseChangeHomologyMap_naturality`.
   This is the canonical induced map, not an arbitrary embedding. A categorical
   mono describes an inclusion up to the usual identification with its image.
9. If that `G` is injective as a module sheaf, the cokernel for `F` embeds in
   `R^q h_* e⁻¹ G`: the third conjunct adds `[Injective G]` to the same
   `(α : F ⟶ G) [Mono α]` and asserts `Mono (cokernel.desc ...)`.
   Verdict: exact. The descending map is the target functor applied to `α`;
   its vanishing witness is the named
   `baseChangeHomologyMap_comp_map_eq_zero_of_injective`. I read its signature
   and proof in `Injectivity.LongExactSequence`: it needs only module-injectivity
   of `G` and `q ≠ 0`, the latter supplied by `hq`. It does not assume that
   `G` is injective after forgetting coefficients. Splitting the three universal
   clauses into a conjunction preserves their quantifier scope and dependence.

Edge cases: `q = 1` uses degree zero only; `q = 0` is intentionally excluded.
`n = 1` permits the zero coefficient ring and zero sheaves; no nontrivial-ring
instance occurs. `n = 0` is outside the node's prescribed coefficient domain,
although the general upstream theorem also allows integral coefficients.
The empty scheme, zero sheaf, zero subsheaf, identity inclusion, identity base
change and arbitrary characteristic satisfying the node's invertibility condition
are all admitted. There is no index family requiring nonemptiness. The universe
`u` is arbitrary and matches the scheme convention and the dependency's
`ModuleCat.{u+1}` values; `ULift` accommodates `ZMod n` at that universe.
Every apparently implicit object in the recorded signature is accounted for by
its explicit section variables; the server probe elaborates the full declaration.

Independent searches with different wording:

- `msearch.py leanfinder`: "monomorphism between cokernels of cohomological
  exchange maps for a subsheaf": eight hits about Mayer--Vietoris, ordinary
  sheaf monomorphisms and complex factorizations; none is the present theorem.
- `msearch.py leansearch`: "cokernel of an etale higher direct image exchange
  map injects into that of a larger torsion sheaf": service unavailable,
  Internal Server Error; no negative mathematical conclusion drawn.
- `rg` for `mono_cokernel|critical.map|q-injective` in upstream
  `WeilConjectures/SixFunctors/Etale/SmoothBaseChange`, project `lean/Sheaf`,
  and Mathlib `AlgebraicGeometry`: the upstream component and aggregate
  declarations are the relevant existing results. Project hits concern general
  abelian-category cokernel lemmas, not this statement; no matching Mathlib hit.
  Opened the aggregate rather than inferring a match from its name.

No mismatch found and no Lean or node change made. No new definition nodes,
dependency modules, statement correction, hollow data, private replacement,
or new theorem proof is introduced. The existing upstream proof follows the
node's three proof steps: embed in an injective module sheaf and use acyclicity;
compare the long exact rows using the two degree-`q-1` isomorphisms; then obtain
clause (3) for the specified injective and clause (2) by embedding both sheaves
in one injective and factoring the canonical cokernel maps. Source and blueprint
identifications and the proof explanation are present in the existing module.
H6 requires no new proofs here; reuse is H4's required outcome.

Validation: delivery uses the existing-declaration server probe through
`scompile.py` (the imported theorem is checked at its full name), and server
preflight through `deliver2.py --no-push`. There are no delivered Lean files to
compile separately. Only this independent review section was appended.
