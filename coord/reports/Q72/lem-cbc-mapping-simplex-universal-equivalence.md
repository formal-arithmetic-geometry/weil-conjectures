## Worker report

The module `Sheaf.CategoryTheory.MappingSimplexUniversalEquivalence` states
`SSet.Enhanced.mapping_simplex_universal_equivalence`, with one `sorry` and no
new definitions or auxiliary theorem statements. The node is unchanged outside
`lean`. There is no statement correction or statement dispute.

I read HTT Definition the project server and Proposition the project server(2), and the reduction and
proof in Propositions the project server and the project server, in the PDF named by the node. The
definition has exactly the three comparison hypotheses used here: over-base
commutation, preservation of marked edges as Cartesian edges, and equivalence
on each vertex fibre. Proposition the project server(2) concludes categorical equivalence
after every simplicial base change.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial sets and standard simplices | `SSet.{u}` and `(Δ[n] : SSet.{u})`, using the primitives imported by `EnhancedDiagramsCones`. |
| `n ≥ 0` | `n : ℕ`, including zero. |
| Small Cartesian fibration `p : Y → Δ[n]` | `Y : SSet.{u}`, `[Quasicategory Y]`, `p`, and `hp : @cartesianFibration ...`. |
| Quasicategory structure on the standard simplex, implicit in that notion | Explicitly supplied by `quasicategory_of_innerFibration` along `(stdSimplex.isoNerve n).hom`; an isomorphism is an inner fibration, and the nerve is a quasicategory. This supplies proof data, with no additional hypothesis. |
| Chain `A_0 ← ... ← A_n` | `A : SimplexChain.{u} n`, the recorded functor from the opposite finite ordinal. |
| Marked mapping simplex `M^m(A)` and simplicial comparison `q` | `mappingSimplex A` is its underlying simplicial set, `markedMappingSimplex A` supplies its marking, and `q : mappingSimplex A ⟶ Y`. |
| Comparison is over `Δ[n]` | `hq : q ≫ p = mappingSimplexProjection A`. |
| Every edge `(alpha,a)` with degenerate `a` maps to a `p`-Cartesian edge | `hcart` quantifies over all 1-simplices `e` in the existing `markedMappingSimplex A` marking and asserts `IsCartesianEdge p (SSet.yonedaEquiv.symm e ≫ q)`. The existing marking is exactly membership of `e.2` in the range of the fibre's `σ 0`. |
| Fibre equivalence for every `0 ≤ i ≤ n` | `hfib` quantifies over `i : Fin (n + 1)`. Its canonical map is `pullback.lift` of the unique map to `Δ[0]` and `mappingSimplexFiberInclusion A i ≫ q`, into `fiber p (stdSimplex.obj₀Equiv.symm i)`. The lift equation follows from `hq` and the recorded `mappingSimplexFiber_projection`. The point-first order of this fibre is the existing dependency's convention and is canonically the node's fibre. |
| Meaning of categorical equivalence in the fibre hypothesis | For each `C : SSet.{max u v}` with `C.Quasicategory`, restriction by the lifted fibre map gives an equivalence of ordinary homotopy categories, exactly the expression in `SSet.exists_joyal_model_structure`. |
| Every small `T` and every map `t` | Conclusion quantifies over arbitrary `T : SSet.{u}` and `t : T ⟶ Δ[n]`. |
| The induced underlying map `q_T` | `pullback.map (mappingSimplexProjection A) t p t q (𝟙 T) (𝟙 (Δ[n])) ...`, with coordinates `(q, id_T)` and base identity. This is the actual induced map, not an arbitrary chosen arrow. |
| `q_T` is a categorical equivalence | The same enlarged-universe ordinary-homotopy-category restriction test as in `hfib`, now applied to this `pullback.map`. |
| Neither `T` nor `A_i` must be quasicategories; `t` need not be injective | No such typeclasses or hypotheses occur. |
| Empty sets and `n = 0` | No nonemptiness or positive-dimension hypotheses occur. |

Dependency declarations reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: existing Mathlib `SSet`, standard
  simplices, simplicial maps, and degreewise categorical pullbacks.
- `Sheaf.CategoryTheory.InfinityFibrations`:
  `SSet.Enhanced.cartesianFibration`, `SSet.Enhanced.IsCartesianEdge`, and the
  fibre convention `SSet.Enhanced.fiber` (its explicit pullback appears in the
  signature).
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`, specifically its enlarged-universe weak
  equivalence characterization, used verbatim for both equivalence tests.
- `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`:
  `SSet.Enhanced.SimplexChain`, `mappingSimplex`, `mappingSimplexProjection`,
  `markedMappingSimplex`, `mappingSimplexFiberInclusion`, and
  `mappingSimplexFiber_projection`. Their full signatures and construction
  docstrings were read. The marked-map-only `mappingSimplexPresentationFiber`
  is not copied or replaced by another definition: its unmarked canonical
  pullback formula is written directly using Mathlib `pullback.lift`.
- `Mathlib.AlgebraicTopology.Quasicategory.Nerve`: the nerve quasicategory
  instance. Mathlib `stdSimplex.isoNerve`, `quasicategory_of_innerFibration`,
  and `innerFibrations.of_isIso` provide the base proof argument.

The theorem docstring records the node's seven proof steps, including the
composition-compatible mapping-space zigzag, Cartesian dualization, induction,
two full regions, mixed mapping square, arbitrary simplex pullback (including
repeated vertices), and simplexwise detection. All currently recorded proof
dependency modules are imported, with proof-only imports non-public. The two
proof-only nodes `lem-coef-mapping-simplex-final-edge` and
`lem-cbc-simplexwise-categorical-base-change` currently have no `lean` record,
so there is no module of theirs to import. Neither is needed to type this
statement; both remain named explicitly in its proof plan.

Edge cases checked before writing:

- `n = 0`: `Fin (n + 1)` has the one required fibre; the conclusion is the
  universal/product version of that fibre equivalence.
- Empty `T`: both pullbacks are empty and the induced map is their isomorphism.
- Empty chain fibres and empty `Y`: no vertex is chosen by the signature; the
  marking condition is vacuous when its edge set is empty, and the fibre
  equivalence hypothesis enforces precisely the remaining restrictions.
- Noninjective `t`, including degenerate simplices: there is no mono or
  injectivity hypothesis; `pullback.map` is defined for all such maps.
- Non-quasicategorical `A_i` and `T`: categorical equivalence uses tests into
  quasicategories, so the source and target of a tested map need not be fibrant.
- Universe size: all small inputs are in `u`; tests range in `max u v`, exactly
  as the recorded Joyal statement, with explicit universe binders `u v`.

Searches for an existing statement (all with no exact match):

| Tool | Query | Result |
| --- | --- | --- |
| `msearch.py leansearch` | `Base changes of a mapping simplex quasi-equivalence to a cartesian fibration are categorical equivalences` | Eight hits: generic model-category base-change stability, ordinary fibre-category results, and Kan-Quillen fibrations; none states this mapping-simplex comparison. |
| `msearch.py leanfinder` | `A quasi-equivalence from a mapping simplex to a cartesian fibration is a categorical equivalence after every simplicial base change` | Eight hits: ordinary fibre categories, homotopy-category/standard-simplex formulas, and nerve equivalences; no mapping-simplex universal comparison. |
| `msearch.py loogle` | `"SSet", "Equivalence"` | Nine hits: opposite equivalence, truncated homotopy categories and fundamental groupoids; none matches. |
| `msearch.py grep` in `AlgebraicTopology` | `mappingSimplex|mapping.simplex|categoricalEquivalence` | Zero hits. |
| `rg` in upstream `WeilConjectures` | `mappingSimplex|mapping.simplex|universal.*[Cc]ategorical` and the exact node id | No matches. |
| `rg` in `lean/Sheaf` | Exact node id, `mapping_simplex_universal`, and `mappingSimplex` | Only the recorded construction and marked-equivalence presentation in `CartesianMappingSimplexPresentation`; no universal underlying categorical-equivalence statement. |
| `rg` in `dag/lean_names_upstream.json` | Exact node id | No match. |

Validation: `scompile.py Q72 lem-cbc-mapping-simplex-universal-equivalence`
compiled this module cleanly as both sandbox and library module (1.4 s and
1.5 s respectively), with no warnings or errors. All variables and universes
are bound explicitly and `autoImplicit` is disabled. The required delivery dry
run checks the packet with maintainer preflight and requests no push.


## Second reading by Q72

I independently read the item node, its four statement-dependency node records,
the dependency declarations, and HTT Section 3.2.2 in the sandbox PDF/text
(printed pp. 179--184). This source is HTT, not Stacks: Definition the project server
lists the three quasi-equivalence conditions and Proposition the project server(2)
states precisely the universal underlying categorical equivalence. There is
no standing fibrancy assumption on the chain or on the base-change source.
The source's mapping-simplex construction and marking occur on printed p. 179.

My object/hypothesis/conclusion checklist, recorded against the Lean:

| Node item | Exact Lean rendering and verdict |
| --- | --- |
| Small simplicial sets, standard simplex, degreewise pullbacks | `SSet.{u}`, `(Δ[n] : SSet.{u})`, Mathlib `pullback`; correct existing primitives from `EnhancedDiagramsCones`, not new copies. |
| Nonnegative integer n | `(n : ℕ)`; correct, includes zero. |
| Cartesian fibration p with small total space Y | `(Y : SSet.{u}) [Quasicategory Y]`, `(p : Y ⟶ Δ[n])`, `hp : @cartesianFibration ...`; correct. The dependency defines precisely inner lifting and Cartesian lifts with prescribed target. The total-space quasicategory follows mathematically from inner lifting over the simplex, so this binder excludes no Cartesian fibration. |
| Quasicategory structure on the base | The explicit proof in `hp` transports the nerve instance through `(stdSimplex.isoNerve n).hom` using `quasicategory_of_innerFibration` and `innerFibrations.of_isIso`; correct, constructed without an extra hypothesis, including universe zero. |
| Chain A_0 ← ... ← A_n | `(A : SimplexChain.{u} n)`; correct. I opened the abbreviation `(Fin (n + 1))ᵒᵖ ⥤ SSet.{u}`: its variance gives the required backward transition maps. |
| Marked mapping simplex and comparison q | `(q : mappingSimplex A ⟶ Y)` and `markedMappingSimplex A`; correct. I read `MappingSimplexDegree`, `mappingSimplexOperator`, `mappingSimplexProjection`, and the marking construction. Their dependent-pair simplices and transition operators are exactly the source's construction. The node explicitly asks for a simplicial map with an edge condition, not an unrelated arbitrary marked target. |
| q is over the standard simplex | `hq : q ≫ p = mappingSimplexProjection A`; correct, source condition (1). |
| Every edge with degenerate fibre coordinate has Cartesian image | `hcart` quantifies over each one-simplex in `(markedMappingSimplex A).marking` and uses `IsCartesianEdge p (SSet.yonedaEquiv.symm e ≫ q)`; correct, source condition (2). The marking is exactly `e.2 ∈ Set.range (...σ 0)`, not merely degeneracy of the whole pair. `IsCartesianEdge` has the final-outer-horn definition from the dependency. |
| Categorical equivalence on every vertex fibre | `hfib` quantifies over all `i : Fin (n + 1)`. Its `pullback.lift` pairs the unique map to `Δ[0]` with `mappingSimplexFiberInclusion A i ≫ q`; correct canonical map, source condition (3). I checked the constant vertex map and `mappingSimplexFiber_projection` used by its commutativity proof. The point-first pullback is definitionally the dependency's `fiber`, canonically isomorphic to the node's opposite factor order. |
| Meaning of categorical equivalence | In both `hfib` and the conclusion the expression with `hoFunctor.map`, `MonoidalClosed.pre`, and `uliftFunctor.{v, u}` is verbatim the test from `exists_joyal_model_structure`; correct ordinary homotopy-category restriction test against every quasicategory in `max u v`. I read that theorem's weak-equivalence clause, not just its name. |
| Every small T and every simplicial t | `∀ (T : SSet.{u}) (t : T ⟶ Δ[n])`; correct quantifier order after all comparison hypotheses. No fibrancy, monomorphism, or injectivity assumption occurs. |
| The induced underlying map after base change | `pullback.map (mappingSimplexProjection A) t p t q (𝟙 T) (𝟙 (Δ[n])) ...`; correct map with coordinates q and identity on T, between exactly the two stated pullbacks. |
| Categorical equivalence of that induced map | The conclusion applies the same full homotopy-category restriction test to this actual `pullback.map`; correct, with no weakened marked-equivalence substitute. |

Edge cases: at `n = 0` there is exactly one fibre hypothesis and the conclusion
still covers all T over the point. No empty index chain is intended since its
indices are 0 through n. Empty T gives two empty pullbacks. Empty Y and empty
chain fibres are allowed: the signature chooses no vertex, and the fibre tests
retain their actual force. Arbitrary non-quasicategorical A_i and T are allowed;
repeated vertices and degenerate/noninjective t are allowed. There are no
coefficient rings, characteristics, schemes or additive zero objects in this
statement. The input universe u is arbitrary, and v permits every enlargement
of tests via `max u v`; no smaller test universe or universe equality is imposed.
I checked that `u v`, n, Y, p, A, q, i, T, t and C are all bound.

Independent searches, using different wording from the author's:

- `msearch.py leanfinder`: `Cartesian fibration over a simplex: a fibrewise
  equivalence preserving Cartesian transport remains an equivalence under
  pullback`. Eight hits concern ordinary fibre categories, Cech nerves, or
  Galois fibre functors; none is the asserted simplicial comparison.
- `msearch.py loogle`: `"SSet", "pullback", "IsEquivalence"`. Zero hits.
- `msearch.py leansearch`: `A fibrewise categorical equivalence from the
  simplicial replacement of a finite chain into a Cartesian fibration is a
  universal categorical equivalence`. Eight hits give ordinary fibre-category
  equivalences and general simplicial/model-category constructions, no match.
- `rg -i` for `quasi.?equivalence`, `universal.{0,40}categorical`,
  `mapping.?simplex`, and `simplex.{0,30}base.?change` in upstream
  `WeilConjectures`, Mathlib algebraic topology, and the project's category
  theory/algebraic topology modules finds the existing construction module and
  different marked-descent, straightening and relative-exponential statements.
  I opened `marked_mapping_simplex_descent`: it concerns marked weak
  equivalences and functor categories, not this universal underlying map.
  Searching the exact item id and declaration in upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` finds no existing theorem to reuse.

No mathematical mismatch was found. I changed only this report, retaining the
correct Lean and node record. There are no new nodes, dependency modules,
statement corrections, or citer verdicts to audit. In particular the marked-only
`mappingSimplexPresentationFiber` requires a different bundled input; using the
canonical unbundled Mathlib pullback lift does not introduce another definition.
The module contains one theorem with `sorry`, no definitions or proved helper
theorems. The commuting-square proofs inside the canonical map's type are
necessary proof arguments, not additional theorem statements. Both source and
blueprint docstrings are present; the theorem's seven-step proof plan matches
all seven node proof steps. All currently recorded proof-dependency modules are
imported; the final-edge and simplexwise-base-change nodes have no module record.
The node differs from the shared base only in `lean`. Its `lean.statement` is
byte-for-byte equal to the source signature before `:= by`, and every Lean line
has at most 100 characters. Validation results follow below.

Second-reader validation: `scompile.py Q72 lem-cbc-mapping-simplex-universal-equivalence lean/Sheaf/CategoryTheory/MappingSimplexUniversalEquivalence.lean` passed in sandbox mode (1.3 s) and library mode (1.4 s), with no errors or warnings. The prescribed delivery wrapper performs server preflight before push.
