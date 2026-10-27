## Worker report

The module `Sheaf.Topology.CompleteMetricGroupQuotients` states
`CompleteMetricGroupQuotients.reconstruction` with `sorry`. Its three fully constructed
helpers define precisely the objects displayed in the item's statement:
`transition`, `compatibleSubgroup`, and `continuousCompatibleSubgroup`. They are helpers
of this node's own notion, recorded in `lean.declarations`, not independent new notions.
No definition contains postponed data or a postponed proof. No statement correction,
new node, dependency repair, or STATEMENT-DISPUTED issue was needed.

Read the whole item, including its nine-step retained proof, and the complete statement
and Lean record of its sole dependency `def-kun-subspace-topology`. Read the recorded
Mathlib declaration `instTopologicalSpaceSubtype` in `Mathlib.Topology.Defs.Induced`:
it is exactly `TopologicalSpace.induced Subtype.val`, and is used for the subgroup H.
This module is imported publicly. There are no other statement or proof dependencies.

Source: read Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.2(1) and its
proof on printed p. 59 from the local PDF, as well as the retained general reconstruction
argument in `coord/reports/Q120/lem-sfb-complete-norm-open-test.md`. The paper states the
finite-extension application for profinite S; the item explicitly records its more general
agent-formulated metric-group lemma. The delivered theorem keeps that full generality.

Clause-by-clause rendering:

- An abelian group G is `{G : Type u} [AddCommGroup G]`, in arbitrary explicit universe u.
- A metric and its metric topology are `[MetricSpace G]`. Completeness is
  `[CompleteSpace G]`. For metric spaces this is equivalent to convergence of every
  Cauchy sequence (`Metric.complete_of_cauchySeq_tendsto`, in the imported Cauchy module),
  so it does not strengthen the node's sequential completeness assumption.
- Translation invariance is exactly
  `htranslation : ∀ x y z : G, dist (x + z) (y + z) = dist x y`.
- Addition and negation continuous are `[IsTopologicalAddGroup G]`.
- The open additive subgroups are `U : ℕ → OpenAddSubgroup G`. This packages exactly
  an additive subgroup and openness, with no extra subgroup hypothesis. The index n
  denotes the node's index n+1, a bijective reindexing of all its positive indices.
- Nesting is `hU : ∀ n, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup`.
- Shrinking is `hshrink : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x : G,
  x ∈ U N → dist x 0 < ε`. Under the stated reindexing the witness is N+1 ≥ 1.
- Quotients are the existing `G ⧸ (U n).toAddSubgroup`. Their Mathlib quotient
  topologies are discrete, by the instance for an `OpenAddSubgroup` in
  `Mathlib.Topology.Algebra.OpenSubgroup` (the additive counterpart of its line 283
  instance). Thus these are exactly the discrete quotients in the node. No finite
  cardinality or compactness hypothesis is imposed.
- The quotient maps are `QuotientAddGroup.mk' (U n).toAddSubgroup`. The helper
  `transition U hU n` is `QuotientAddGroup.map` induced by `AddMonoidHom.id G` and hU.
  It is the actual canonical quotient transition, not an arbitrary map.
- H is `(compatibleSubgroup U hU)` coerced to its subtype. The subgroup is the
  intersection of `AddMonoidHom.eqLocus` of the transition after evaluation at n+1
  and evaluation at n. Hence its carrier is exactly the node's compatibility equations.
  Group operations are inherited from the product. The standard product topology and
  `instTopologicalSpaceSubtype` give exactly the required subspace topology.
- The canonical q being simultaneously additive and a homeomorphism is the witness
  `e : G ≃ₜ+ compatibleSubgroup U hU`. Its coordinate equation
  `(e x).val n = QuotientAddGroup.mk' (U n).toAddSubgroup x` fixes its forward map
  to q, including every displayed quotient projection. Its inverse is unique.
- For every space S, `C(S,G)` is Mathlib's `ContinuousMap` with its existing pointwise
  additive commutative group. No separation, compactness or nonemptiness is assumed.
- The function-limit group is `continuousCompatibleSubgroup U hU S`. This is the
  intersection, over s : S, of preimages of H under the additive evaluation map
  `a ↦ (fun n => a n s)`. Membership says precisely
  `∀ s n, transition U hU n (a (n+1) s) = a n s`, equivalently the equality of
  continuous maps `t_n ∘ a_(n+1) = a_n` in the node. It inherits pointwise operations.
- `E : C(S,G) ≃+ continuousCompatibleSubgroup U hU S` is the asserted group
  isomorphism. The displayed equation for every f,n,s fixes it to the quotient maps.
- `S : Type v` and `S' : Type w` have independent arbitrary explicit universes and
  arbitrary `TopologicalSpace` instances. The theorem supplies E and E' with the
  same quotient normalization. For every `a : C(S',S)` its final clause states
  `(E' (f.comp a)).val n = ((E f).val n).comp a` for every f and n. This is exactly
  naturality under every continuous precomposition. No map a is fixed in the hypotheses.
  The coordinates determine E and E' uniquely, so the choices agree for different
  pairs of spaces and the inverse naturality follows as well. The two normalization
  clauses are the claimed compatibility with all quotient projections.

Existing declarations used beyond the sole DAG dependency include
`QuotientAddGroup.map`, `QuotientAddGroup.mk'`
(`Mathlib.GroupTheory.QuotientGroup.Defs`, publicly provided by OpenSubgroup),
`OpenAddSubgroup` and its discrete quotient instance
(`Mathlib.Topology.Algebra.OpenSubgroup`), `ContinuousAddEquiv`
(`Mathlib.Topology.Algebra.ContinuousMonoidHom`), `ContinuousMap` and its pointwise
operations (`Mathlib.Topology.ContinuousMap.Algebra`), `AddMonoidHom.eqLocus`
(`Mathlib.Algebra.Group.Subgroup.Ker`), `AddMonoidHom.pi`,
`Pi.evalAddMonoidHom` (`Mathlib.Algebra.Group.Pi.Lemmas`), and
`ContinuousMap.coeFnAddMonoidHom`. Full relevant signatures and source definitions
were read before constructing the helpers. MetricSpace.Basic provides MetricSpace;
MetricSpace.Cauchy supplies the sequential completeness interface used by the proof plan.

Edge cases checked: the zero group satisfies the hypotheses and gives trivial quotient
and limit groups. If all U_n are zero in a discrete group, the compatible family is a
constant sequence and reconstruction is valid, including an infinite discrete group
with the bounded discrete metric (complete, noncompact, and with infinite quotients).
Repeated subgroups are permitted. Shrinking excludes a nonzero intersection of all U_n
by metric separation, exactly as needed. Empty S gives the trivial continuous-function
group and its trivial compatible-family group; empty S' and identity precomposition
are also included. The only fixed index set is the nonempty countable tower from the
node, reindexed from positive naturals to naturals. No coefficient or index universe
restriction, finite-quotient assumption or compactness assumption was introduced.

Searches, run with the required msearch wrapper and retained in sandbox searches.jsonl:

- LeanFinder: `A complete metric abelian group with decreasing shrinking open subgroups
  is homeomorphic to the inverse limit of its discrete quotients`: eight hits, principally
  `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`, `isoLimittoFiniteQuotientFunctor`,
  `toLimit`, `isIso_toLimit` and additive profinite instances. Read the profinite limits
  source: those hypotheses require profiniteness and finite quotients, absent here.
- Loogle: `"QuotientAddGroup", "limit"`: no hits.
- Mathlib grep through msearch: `(complete|Complete|[Ll]imit).*(OpenAddSubgroup|openAddSubgroup)|
  (OpenAddSubgroup|openAddSubgroup).*([Ll]imit|complete|Complete)`: no hits.
- LeanSearch: `A complete metric abelian group is the inverse limit of its quotients by
  decreasing open subgroups tending to zero`: eight hits: profinite reconstruction,
  quotient completeness, and AdicCompletion. Quotient completeness does not reconstruct
  the group; adic completion uses a ring/module filtration and does not derive the needed
  reconstruction from metric completeness. None matches this statement.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `metric.*group.*quotient|shrinking.*subgroup|completeMetricGroupQuotients`, then for
  `CompleteMetricGroupQuotients|continuousCompatibleSubgroup|compatibleSubgroup`, including
  `dag/lean_names_upstream.json`: no existing declaration matches the notion or these names.
  General complete/quotient searches return adic completion, the parent CompleteNormOpenTest,
  and unrelated quotient comparisons. None states this group reconstruction.

Validation: scompile.py compiles the module cleanly in both its sandbox and library module
contexts. The first compile exposed a missing metric-space import and the evaluation
homomorphism's missing input-coordinate projection. Both were repaired: MetricSpace.Basic
is now public, and each point evaluation composes with the appropriate `Pi.evalAddMonoidHom`
on the family of continuous maps. The only theorem is the full reconstruction statement,
with its nine-step proof documented and postponed as required for stage 2.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
