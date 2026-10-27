## Worker report

The module `Sheaf.LinearAlgebra.TransfiniteSuccessorGeneratorsSurjective` states
`Module.directSum_toModule_image_of_filtration_successor_generators`, with its sole proof
postponed by `sorry`. It introduces no definitions, helper nodes, or dependency repairs.
The DAG statement and dependency lists are unchanged.

Source read: `literature/stacks-project/algebra.tex`, Tag 058V,
`lemma-direct-sum-devissage`, especially lines 20417–20433 identifying the images
of the partial sum maps by transfinite induction. Also read Definition 058U,
`definition-devissage`, which supplies the increasing, initially zero, continuous
filtration in that source. The assigned node explicitly generalizes the image
argument to successor-generating maps without injectivity; the statement retains
exactly that generalization.

Hypothesis and conclusion correspondence:

- The commutative ring is `(R : Type u) [CommRing R]` and the ambient module is
  `(X : Type v) [AddCommGroup X] [Module R X]`.
- The set ordinal is `(κ : Ordinal.{w})`; the family of submodules through the
  endpoint is `(F : Set.Iic κ → Submodule R X)`. Its increasing property is
  `(hmono : Monotone F)`.
- The modules at indices strictly below the endpoint are
  `(A : Set.Iio κ → Type z)` with the two dependent additive group/module instances.
  The universes of the ring, ambient module, ordinal, and summands are independent.
- Each `t α` is an `R`-linear map from `A α` into the actual submodule
  `F ⟨Order.succ α.val, Order.succ_le_of_lt α.property⟩`. The explicit order arguments
  in the file fix the endpoints of each proof. No independent arbitrary ambient map
  replaces this prescribed map.
- The direct sum `D` is Mathlib's `DirectSum (Set.Iio κ) A`, as recorded by
  `def-weil-pbc-direct-sum-modules`.
- The map `f` is written explicitly as `DirectSum.toModule R (Set.Iio κ) X` applied
  to the maps `(F ...).subtype.comp (t α)`. This is precisely the canonical finite
  sum of the successor maps included into `X`. It is neither a new definition nor
  a universally quantified map requiring an additional hypothesis.
- Initial vanishing is `hzero : F ⟨0, bot_le⟩ = ⊥`.
- Continuity is `hcont`: for every `μ : Set.Iic κ` with
  `Order.IsSuccLimit μ.val`, `(F μ : Set X)` is the union of all earlier
  `(F β : Set X)`. `Order.IsSuccLimit` excludes zero and successors, so no
  extra condition at zero or successor ordinals is imposed.
- Successor generation is `hgen`: every `x` in the successor submodule is a sum
  of a `y` in the preceding submodule and `t α a`, with `a : A α`. The equality
  is in the ambient `X`, matching the node's addition formula.
- For each `β : Set.Iic κ`, the set
  `{a : DirectSum (Set.Iio κ) A | ∀ α : Set.Iio κ, β.val ≤ α.val → a α = 0}`
  is exactly `D_β`. The first conjunct asserts that its set image under the
  canonical `f` equals `(F β : Set X)`.
- The second conjunct is `F ⟨κ, le_refl κ⟩ = ⊤ → Function.Surjective f`, keeping
  the endpoint hypothesis conditional rather than imposing exhaustion in advance.
- There is no injectivity assumption on `t`; no disjointness or uniqueness is added.

Dependency declarations read and used: the dependency node is a Mathlib leaf, so
it correctly has no `lean` record. Its `mathlib_match` names `DirectSum` and
`DirectSum.induction_on` in `Mathlib.Algebra.DirectSum.Basic`, and the module
instance, `DirectSum.lof`, and `DirectSum.component` in
`Mathlib.Algebra.DirectSum.Module`. I read their full signatures and docstrings,
including the finite-support representation and componentwise module structure.
The module publicly imports `Mathlib.Algebra.DirectSum.Module` and
`Mathlib.SetTheory.Ordinal.Basic`; these provide all notions in the statement.
The proof dependency is the same direct-sum node. No proof-only import is missing.
For the canonical map I also read `DirectSum.toModule`, `toModule_lof`, and
`coe_toModule_eq_coe_toAddMonoid`, identifying it with the finite-sum universal map.

Edge cases checked before writing: when `κ = 0`, the direct sum has no coordinates,
`D_0` is zero, and `hzero` gives precisely the required image; exhaustion then forces
the ambient module to be zero. At any `β = 0` the vanishing condition kills all
coordinates. At `β = κ` it imposes none, since all indices are strictly below `κ`.
At a nonzero limit the union includes exactly all earlier stages, including zero.
Zero summands, zero ambient module, and the zero ring are allowed. Noninjective
maps are allowed, for example a zero successor map at a repeated stage, or a
surjective map with nonzero kernel. No nontriviality or nonempty-index assumption
was introduced.

Searches performed for an existing statement:

- `msearch.py leanfinder`: “For a continuous ordinal filtration of a module starting
  at zero, maps generating successors modulo previous stages induce a surjection
  from their direct sum”. Eight results, including `LinearMap.proj_surjective`,
  adic-completion surjectivity, `ModuleCat.FilteredColimits.M.mk_surjective`, and
  `DirectSum.lmap_surjective`. None identifies the images of these transfinite stages.
- `msearch.py leansearch`: “A continuous ordinal filtration of a module starting at
  zero is generated by maps generating its successive quotients”. Eight results,
  concerning `IsModuleFiltration`, ideal filtrations, and measure filtrations;
  none states this theorem.
- `msearch.py loogle`: `DirectSum, LinearMap.range`. Four results:
  `DirectSum.range_lmap`, `DirectSum.range_coeLinearMap`, and the tensor-algebra
  grading inclusion and its evaluation lemma. The first is componentwise; the
  second is a supremum of inclusions of submodules, not the given stage equality.
- `msearch.py grep`: `transfinite|iSup_eq_range_dfinsupp_lsum|range_coeLinearMap`
  in `LinearAlgebra`. Five hits in `Mathlib/LinearAlgebra/DFinsupp.lean`, notably
  `Submodule.iSup_eq_range_dfinsupp_lsum`; these give supremum/range formulas,
  not the transfinite generation argument.
- `rg` in `lean/WeilConjectures` for the exact item id returned no match. Searches
  in `lean/WeilConjectures` and `lean/Sheaf` for transfinite and successor-generation
  terminology found `InvariantCoordinateTransfiniteFiltration` (existence of a
  special coordinate filtration) and `FiltrationSuccessorMapsIndependent` (injectivity
  under independence hypotheses). I read the latter's full theorem and docstring;
  its canonical sum map and ordinal indexing agree with this delivery, but its
  mathematical conclusion and hypotheses are different. No import of that unrelated
  theorem is needed. Searches for the proposed declaration name and
  `successor_generators|successorGenerators` in both libraries and the relevant
  Mathlib directories found no declaration with that name.

No statement correction or disputed mathematical assertion was needed.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
