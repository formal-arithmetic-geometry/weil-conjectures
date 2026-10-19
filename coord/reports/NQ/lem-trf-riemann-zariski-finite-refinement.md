## Worker report

Stage-2 repair of `lem-trf-riemann-zariski-finite-refinement`, group NQ.
The delivery adds `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement` and its
complete node `lean` record. The node is copied from the current shared base;
only `lean` changes. In particular `mathlib_searches` is identical to the base,
removing the unauthorized extra search from the returned packet. This is a Lean
statement delivery, not another stage-1 split.

The main declaration is
`AlgebraicGeometry.RiemannZariski.finite_refinement`. Its single postponed proof
is `sorry`. Its docstring carries all twelve steps of the node's proof, with the
named proof dependencies and sources. The other declarations are real structures,
subtypes, the initial topology, and explicit maps. There is no postponed data,
arbitrary proposition field, abstract replacement space, or theorem used to
choose an undetermined object.

### Source and dependency reading

I read the complete item statement and twelve proof steps, and the statement and
Lean/Mathlib records of all four statement dependencies. Their recorded source
signatures and docstrings were opened:

| Node | Imported module and declaration | Meaning used |
| --- | --- | --- |
| `def-pc-integral-scheme` | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral` | Nonempty integral schemes; their generic stalk is a field. |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact` | Finite type is exactly both predicates. |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper` and `AlgebraicGeometry.IsSeparated` | Properness gives separatedness, local finite type and quasi-compactness; quasi-models retain separatedness only. |
| `def-kun-separably-closed` | `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosure` | Separably closed top field and separable algebraic extension, with no perfection hypothesis. |

Also read `Scheme.functionField` in Mathlib's `FunctionField` module,
`Scheme.stalkClosedPointTo` in `Stalk`, and `ValuationSubring` including its
canonical inclusion, local-ring instance, and `IsFractionRing V L` instance.
The field embedding of a model is the generic stalk map, transported by the
specified generic-point equality, not an arbitrary field map.

The paper was obtained in the sandbox from
https://arxiv.org/pdf/0707.3953v3 and read at printed pp. 15--17, §3.2.
The opening definitions identify models as proper generic factorizations and
quasi-models as separated finite-type generic factorizations. Proposition 3.2.1
and Corollaries 3.2.4--3.2.5 give compactness and the actual valuation/centre
bijection. Proposition 3.2.6 and Corollary 3.2.7 give common proper refinements
and the open subspace identification. No source or node statement is changed.
The node's §2.1 valuation-height argument is preserved in the proof docstring.

Recorded proof modules are imported without `public`: Noetherian schemes,
Zariski's main theorem for closed immersions/properness, the valuative criterion,
spectral spaces and `Sheaf.Topology.SpectralDirectedLimit`, the recorded
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`, projective
space and its affine chart, Nagata compactification, and the two valuation
extension/intersection lemmas. Missing/stale local upstream files were read
through `scompile.py --source`, particularly the reduced-closure, projective-space,
Nagata and valuation-local-subring modules. The two height proof dependencies
have no recorded Lean declarations, so no nonexistent imports are invented.

### Each hypothesis and clause

All helper names below are in `AlgebraicGeometry.RiemannZariski`.

| Node text | Lean rendering |
| --- | --- |
| Integral scheme `T` | `(T : Scheme.{u}) [IsIntegral T]`. |
| Finite type over the integers | `(t : T ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType t] [QuasiCompact t]`. The lift places the integers in the scheme universe; it is the same integer ring. No separatedness over the integers is assumed. |
| Function field `k(T)` | `T.functionField`, Mathlib's stalk at `genericPoint T`, with its existing field instance. |
| Fixed separable closure `L/k(T)` | `(L : Type u) [Field L] [Algebra T.functionField L] [IsSepClosure T.functionField L]`. |
| Given generic map | Everywhere the literal `Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫ T.fromSpecStalk (genericPoint T)`. It is not an additional arbitrary map or hypothesis. |
| Integral factorization with first arrow generic | `GenericScheme` has actual `X`, `[IsIntegral X]`, `map`, `generic`, `fac`, and `generic_point : generic (IsLocalRing.closedPoint L) = genericPoint X`. The sole point of a field spectrum is its closed point as well as its generic point. |
| Proper `L`-model | `Model` extends precisely that factorization with `[IsProper map]`. |
| Separated finite-type `L`-quasi-model | `QuasiModel` extends the factorization with `[IsSeparated map]`, `[LocallyOfFiniteType map]`, `[QuasiCompact map]`. |
| Models' and quasi-models' finite separable function fields over `k(T)` | The first conjunct quantifies over every `QuasiModel` and asserts `GenericScheme.IsFiniteSeparableOver (algebraMap T.functionField L)`. This existential field inclusion is finite (`φ.Finite`), separable (`Algebra.IsSeparable` for exactly `φ.toAlgebra`), and commutes with the fixed embedding into `L`. `Model.toQuasiModel` is the explicit real-data conversion, so the same conjunct applies to every proper model. |
| Morphisms of models | `ModelHom M N`: a scheme map `hom`, with `hom ≫ N.map = M.map` and `M.generic ≫ hom = N.generic`. |
| Points of `RZ_L(T)` | `Point T L η` is the subtype of `(M : Model T L η) → M.X` satisfying compatibility for every model morphism. Its index is every proper model, not a chosen subfamily. |
| Limit topology | `pointTopologicalSpace` is `⨅ M, TopologicalSpace.induced (fun x ↦ x.1 M) inferInstance`, exactly the coarsest topology making all projections continuous. |
| Quasi-compactness | The second conjunct is `CompactSpace (Point T L η)`, using that actual initial topology. |
| Valuation ring of `L` with fraction field `L` | `ValuationPoint.V : ValuationSubring L`. Mathlib's defining alternative holds for all elements (the zero case is automatic); it gives the existing valuation-ring, local-ring and `IsFractionRing V L` instances. |
| Centre morphism agreeing with the generic map | `ValuationPoint.centre : Spec (.of V) ⟶ T`, with `Spec.map (CommRingCat.ofHom V.subtype) ≫ centre = η`. The generic inclusion is the subring inclusion, not an arbitrary map. |
| Points precisely the centred valuations, bijectively | `∃ e : Point T L η ≃ ValuationPoint T L η`, with `∀ x, Corresponds x (e x)`. `Corresponds` requires, in every model, a lift agreeing with both the centre and the specified generic map, whose closed-point image is the corresponding coordinate of `x`. Thus this is the canonical valuation correspondence. |
| Finite height of each valuation | `∀ v, ∃ N : ℕ, ∀ n (p : Fin (n + 1) → PrimeSpectrum v.V), StrictMono p → n ≤ N`: a bound on lengths, not on cardinality of the set of prime ideals or on generators of the ring. |
| `RZ_L(U)` by the same construction | In the rest of the theorem, `Point U.X L U.generic` uses the identical `Model`, `Point` and topology definitions with the base replaced by `U.X` and the generic map by `U.generic`. |
| Valuation description over every quasi-model | `eU U : Point U.X L U.generic ≃ ValuationPoint U.X L U.generic`, again characterized by `Corresponds`. |
| Open injection | `j U : Point U.X L U.generic → Point T L η`, with `∀ U, IsOpenEmbedding (j U)`. This includes injectivity, continuity and the subspace topology, not just an open range. |
| Natural map on valuation points | `e (j U x) = ValuationPoint.push U (eU U x)`. `push` retains the same valuation subring and composes its actual centre with `U.map`. |
| Image precisely the valuations admitting a compatible lift | `x ∈ Set.range (j U) ↔ (e x).LiftsTo U`. `LiftsTo` requires the actual `Spec V → U` with both the triangle over `T` and the generic triangle over `Spec L`. |
| Opens cover whenever all valuation points lift | The penultimate conjunct quantifies over arbitrary `I : Type w` and `U : I → QuasiModel ...`, and states `(∀ v, ∃ i, ValuationPoint.LiftsTo v (U i)) → ∀ x, ∃ i, x ∈ Set.range (j (U i))`. |
| Finite common refinement `T'` | The last conjunct quantifies over `I : Type w` with `[Finite I]` and the specified family `U`, and supplies `r : FiniteRefinement U`. Its `model : Model T L η` is proper integral with the required specified generic factorization. |
| Opens `W_i ⊂ T'` | `r.W : I → r.model.X.Opens`, with Mathlib's actual open-subscheme construction and inclusion `(r.W i).ι`. |
| Proper dominant maps `W_i → U_i` | `r.map i : (r.W i).toScheme ⟶ (U i).X`, with `r.proper` and `r.dominant`. |
| Maps are `T`-morphisms even if `T` is nonseparated | `r.over i : r.map i ≫ (U i).map = (r.W i).ι ≫ r.model.map`. |
| Compatible with `Spec L` | Actual `r.generic i : Spec L ⟶ (r.W i).toScheme`; `generic_model` and `generic_quasi_model` give its composites into `T'` and `U_i`. They force each `W_i` to contain the generic point. |
| Finite separable generic extensions for `W_i → U_i` | `r.finite_separable i` says `k(U_i) → k(T')` is finite separable and commutes with both embeddings into `L`. The nonempty generic open `W_i` has the same function field as `T'`. The generic triangles ensure this is the extension for the stated map. |
| Covering clause | For this same refinement, `(∀ x, ∃ i, x ∈ Set.range (j (U i))) → ∀ y : r.model.X, ∃ i, y ∈ r.W i`. It is not a cover assumption imposed on every finite family. |
| Empty finite family | There is no `[Nonempty I]` and no positive-cardinality assumption. `I` may be empty in either covering clause or the refinement clause. The refinement still exists (take the identity model `T`), and its open cover is demanded only under the stated antecedent. |

### Edge cases and size

- The empty scheme is not an integral scheme, so its exclusion is exactly the
  node's hypothesis rather than a new nonemptiness assumption.
- `V = L` (height zero) is a `ValuationSubring`; the prime-chain bound allows
  `N = 0`. No discreteness, rank-one, Noetherianity or finite-generation condition
  is placed on valuation rings.
- In characteristic `p`, the map from the lifted integers and all generic maps
  remain defined. No characteristic-zero or perfection hypothesis is used.
- `T` may be nonseparated over the integers. Its centre maps, lifts and over-`T`
  equalities are retained as morphism data, not inferred from the valuation ring
  or underlying point alone.
- A singleton family admits a proper envelope and its corresponding open; the
  covering conditional applies only if its valuation open covers. An empty family
  gives a refinement with no opens, without asserting that these cover `T`.
- The identity quasi-model is permitted; `IsOpenEmbedding` includes an isomorphism
  onto the entire space, and the lift image condition includes all valuations.
- All schemes, rings and their morphisms use a common arbitrary universe `u`,
  as required by Mathlib's `Scheme` category; the integer ring is lifted to that
  universe. The type of all models and `Point` may live in `Type (u+1)`;
  there is no small-skeleton or smallness hypothesis. Covering/refinement index
  types use an independent arbitrary universe `w`, so no finite or infinite
  family is excluded by an index-universe constraint.

### Searches

These new searches are recorded here, not added to the node's immutable
`mathlib_searches` field.

- `msearch.py ... leanfinder`: "The Riemann Zariski inverse limit space has
  valuation ring points and finite common proper model refinements" returned
  eight hits, chiefly `ValuativeCommSq.valuationRing`, `ValuativeCriterion.eq`,
  and the valuative existence statements. They give generic valuative tools,
  not this space or theorem.
- `msearch.py ... leansearch`: "The Riemann Zariski space has centered valuation
  ring points and an open embedding for each quasi modification" returned eight
  hits, including `PrimeSpectrum.localization_away_isOpenEmbedding`,
  `Scheme.basic_open_isOpenImmersion` and valued-field integer-ring opens.
  None constructs the compatible-model limit or states its theorem.
- `msearch.py ... loogle '"RiemannZariski"'`: zero hits.
- `msearch.py ... grep 'RiemannZariski|Riemann.Zariski|quasi.alteration'
  AlgebraicGeometry`: zero hits in Mathlib.
- `rg` of these concepts in `WeilConjectures` and `lean/Sheaf`, plus the exact
  node id in `WeilConjectures`: no existing implementation of this theorem or
  these model/space definitions. The already-landed Temkin theorem only mentions
  the item in its proof docstring. The birational common-cover nodes concern a
  different specialization and supply no competing definition in Lean.
- `rg` in `dag/lean_names_upstream.json`: no entry for this item's declaration.
- `rg` over DAG node statements confirms that this item itself introduces the
  `L`-model, quasi-model and `RZ_L(T)` notions. `tools/blueprint_refs.py search
  'Riemann Zariski'`: zero blueprint nodes. Accordingly the auxiliary declarations
  belong to this owning node and are all listed in `lean.declarations`; no new
  independent definition node or dependency module is needed.

### Validation

`scompile.py NQ lem-trf-riemann-zariski-finite-refinement
lean/Sheaf/AlgebraicGeometry/RiemannZariskiFiniteRefinement.lean` compiled both
the sandbox and library module without errors or warnings. Every variable and
universe is explicit (`autoImplicit false`). Every source line is at most
100 characters. There is exactly one `sorry`, the main named theorem, and the
signature in the node is extracted verbatim from the final source.

## Second reading by NQ

This is a separate clause-by-clause second pass by the delivering worker; the
brief prohibits starting other agents, and the maintainer supplies the independent
review. I reopened the item statement and final Lean file and checked the table
above against their actual declarations, not against the stage-1 proof alone.

I found and repaired the draft's substantive mismatches: an arbitrary family of
models instead of all models, a freely specified topology instead of the initial
topology, placeholder proposition fields, an arbitrary generic inclusion for
valuations, a missing bijection, and missing ties between a chosen quasi-model,
its injection, and its valuation lift image. They have all been replaced with
real data and explicit characterized maps. The final finite refinement is
parameterized by the input family itself and includes its properness, dominance,
both generic triangles, the over-`T` equality and the conditional cover.

The source check is Temkin §3.2 pp. 15--17: the generic factorization is
schematically dominant (for an integral scheme, the generic-point condition
encoded here); `Point` uses every proper factorization; its topology is precisely
the projection topology; the correspondence remembers the actual valuation centre;
and the open embedding is characterized by composing that centre and admitting
compatible lifts. The last two conjuncts cover arbitrary lift-neighbourhood
families and finite common refinements with no nonemptiness hypothesis. Height
is the bound on strict prime chains, including height zero.

The final pass also verified the four recorded dependency declarations are used,
all defined data is independent of the postponed theorem, the twelve-step proof
is in the theorem docstring, there are no extra assumptions on `T`, and only
`lean` changes in the item JSON. No statement dispute or statement correction
remains. The preflight and delivery wrapper results are recorded below when run.

The prescribed dry run completed successfully: `deliver2.py NQ
lem-trf-riemann-zariski-finite-refinement --no-push` reported
`OK (dry run): commit adfdef8ef1 passes the preflight and compiles; nothing pushed`.
Its exact staged set is the report, the item's node, and the single Lean module.
