## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionCokernelCohomology` states
`AlgebraicGeometry.Scheme.Modules.closedImmersion_cokernel_cohomology` with `sorry`.
Its two helpers have fully specified data: `closedImmersionCokernelArrow` is
`c.toLinearMap.comp H(u)`, using restriction of scalars on the existing derived-functor
map; `closedImmersionCokernelBoundary` is the specified module-cohomology boundary,
restricted to the base field and composed with `c.symm.toLinearMap`. There are no
new cohomology, direct-image, scalar-action or boundary constructions and no new DAG nodes.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. The schemes are `{X Y : Scheme.{u}}`.
  The two structure morphisms are `[X.Over (Spec (.of k))]` and
  `[Y.Over (Spec (.of k))]`; their maps are `X ↘ Spec (.of k)` and
  `Y ↘ Spec (.of k)`. The morphism is `i : Y ⟶ X`, with
  `[IsClosedImmersion i]` and `[i.IsOver (Spec (.of k))]`. Thus the structure maps
  commute, and this is a closed immersion over the specified field.
- The arbitrary module sheaves are `L E : X.Modules` and `M : Y.Modules`.
  Mathlib's `Scheme.Modules` is definitionally `SheafOfModules` over the underlying
  ring sheaf, hence is the scheme specialization of the recorded `ringedSiteModules`.
- The direct image is Mathlib's `Scheme.Modules.pushforward i`, defined by
  `SheafOfModules.pushforward i.toRingCatSheafHom`. Its sections at `U` are
  `M(i ⁻¹ᵁ U)`; its scalar action is through the structure-sheaf map.
- Cohomology is the recorded `RingedSpace.moduleCohomology`, not abelian-sheaf Ext.
  `scalarCohomology (X ↘ Spec (.of k)) F q` is this exact module object with scalars
  restricted along `scalarMap (X ↘ Spec (.of k)) ⊤`, and likewise on Y.
  `scalarMap` is the structure-morphism ring map followed by open restriction.
- `∃ c : ∀ (q : ℕ) (M : Y.Modules), ... ≃ₗ[k] ...` gives every nonnegative degree
  and every module, with both directions k-linear. The first conjunct identifies
  its underlying map with `moduleCohomologyEdgeMap i M q`, the recorded canonical
  edge map associated to the identity on `i_*M`. This fixes the comparison, rather
  than choosing an arbitrary vector-space equivalence.
- The second conjunct is naturality for every module map `a : M ⟶ N`, written with
  `scalarCohomologyMap` and `(pushforward i).map a`.
- The third conjunct explicitly says that `c 0 M` sends the derived class of a
  global section `s` to the same section on Y. Classes are formed by
  `globalSectionsFunctor.toRightDerivedZero`; the only change of section is
  `M.val.map (homOfLE (by simp : ⊤ ≤ i ⁻¹ᵁ ⊤)).op`, the canonical identification
  of sections on `i⁻¹(X)` with sections on Y. It uses no chosen section isomorphism.
- The sequence is specified by `f : L ⟶ E`, `u : E ⟶ (pushforward i).obj M`,
  `w : f ≫ u = 0` and `(ShortComplex.mk f u w).ShortExact`. These encode exactly
  the given sheaf short exact sequence, including its arrows.
- `Function.Injective (scalarCohomologyMap ... f 0)` encodes the initial zero.
  For every q, the three `Function.Exact` conjuncts encode exactness at Hq(E),
  Hq(Y,M), and H(q+1)(L). They cover all positions of the infinite sequence,
  including q=0. The incoming and outgoing arrows are the two helpers above.
  All arrows are k-linear: the cohomology maps are underlying morphisms obtained
  by `ModuleCat.restrictScalars`, the comparisons are linear equivalences, and
  both helpers have type `→ₗ[k]`. Exactness of their underlying functions is
  exactly equality of image and kernel in these vector spaces.
- The four hypotheses in the final implication are `IsZero` of scalar cohomology
  of L in degrees 0 and 1, and of E in degrees 1 and 2. These are objects of
  `ModuleCat k`, so `IsZero` is precisely the stated vanishing. The conclusion
  gives `Function.Bijective` for the linear incoming degree-zero map and the
  linear degree-one boundary. Bijective linear maps are exactly linear
  isomorphisms; their specified underlying arrows are retained.
- No quasi-coherence, Noetherian, properness, smoothness, finite-dimensionality,
  nonemptiness, or injectivity-on-global-sections assumptions occur. The standard
  derived categories in the boundary helper only fix localization sizes; no extra
  category-existence hypothesis is imposed.

Dependencies used (module and declarations read in their sources):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the scheme specialization uses Mathlib's transparent `Scheme.Modules`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`, `RingedSpace.moduleCohomology`.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `Scheme.Modules.scalarMap`, `scalarCohomology`, `scalarCohomologyMap`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `Scheme.Modules.moduleCohomologyEdgeMap`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary`:
  `RingedSpace.moduleCohomologyBoundary`.
- Proof-only imports are the recorded modules
  `WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree`,
  `Sheaf.Topology.ClosedPushforwardBoundaryNaturality`,
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism`,
  `WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`, and
  `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`, with
  their recorded declarations `zariskiModuleAbelianCohomologyAgree`,
  `TopCat.Sheaf.closed_pushforward_boundary_naturality`,
  `moduleCohomology_scalar_endomorphism`,
  `RingedSpace.moduleSheaves_abelian_enoughInjectives`, and
  `CategoryTheory.Functor.exists_universal_rightDerived_deltaFunctor`.

The statement-dependency list gains the already landed nodes
`def-sc-field-linear-module-cohomology-operations`,
`def-weil-pbc-module-cohomology-fmap`, and `def-sc-module-cohomology-boundary`,
so the scalar structures, canonical comparison and boundary used in the signature
are explicitly recorded. Their definitions were reused, with no dependency repairs.
The mathematical statement, accepted split, and proof-dependency list are unchanged.

Edge cases checked: q=0 and the initial injection are explicit. For i the identity,
the comparison is the canonical identity and the theorem reduces to the ordinary
module-cohomology sequence. For Y empty, pushforward of M and cohomology of M are
zero; the asserted sequence reduces to the sequence for L→E. Zero modules and zero
arrows satisfying short exactness are allowed. X may be empty. All characteristics
are permitted, and the four vanishings impose no conditions in other degrees.
The target of δ¹ is literally degree 1+1, hence degree 2. Both directions of the
comparison and the boundary orientation agree with the source.

Searches for an existing full statement:

- `msearch.py ... leanfinder "Closed immersion direct image of arbitrary module sheaf
  has naturally isomorphic cohomology and linear long exact sequence over the base field"`:
  8 hits, for open-immersion section identities, immersion app maps and module
  restriction adjunctions; no matching theorem.
- `msearch.py ... loogle '"IsClosedImmersion", "cohomology"'`: 0 hits.
- `msearch.py ... grep 'closedImmersion.*cohomology|cohomology.*closedImmersion|
  ClosedEmbedding.*cohomology'`: 0 hits in Mathlib.
- `msearch.py ... leansearch "Cohomology of direct image under a closed immersion
  of schemes equals cohomology of an arbitrary sheaf of modules and gives a linear
  long exact cohomology sequence"`: 8 hits, for closed-immersion image isomorphisms,
  stalk surjectivity, affineness, stability under base change and open restriction;
  no matching cohomology statement.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id and declaration names: no existing declaration. The only
  item-id hit is a proof docstring in `UniformProjectiveFibreVanishing`.
- Concept searches for closed/cohomology in both project roots located
  `CoherentRegularHyperplaneRestriction` (a coherent hyperplane specialization),
  affine quasi-coherent comparisons, closed topological pushforward comparisons,
  and `ModuleCohomologyFMap`. None states the arbitrary-module, field-linear
  sequence with the four-vanishing conclusion. Their existing canonical
  constructions were reused rather than redefined.

Sources opened: `literature/stacks-project/curves.tex`,
`lemma-genus-plane-curve` (Tag 0BYD), especially the two displayed isomorphisms
in its proof; the dependency source docstrings and full signatures listed above.
No statement fault or STATEMENT-DISPUTED flag was found.

Validation: the delivered module compiled separately through the prescribed
`scompile.py Q86 lem-sfb-closed-immersion-cokernel-cohomology <file>` against the
published live library, with no errors and no warnings. No global build was run.

## Second reading by Q86

This is a second in-session reading; the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review.
I reopened the statement and checked all hypotheses and clauses against the module.
The comparison's direction is H(X,i_*M)→H(Y,M), and its inverse occurs only in the
boundary. The zero-degree normalization uses the canonical class of the same
section on both schemes. All three exact positions are included for every q,
and the initial injection is separate. The final two maps are the precise incoming
map and δ¹ of the same short exact sequence, with the four requested vanishings.
The helpers reuse the actual derived-functor map and actual canonical module boundary,
with standard category sizes, so no data are hidden in sorry. I checked that
`scalarCohomology` has exactly the carrier of `moduleCohomology` and its k-action is
restriction along the two structure maps. The item is about cohomology objects,
not an identification of two complexes; its specified per-degree and sequence
form is retained. No mismatch was found and no statement correction was needed.
