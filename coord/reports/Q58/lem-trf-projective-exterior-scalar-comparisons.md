## Worker report

The delivery states lem-trf-projective-exterior-scalar-comparisons in
Sheaf.LinearAlgebra.ProjectiveExteriorScalarComparisons. All 12 theorem proofs are
`sorry`; the three formula predicates are fully written Prop-valued definitions.
There is no data definition, new independent notion, dependency repair, statement
correction, or STATEMENT-DISPUTED issue. The existing item changes only in `lean`.

Sources read: Stacks more-algebra.tex, section-determinants, the socle remark
0FJA and both proofs of lemma-det-ses 0FJB (lines 36228–36334); perfect.tex,
remark-functorial-det 0FJY (lines 10337–10351); and the current blueprint
latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md for the unit context.
The proof docstrings distribute the accepted node's eight proof steps over the
existence and coherence statements, including the dual-frame inverse, alternating
inverse in characteristic two, socle restriction, chart descent, and the
kernel-first local wedge calculation. No source statement or route is changed.

Hypothesis and clause correspondence:

- A commutative-ring homomorphism A → B is `[CommRing A] [CommRing B]
  [Algebra A B]`, with its actual map `algebraMap A B`. The ring and module
  universes are explicit and independent; no universe equality is imposed.
- A direct summand of a finite free module V is `[Module.Finite A V]
  [Module.Projective A V]` in `projectiveScalarComparisons`. This is the usual
  equivalent finite-projective characterization. Coherence theorems are stated
  for the uniquely formula-characterized comparisons; these exist under exactly
  the finite-projective hypotheses of that theorem. They do not require any
  additional choice or uncharacterized map.
- For every r ≥ 0 is `∀ r : ℕ`. The first conjunct is `∃! e` with source
  `B ⊗[A] (⋀[A]^r V)` and target `⋀[B]^r (B ⊗[A] V)`.
- The exact displayed exterior formula is the second conjunct of
  `IsExteriorScalarComparison`, using `exteriorPower.ιMulti` and
  `fun j ↦ (1 : B) ⊗ₜ[A] v j`. Its first conjunct also records the ambient
  `ExteriorAlgebra.scalarExtensionMap` formula for every exterior-power element.
  Thus the determinant and exterior maps are restrictions of the same map, not
  unrelated equivalences with the right source and target.
- The second comparison has source `B ⊗[A] Dual A V` and target
  `Dual B (B ⊗[A] V)`, where `Dual` is Mathlib's actual module dual.
  `IsDualScalarComparison` says for all b,b',l,x that evaluation is
  `b * b' * algebraMap A B (l x)`, exactly the stated bilinear formula.
- Exterior naturality is the first conjunct of `scalarComparisons_naturality`,
  on arbitrary elements, with `exteriorPower.map r f` and `f.baseChange B`.
  The second conjunct uses `f.dualMap` contravariantly, in the direction from
  the scalar-extended dual of W to the dual of the scalar-extended V. There is
  no restriction on the linear map f.
- Evaluation compatibility is `scalarDual_evaluation`, on arbitrary dual tensors
  and vector tensors. `TensorProduct.lift (LinearMap.id : Dual A V →ₗ[A] Dual A V)`
  is the existing tensor universal-property evaluation map; `distribBaseChange`
  and `rid` express the ordinary canonical tensor and scalar identifications.
- Ordinary symmetry compatibility is `scalarTensor_symmetry`, the equality of
  the tensor-distribution square with Mathlib's `TensorProduct.comm`. This uses
  ordinary tensor symmetry with no graded sign. These same constraints are used
  in the evaluation and determinant squares.
- Preservation of exterior products is `scalarExterior_product`, specifying the
  product after ambient exterior inclusions in degrees r,s,r+s. The explicit
  input z with `z.val = x.val * y.val` avoids introducing a duplicate exterior
  product construction. Such z exists by graded multiplication of exterior powers.
- Identity scalar extension is `scalarComparisons_identity`, simultaneously for
  exterior powers, duals and determinants, using `TensorProduct.lid`. Each is
  written on spanning tensors, and for duals evaluated on every vector; this
  is precisely the corresponding full linear-map equation.
- Successive scalar-extension associativity is `scalarExterior_tower`,
  `scalarDual_tower`, and `scalarDeterminant_tower`. Their hypotheses introduce
  A → B → C with `[IsScalarTower A B C]`; they use the standard
  `TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C V`, sending
  c tensor (b tensor v) to c*beta(b) tensor v. They compare the iterated and
  direct maps on arbitrary spanning tensors, including arbitrary dual evaluations.
- The third conjunct of `projectiveScalarComparisons` gives `∃! s` from
  `B ⊗[A] determinantModule A V` to `determinantModule B (B ⊗[A] V)`.
  `IsDeterminantScalarComparison` specifies its exterior inclusion as exactly
  the same exterior scalar-extension map used for all exterior powers. The
  dependency's `determinantModule` is the actual variable-rank socle, and there
  is no constant-rank or free-module hypothesis.
- Determinant naturality for isomorphisms is `scalarDeterminant_naturality`.
  The element y is determined by `y.val = ExteriorAlgebra.map f.toLinearMap x.val`;
  its existence is concluded, not assumed. The second equation is the naturality
  square after the injective socle inclusion, for every scalar b. This states
  naturality without adding a second determinant action construction.
- The zero-module unit clause is `scalarDeterminant_zero`, for any subsingleton
  module model. It uses the dependency's normalization of the two determinant
  identifications by `algebraMap`, and concludes `b * algebraMap A B (eA x)`.
  It therefore states the exact multiplication unit comparison, not mere existence
  of an unspecified isomorphism of rank-one modules.
- A short exact sequence is i,p with `Function.Injective i`,
  `Function.Surjective p`, and `Function.Exact i p`. All three modules have both
  finite and projective instances in `scalarDeterminant_exactSequence`.
- The original gamma is e with the dependency's
  `IsDeterminantExactSequenceMap i p e`; its existence and uniqueness are provided
  by the recorded dependency `existsUnique_determinantExactSequence`.
  The conclusion first asserts exactness of the scalar-extended sequence. It then
  produces eB with that same kernel-first predicate for `i.baseChange B` and
  `p.baseChange B` and states the square
  `sV (b ⊗ e(x ⊗ y)) = eB (sU(b ⊗ x) ⊗ sW(1 ⊗ y))`.
  Pure tensors span, so this is precisely the full square through the usual
  scalar tensor-distribution equivalence, not a restriction to chosen bases.
- No flatness, nontriviality, positive-rank or characteristic assumption occurs.

Dependency declarations used (full source signatures and docstrings read):

- Mathlib.Algebra.Module.Projective: `Module.Projective`, with its splitting
  characterization `Module.Projective.iff_split` and finite-projective context.
- Mathlib.LinearAlgebra.ExteriorAlgebra.Basic and ExteriorPower.Basic:
  `ExteriorAlgebra`, `ExteriorAlgebra.ι`, `ExteriorAlgebra.ιMulti`, `exteriorPower`,
  `exteriorPower.ιMulti`, `exteriorPower.map`, and the proof dependency
  `exteriorPower.alternatingMapLinearEquiv`.
- Mathlib.LinearAlgebra.TensorProduct.Basic and TensorProduct.Tower:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.comm`,
  `TensorProduct.lid`, `LinearMap.baseChange`, and the ordinary scalar constraints
  `TensorProduct.AlgebraTensorModule.rid`, `.distribBaseChange`, `.cancelBaseChange`.
- Sheaf.LinearAlgebra.ProjectiveDeterminantModule:
  `Module.determinantModule`, `ExteriorAlgebra.scalarExtensionMap`.
- Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence:
  `Module.IsDeterminantExactSequenceMap`,
  `Module.existsUnique_determinantExactSequence`,
  `Module.determinantModule_topExterior`, `.determinantModule_localization`,
  `.determinantModule_zero` and `.determinantModule_finite_projective`.
- Mathlib.LinearAlgebra.Dual.BaseChange / Dual.Defs:
  `Module.Dual`, `LinearMap.dualMap`, `Module.Dual.baseChange`; the existing
  `IsBaseChange.toDualBaseChange` requires finite freeness and does not state this
  item's finite-projective comparison or its determinant coherence.
- Proof-only import WeilConjectures.RingTheory.CoverModuleExact:
  `RingTheory.coverModuleExact`. The standard-free-cover module and theorem
  `Module.exists_standardFreeCover_of_finite_projective` are already publicly
  imported by the determinant exact-sequence dependency. The projective splitting
  Mathlib declaration is also available through those imports. The proof-only
  dependency lem-trf-projective-determinant-chart-descent has no recorded Lean
  module, so no nonexistent import is introduced.

Edge cases checked before drafting and again against the actual signatures:

- r=0: `Fin 0` gives the empty wedge; the canonical exterior map preserves scalars.
- Degree above a local rank: both exterior powers vanish; the formula still types.
- V=0, and U=0 or W=0 in a sequence: no positive-rank assumption; zero determinant
  normalization and the same kernel-first formula apply to empty basis lists.
- Zero rings, including a scalar map to the zero ring: no `Nontrivial` hypothesis;
  every displayed equality and equivalence remains meaningful.
- Characteristic two: alternation, rather than division by two, is used in the
  accepted proof; no graded sign is inserted in ordinary tensor symmetry.
- Nonflat extensions: the quotient module is projective, so tensoring the split
  exact sequence remains exact; no appeal to tensor preservation of arbitrary
  nonsplit kernels or annihilators is made.
- Disconnected bases and varying ranks: the socle determinant is used verbatim,
  with no selected global rank. Three module universes and ring tower universes
  remain independent.

Searches performed with the authorized msearch.py wrapper (raw results are in
searches.jsonl in the sandbox):

- leanfinder: "Exterior powers and finite projective duals commute with scalar
  extension naturally with determinant exact sequence". Eight hits: pairings,
  finite-free `IsBaseChange.toDualBaseChange` / `.dual`, and degree-one naturality;
  no match for the whole statement or its variable-rank determinant comparison.
- loogle: "Module.Dual.baseChange, exteriorPower.map". Zero hits.
- grep Mathlib LinearAlgebra/ExteriorPower: "baseChange|BaseChange". Zero hits.
- leansearch: "exterior powers finite projective modules scalar extension determinant
  naturality". Eight hits: exterior definitions, maps, degree-one naturality and
  ModuleCat exterior functors; no scalar-comparison theorem matching this item.
- Direct rg of WeilConjectures and Sheaf for the item id and exterior/determinant
  base-change names: no existing match. The Koszul scalar-change maps are only for
  their chosen free Koszul modules. Direct reads of the determinant modules found
  the socle and exact-sequence interfaces, reused as recorded.

Validation: scompile.py compiled the full file in module mode both as sandbox and
as Sheaf.LinearAlgebra.ProjectiveExteriorScalarComparisons, cleanly (12.9 s / 5.8 s).
The first elaboration found missing TensorProduct namespace qualification on the
scalar constraints and the nonstandard parameter order of LinearEquiv.baseChange;
these were repaired using the actual APIs. No warning beyond permitted sorry usage
remains. No source checkout, launcher file or live library was modified.

## Second reading by Q58

A separate pass over the written file and the unchanged node checked the formula
predicates, all 12 theorem signatures, and the actual dependency declarations.
This is a self-check by the dispatched worker, not a claim of independent agent
review; the brief prohibits starting other agents and assigns independent review
to the maintainer. The check confirmed: both coefficients occur in the dual
formula; the dual square is contravariant; the tensor square uses ordinary
symmetry; the scalar-tower coefficient is c*beta(b); the determinant inclusion
formula is the restriction of the same exterior map; the zero comparison uses
the normalized algebraMap identifications; and the exact-sequence wedge order
is kernel first. The source of gamma and the predicate specifying gamma are the
recorded dependency declarations. All theorem hypotheses describing comparisons
are satisfiable by the existence theorem, so they are not arbitrary isomorphism
assumptions. The existence of the extended gamma is concluded explicitly rather
than assumed. No mathematical mismatch or silent statement correction was found.
