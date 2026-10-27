## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.PrimitiveCyclicWeightBound` states
`AlgebraicGeometry.RationalHighestWeight.primitive_cyclic_weight_bound`, with the sole proof
`sorry`. It states precisely the multiplicity-one and weight-bound clauses of Milne,
Algebraic Groups (2017), Proposition 22.17, printed p.467, for the finite-dimensional
case requested by the DAG. I read that proposition and the coefficient comparison in
22.14, p.466, directly from the local PDF. Dominance and a largest proper submodule,
which are further assertions of Milne's proposition, are not assertions of this node.
The node statement and proof plan are unchanged. No statement is disputed.

The statement uses an existing notion rather than defining a second rational-module API.
Its `stmt_deps` gains the already landed `def-sfb-rational-highest-weight-data`.
There are no new nodes and no dependency repairs. The only other node-field change is
its new `lean` record.

Hypothesis-by-hypothesis correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- `G : Grp (Over (Spec (.of F)))` is the actual group scheme over F, and
  `hG : ReductiveTorusCentralizer.IsReductive G` gives precisely the smooth,
  connected, affine finite-type reductive group of the node over an algebraically
  closed field. This is the predicate used by its Borel-pair dependency.
- `T`, `iT`, `hT : IsMaximalTorus iT`, and `hsplit` give the fixed split maximal torus.
  `B`, `iB`, `hB : IsBorelGroupScheme iB.hom.hom`, `j : T ⟶ B`, and
  `hj : j ≫ iB = iT` give the fixed Borel containing that torus.
- `U`, `iU`, `hUclosed`, `hUnormal`, `hUsmooth`, `hUconn`, `hUunip`, and `hUmax`
  describe the unipotent radical with exactly the universal maximality condition
  supplied by `reductive_borel_pair_structure`. `p : B ⟶ T`, `hp`, `hker`,
  and `hsplitB` express its projection, identity on T, kernel U, and the
  multiplication isomorphism U times T to B. All are the data fixed by the node's
  phrase “as in lem-sfb-reductive-borel-pair-structure”, not new restrictions.
- The explicit `IsAffine` instances for G, T, B are consequences of reductivity,
  split torus, and closed-subgroup inclusion in affine G; they expose the instances
  needed to form the canonical coordinate algebras. The two `IsCommMonObj`
  instances expose the torus and G_m commutativity witnesses appearing in the
  Borel-pair theorem. None imposes a new mathematical hypothesis.
- `aG`, `aB`, `haG`, and `haB` pin down actual conjugation by iT and j, rather
  than permitting an unrelated torus action on either tangent space.
- `Φ`, `P : RootDatum Φ ...`, `base : P.Base`, `hred`, `hroot`, `hpair`, `hΦ`,
  and `hpos` are the root datum and simple-root base of the Borel-pair theorem:
  roots are actual nonzero character weights in Lie(G); roots of Lie(B) are
  exactly the positive ones. `hroot` identifies each root with its actual character;
  `hpair` pins the integer pairing to character/cocharacter composition. Thus
  `base.support` is the specified Delta, with the sign determined by B.
  Finite generation of the lattices, another output of the Borel-pair theorem,
  is not needed as an extra hypothesis: splitness already implies it.
- `{M : Type v} [AddCommGroup M] [Module F M] [FiniteDimensional F M]` is the
  arbitrary finite-dimensional F-vector space, in its own universe.
- `c : M →ₗ[F] M ⊗[F] coordinateAlgebra G`, `hcoassoc`, and `hcounit` are the
  exact linear coaction, coassociativity, and counit identity. The coordinate algebra
  is the actual global-section algebra F[G] with its canonical Hopf structure.
- `lam : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))` is the
  actual character lambda written additively; `.toMul` returns the group-scheme map.
- `v : M`, `hv : v ≠ 0` give the nonzero generating vector.
- `heigen` is `(1 tensor iB*) c(v) = v tensor (lambda o p)*(t)`, using the existing
  `coordinateMap` and `characterElement`. Evaluating this identity at any algebra
  map F[B] to A gives the node's identity for every b in B(A). Conversely use the
  universal point with A=F[B]. Thus this is precisely the stated algebra-valued
  eigenvector condition, without reducing to F-points or differentiating characters.
- `hcyclic : ∀ N : Submodule F M, IsStable c N → v ∈ N → N = ⊤` states that
  every rational submodule containing v is M. Since M itself is rational, this
  is exactly that the smallest rational submodule containing v is M.

Conclusion-by-conclusion correspondence:

- `LinearMap.eqLocus ((coordinateMap iT).toLinearMap.lTensor M ∘ₗ c)
  ((TensorProduct.mk F M (coordinateAlgebra T)).flip (characterElement lam.toMul))`
  is M_lambda: it consists exactly of m with restricted coaction m tensor lambda.
  The same universal-point argument proves equality with the all-A definition
  in the node, including nonreduced A. Equality to `Submodule.span F {v}` says
  M_lambda=Fv, not merely a dimension bound or existence of one eigenvector.
- The second conjunct quantifies over every character `mu` of T. Its premise
  that the same coaction equalizer for mu is not bottom says exactly M_mu is
  nonzero. It concludes `∃ n : Φ → ℕ, mu = lam - ∑ α ∈ base.support, n α • P.root α`.
  Natural numbers are exactly nonnegative integers here, and nsmul is repeated
  addition in the character lattice. Values of n off `base.support` are ignored;
  any function on the simple roots extends by zero, so the index type does not
  strengthen the conclusion. The sum is finite and ranges over precisely Delta.
- There is no simplicity hypothesis and no `CharZero`/characteristic bound.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`, read with its docstring and full class
  signature. `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with its
  all-polynomials-split definition and root-existence equivalence. The algebraic
  closure node's `mathlib_match` explicitly records this predicate, not just the
  bundled `AlgebraicClosure` construction.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, the group-object
  structure (multiplication, inverse, unit diagrams), used through `Grp` over Spec F.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`. I read its full signature
  and proof docstring. Its imported `IsReductive`, `IsMaximalTorus`,
  `IsBorelGroupScheme`, and `TorusCharacterTangent.weightSpace` definitions were
  also read. The statement copies its actual radical, projection, conjugation,
  root-datum and positive-base interfaces, without assuming semisimplicity.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `coordinateMap`, `IsStable`, and
  `characterElement` in `AlgebraicGeometry.RationalHighestWeight`.
  I read the entire module and the owning node. Its reused
  `HopfAction.Coassociative` and `HopfAction.Counital` signatures in
  `Sheaf.RingTheory.HopfActionModuleData` were read explicitly.
- `Mathlib.Algebra.Module.Submodule.EqLocus`: `LinearMap.eqLocus` supplies the
  linear subspace defined by the coaction equality, so no new weight-space
  definition or arbitrary supplied subspace is needed.
- `Mathlib.LinearAlgebra.RootSystem.Base`: `RootPairing.Base`, with finite
  support, root/coroot independence and signed nonnegative generation.
- Each already stated proof dependency is imported without `public`:
  `Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts`
  (`AlgebraicGeometry.bruhat_longest_cell_charts`),
  `Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates`
  (`AlgebraicGeometry.borel_root_product_coordinates`),
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`
  (`AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`),
  `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
  (`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant`), and
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
  (`AlgebraicGeometry.Scheme.Hom.image`). Their full signatures and available
  docstrings were read. The Borel-pair proof dependency is already a public import.
  The natural-language proof in the theorem's docstring records all six DAG steps.

Edge cases checked before writing:

- M=0 has no nonzero v, as required; the theorem does not introduce an unrelated
  nontriviality assumption on M.
- For a torus G=T=B, U is trivial and Phi and Delta are empty. The sum is zero;
  cyclicity of a weight vector gives M=Fv, and the only weight is lambda.
  This also includes the trivial group and the zero character.
- A one-dimensional character module gives M_lambda=M=Fv and all coefficients zero.
- Reducible or nonsimple cyclic modules remain covered: `hcyclic` only concerns
  submodules containing v and does not say all nonzero submodules are M.
- In positive characteristic, coaction equalizers distinguish characters differing
  by p multiples, even if their differentials agree. All coefficient algebras,
  not only fields or reduced rings, remain included by the universal coaction test.
- The sign agrees with an upper-triangular Borel for SL2: its primitive vector is
  the highest vector, and opposite-root coefficients lower its character.
- F and M have independent universes u and v. Equalizer equations need no quantified
  test-algebra universe and hence exclude no algebra-valued cases.

Searches actually run (no exact existing theorem found):

- `msearch.py` LeanFinder: “A cyclic rational representation generated by a Borel
  eigenvector has highest weight multiplicity one and weights below its highest
  weight”: eight LieModule chain results, including
  `LieModule.genWeightSpace_nsmul_add_ne_bot_of_le`, no rational group-scheme theorem.
- `msearch.py` Loogle: `Representation, weightSpace`: zero hits, with note
  `loogle: unknown identifier 'weightSpace'`; not evidence that rational coactions
  are absent, which was separately checked in source.
- `msearch.py` grep: `RationalRepresentation|RationalModule|Comodule|highest.weight`:
  two unrelated Mathlib files, Young tableaux and Lie basis products.
- `msearch.py` LeanSearch: “Weights in a cyclic rational representation generated
  by a Borel eigenvector are below the generating weight”: eight LieModule results,
  including `LieModule.weightSpace_le_genWeightSpace`, no matching group-scheme result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for rational representations,
  coactions, highest weights, cyclic highest weights and weight spaces: found the
  existing RationalHighestWeightData, the coaction dictionary, and the downstream
  SimpleModuleDualHighestWeight module. The first is reused. The downstream theorem
  assumes simplicity and states highest-weight classification, not this cyclic lemma.
  No node-id hit for this item occurred in `lean/WeilConjectures`.
- `rg` for `primitive_cyclic_weight_bound|primitiveCyclicWeightBound` in the
  upstream-name index and both Lean roots: no declaration with the proposed name.
- Read the current blueprint `literature/blueprint/latest` (snapshot main-20261024,
  ef6f9619fdbffa59e88528fb56483d76c70258c8); its highest-weight search gives no
  equivalent blueprint statement. This item is the Milne supporting input described
  by its inherited blueprint provenance, not the unit's own statement.

Validation: scompile.py compiled the delivered module both under the sandbox module
name and its library module name, each in 2.4 seconds, with no errors or warnings.
The file contains only the one named theorem with proof `sorry`, no helpers or data
choices. All variables and universes are explicit (`autoImplicit false`), every line
has at most 100 characters, and the recorded signature is copied verbatim from the file.

## Second reading by N0

No second reading by a worker: this dispatcher assignment forbids other agents.
The worker delivers directly and the maintainer's independent review reads the delivery.
