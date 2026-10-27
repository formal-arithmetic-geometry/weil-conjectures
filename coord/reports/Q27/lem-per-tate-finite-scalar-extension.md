## Worker report

The module `Sheaf.RingTheory.TateFiniteScalarExtension` states
`RestrictedSeries.tate_finite_scalar_extension`, with one `sorry`, and supplies
`RestrictedSeries.constantsAlgebra` with real data `(constants R r).toAlgebra`.
No theorem is proved. No new notion or definition node is needed: the ring and
constant map already exist. The latter's landed node,
`def-trf-restricted-series-presentation`, is added to `stmt_deps` as authorized.
There is no statement correction and no disputed statement.

Hypothesis and clause correspondence:

- The complete fields with nontrivial real-valued absolute values are
  `(K : Type u) (L : Type v) [NontriviallyNormedField K]
  [NontriviallyNormedField L] [CompleteSpace K] [CompleteSpace L]`.
  Normed-field norms are multiplicative real-valued absolute values.
- Nonarchimedean absolute values are `[IsUltrametricDist K]` and
  `[IsUltrametricDist L]`. For the norm metric this is the ultrametric triangle
  inequality. No discretely valued or characteristic-zero hypothesis is imposed.
- The extension is `[Algebra K L]`; a unital field map is injective.
  `[FiniteDimensional K L]` is finite field degree, and
  `(hι : Isometry (algebraMap K L))` imposes exactly the given isometry.
- `(r : ℕ)` includes zero. The ring in each occurrence is Mathlib's actual
  `MvPowerSeries.IsRestricted.subring (fun _ : Fin r ↦ (1 : ℝ))`.
  Multi-indices `Fin r →₀ ℕ` are the same as finite tuples of naturals. The
  weight product at polyradius one is one. Convergence in the cofinite filter
  to zero means exactly that every positive epsilon has finitely many
  coefficients of norm at least epsilon. The inherited operations are
  coefficientwise addition and the finite Cauchy product.
- The first existential binds a ring map `φ`; the first conjunct specifies
  **every** coefficient of `φ f` to be the included coefficient of `f`.
  This determines the map uniquely by power-series extensionality. It is not
  an arbitrary map or an assumption of the desired construction, and no data
  are selected from this existence theorem to define anything else.
- The tensor is `TensorProduct K T_K L`, with Mathlib's ordinary algebraic
  tensor ring structure. Its multiplication is
  `Algebra.TensorProduct.tmul_mul_tmul`. No topological completion occurs.
  The `constantsAlgebra` instance makes the K-algebra on T_K the constant map.
- The second conjunct gives an actual `AlgEquiv` over L. Its source L-algebra
  is explicitly `Algebra.TensorProduct.rightAlgebra (R := K)`; its target
  L-algebra is the constant-series algebra. The equation
  `∀ f c, e (f ⊗ₜ[K] c) = constants L r c * φ f` is exactly the prescribed map,
  and determines it on all tensors by pure-tensor generation. `AlgEquiv`
  supplies multiplicativity, unit preservation, bijectivity and L-linearity.
- The third conjunct quantifies over every type `ι : Type w` and every
  `Module.Basis ι K L`. It gives `bT`, a basis over T_K whose module action on
  T_L is explicitly `φ.toAlgebra.toModule`, and requires
  `∀ i, bT i = constants L r (b i)`. There is no particular chosen basis or
  nonempty-index restriction. Finite degree guarantees the basis is finite.
- The final conjunct `φ.Flat` is the recorded `RingHom.Flat`; it means flatness
  of T_L as a T_K-module via that very coefficient map.
- There is no separability, perfectness, trace, characteristic or positivity
  assumption on r. Independent universes u, v, w are explicit; auto implicits
  and relaxed auto implicits are both disabled.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product`: Mathlib's `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, including `TensorProduct.mk`;
  the universal property `TensorProduct.lift` and uniqueness `ext'` in Basic,
  and `LinearMap.rTensor` in Map were read. The multiplicative structure and
  right scalar structure come from `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat` in
  `Mathlib.RingTheory.RingHom.Flat`; its body is `Module.Flat R S` for
  `f.toAlgebra`, exactly the node's module action.
- `def-trf-restricted-series-presentation`: `RestrictedSeries.constants` in
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, the real codomain restriction
  of `MvPowerSeries.C`. The statement's ring is the subring used by that node.
- The proof imports are `Mathlib.Topology.Algebra.Module.FiniteDimension`
  (`LinearMap.continuous_of_finiteDimensional`, recorded by
  `lem-sfb-finite-dimensional-linear-map-continuous`) and
  `Mathlib.Analysis.Normed.Operator.Basic` (`ContinuousLinearMap.bound`, recorded
  by `lem-trf-continuous-linear-map-norm-bound`). Their full signatures and
  surrounding hypotheses were read. They are plain imports, not public imports.

Edge cases checked mathematically: r=0 has the singleton multi-index set, so all
series are constants and the map is K tensor_K L to L; L=K gives the identity
scalar extension; a purely inseparable finite extension such as
F_p((t)) inside F_p((s)), t=s^p, works by bounded coordinate projections just
as in the separable case. An empty purported basis of a nonzero field cannot
exist; the unrestricted index quantifier introduces no false empty-basis case.
Zero series and scalar zero satisfy the exact coefficient and tensor formulas.
No algebraic closure, finite residue field or discretely valued assumption is used.

Searches actually run through `batch2/msearch.py`:

- leanfinder: "Finite coefficient extension of a Tate algebra is ordinary tensor
  extension and the constants of a field basis form a module basis": eight
  hits on general tensor bases/local rings, no restricted-series statement.
- loogle: `"MvPowerSeries", "IsRestricted"`: twelve hits including the actual
  restricted predicate and subring; these are used, not redefined.
- grep: `TateAlgebra|RestrictedPowerSeries|IsRestricted` in
  `RingTheory/MvPowerSeries`: restricted predicate and closure file, no scalar
  extension theorem.
- leansearch: "Finite scalar extension Tate algebra restricted power series
  ordinary tensor product isomorphism": polynomial tensor equivalences,
  piScalarRight, tensor basisAux and analytic restriction results; no match.

Direct `rg` of both project roots found RestrictedSeriesPresentation and its
consumers; this supplied the existing constants map. A direct search for the
item id in WeilConjectures found no match. Direct declaration-name searches
in Mathlib, both project roots and `dag/lean_names_upstream.json` found no
collision for the two delivered names. DAG searches for Tate algebras and
restricted series identified the existing definition node; no duplicate was
created. The live Mathlib restricted-series source was also read through
`scompile.py --source Mathlib.RingTheory.MvPowerSeries.Restricted`.

Source read: https://math.stanford.edu/~conrad/papers/aws.pdf, Definition 1.1.2
(PDF page 3) and Exercise 2.2.3(3) (PDF page 13), plus the standing complete,
nontrivially nonarchimedean convention. The finite-degree ordinary-tensor and
basis proof is the node's explicitly marked agent specialization. The latest
blueprint ancestor `lem-per-artin-gabber-affine-curve.proof.md` was read; its
Step 3 concerns duality, consistent with the node's inherited-branch note.

Validation: prescribed `scompile.py` compiles the final module in both sandbox
and intended library-module modes cleanly (1.5 seconds each). All declarations
are public in module mode. The sole postponed proof belongs to this DAG item
and its docstring contains all five proof steps.

## Second reading by Q27

Dispatcher assignment prohibits starting another agent; this is a second pass
by the same worker, with independent maintainer review still required.
I reread the node and final signature together. The intermediate ring-equivalence
encoding was replaced by an actual L-algebra `AlgEquiv` with explicit right-factor
algebra structure, so the algebra-isomorphism clause appears directly in the type.
I checked the source and target scalar structures, each coefficient equation,
the pure-tensor formula, the arbitrary basis quantifier and its explicit module
action via φ, and the final flatness conjunct. I also rechecked r=0 and purely
inseparable extensions. No mathematical mismatch remains; the existing constant
map, rather than a second definition, supplies the sole new algebra instance.
