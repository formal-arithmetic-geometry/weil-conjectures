## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleChartRationalPointTaylorIso` states
`AlgebraicGeometry.EtaleChartTaylor.exists_unique_taylor_iso`, with `sorry` as its
whole proof. The six auxiliary declarations are real constructions or the
finite-level predicate belonging to this theorem. They do not assert postponed
facts or choose any object from an unproved existence theorem. All seven names
are listed in `lean.declarations`. No node statement or dependency list changes.

Hypotheses and objects, matched against the node:

- The fields and extension are `{k L : Type u} [Field k] [Field L] [Algebra k L]`.
  The arbitrary common universe can be taken large enough for any such fields
  and scheme; no universe equation between independent test objects is imposed.
- The k-scheme is `{U : Scheme.{u}} (p : U ⟶ Spec (.of k))`.
- The integer is `(n : ℕ)`, including zero. The chart is
  `t : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))`, with `[Etale t]`.
  The equality `ht` states exactly that this is a morphism of k-schemes.
  `ULift (Fin n)` is Mathlib affine space's coordinate-universe convention,
  still with exactly n coordinates; series are indexed by `Fin n`.
- `baseChange p L` unfolds to the actual `pullback p (Spec.map ... (algebraMap k L))`.
  Its second projection, not an arbitrary map, supplies the scalars.
- `(b : baseChange p L)` is the specified point. `hb` is bijectivity of
  `residueMap p b`, the composite of the canonical scalar map into the stalk
  with `Scheme.residue`. Thus it requires the structural residue extension to
  be trivial, not merely an abstract field isomorphism.
- The local ring is `(baseChange p L).presheaf.stalk b`, with its Mathlib
  `IsLocalRing.maximalIdeal`; the completed ring is its `AdicCompletion`.
- `coordinate p t b i` is the germ of the pullback of `AffineSpace.coord` along
  the first projection and t. `centeredCoordinate` is that germ minus the scalar
  image of its residue, transported to L by
  `(RingEquiv.ofBijective (residueMap p b) hb).symm`. This is exactly t_i-c_i.

Conclusion, clause by clause:

- The existential θ is a ring homomorphism from `MvPowerSeries (Fin n) L` to
  the specified completion. `IsExpansion` first requires θ(C a) to be the
  completed structural scalar a, precisely the L-algebra homomorphism condition.
  This explicit condition avoids introducing an unrelated algebra instance.
- Its second conjunct is the required formula for every `r : ℕ` with `1 ≤ r`
  and every series f, using `AdicCompletion.evalₐ ... r`. Mathlib's
  `MvPowerSeries.truncTotal r f` has coefficients a_E exactly for |E|<r and zero
  otherwise (`coeff_truncTotal`, `coeff_truncTotal_eq_zero`). Evaluating this
  polynomial using `MvPolynomial.eval₂` and the centered germs is exactly the
  displayed finite sum, then `Ideal.Quotient.mk` takes its class modulo m_b^r.
- The next quantified conjunct says that every θ' satisfying exactly the same
  L-algebra and finite-level conditions equals θ. Neither existence nor
  uniqueness assumes continuity, bijectivity, or any desired conclusion.
- `Function.Bijective θ` states isomorphism. `IsLocalHom θ` states locality;
  the conclusion also supplies `hlocal : IsLocalRing` of the completion.
  These conditions with bijectivity also give the source local-ring structure.
- The `Ideal.map θ (Ideal.span (Set.range MvPowerSeries.X))` equality says that
  (T_1,...,T_n) maps onto the completion's maximal ideal. The explicit `hlocal`
  argument makes that ideal meaningful without adding a Noetherian hypothesis
  or requiring a proof of local Noetherianity during statement elaboration.
- `∀ i`, the displayed θ(X i) equality is the completed image of t_i-c_i.
- The level-one equality with `scalarMap ... (MvPowerSeries.constantCoeff f)`
  specifies the induced residue map: under the structural identification with L,
  it is constant-coefficient evaluation, hence the identity on residue scalars.
- The `n = 0` implication asserts bijectivity of L -> O_{U_L,b} and of its
  composite with the completion structural map. The coefficient condition
  already identifies θ with that latter structural map on the zero-variable
  series ring. Thus both parenthetical zero-variable assertions are included.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  structure presheaf, `Scheme.Hom.appTop` and germs.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, its
  structural projection and `AffineSpace.coord`. `AffineSpace.SpecIso` was also
  read to check agreement with the polynomial spectrum in the proof plan.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (exposed by the
  affine-space imports): `pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.Γevaluation`; the implemented residue map is the
  same germ-and-residue composite, preceded by the structural scalar map.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  retained as the recorded localization dependency; local rings here are the
  actual scheme stalks, not separately chosen localization models.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its canonical algebra map and `AdicCompletion.evalₐ`.
- `Mathlib.RingTheory.MvPowerSeries.Basic` (through `.Trunc`): `MvPowerSeries`,
  `MvPowerSeries.C`, `MvPowerSeries.X`, `MvPowerSeries.constantCoeff`;
  `.Trunc` supplies `MvPowerSeries.truncTotal`.

The plain imports retain the recorded proof dependencies: affine-stalk
localization, Noetherian finite-type algebras and localizations, locally
Noetherian schemes and their local-finite-type permanence, flatness,
`IsUnramified`, `unramified_neighbourhood_iff_maximalIdeal_residue`,
`RingHom.flat_local_completion_iso`,
`AddMonoidAlgebra.monoidCompletion_coefficients`, and local completion structure.
The module docstring and theorem docstring give the source and all seven proof
steps. The source read was `literature/stacks-project/etale.tex`,
`lemma-characterize-etale-completions` (Tag 039M), including the following
residue-degree remark. No algebraic-closedness hypothesis is needed when the
actual residue degree is one.

Edge cases checked: n=0 retains its constant monomial in every positive-degree
truncation, has no coordinate-image obligations and has the explicit two
structural isomorphism clauses. The empty scheme has no b, so its case is
correctly conditional. No global finite-type, quasi-compactness, separation,
closedness of b, characteristic-zero, perfect-field, or algebraic-closedness
hypothesis has been added. In positive characteristic evaluation of finite
polynomials still makes sense and needs no factorial denominators. L=k is
allowed. The rationality condition concerns the structural map, which excludes
nontrivial residue extensions without excluding nonclosed rational points by an
extra topological assumption.

Searches actually run:

- `msearch.py ... leanfinder` with “Completed local ring of an etale chart at a
  rational point over a field is the multivariate power series ring with shifted
  coordinates”: eight hits about standard étale algebras and presentations,
  none the specified Taylor-completion theorem.
- `msearch.py ... loogle "AdicCompletion, Algebra.Etale"`: zero hits.
- `msearch.py ... grep "etale.*complet|complet.*etale|toAdicCompletionAlgEquiv"`:
  twelve hits, chiefly `MvPowerSeries.toAdicCompletionAlgEquiv` and étale
  idempotent splitting. The former is the polynomial-completion ingredient,
  not the theorem for an étale chart at b after field extension.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for Taylor, rational-point
  completion and étale-completion patterns found, among others,
  `EtaleCompletedLocalRingIso.lean`. Its theorem assumes an algebraically closed
  field and relates two completions; it does not state this coordinate-normalized
  theorem. The exact item-id grep in `lean/WeilConjectures` found no declaration.
- Namespace/name searches in the project and Mathlib found no declaration in
  `AlgebraicGeometry.EtaleChartTaylor`. A `fieldStalkMap` in
  `ConormalSequenceSmoothImmersion.lean` is private; its germ formula was read
  as an additional check of the actual structural scalar construction.

Validation: scompile.py compiled the file in module mode, both as a sandbox
module and at its library module name, cleanly (11.0 s and 3.0 s respectively).
There are no statement disputes, dependency repairs, or new DAG nodes.

## Second reading by Q13

A separate reading pass of the node and finished file checked every hypothesis
and conclusion against the mapping above. The pullback projection defining
scalars and the first projection defining coordinate germs were checked in the
file, so no arbitrary coefficient-field embedding or replacement chart is used.
The uniqueness conjunct ranges over every map with the truncation condition,
not just already bijective maps. The maximal ideal is that of the completion,
not merely its extended stalk ideal with locality assumed. The r=1 clause and
the n=0 clause are both present. Fin n and ULift (Fin n) have the same n
coordinates, and `truncTotal` uses total degree rather than coordinatewise
truncation. No mathematical mismatch was found; the first compilation's missing
closing parenthesis in ht was repaired before the clean compilation. This was
an in-thread rereading; no additional agent was started, as the brief requires.
