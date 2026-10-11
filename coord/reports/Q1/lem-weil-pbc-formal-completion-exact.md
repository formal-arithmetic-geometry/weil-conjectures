## Worker report

The module `Sheaf.AlgebraicGeometry.FormalCompletionExact` states
`AlgebraicGeometry.formalCompletion_exact`, with its sole proof `sorry`. It uses the actual
completion functor already defined by the dependency, without defining any new notion.
The node is unchanged except for `lean`. No disputed statement or dependency fault was found.

Hypothesis and clause correspondence:

- A scheme X is `X : Scheme.{u}`, with explicit universe `u`.
- Locally Noetherian plus quasi-compact is `[IsNoetherian X]`: Mathlib's class extends
  `IsLocallyNoetherian X` and `CompactSpace X`, exactly the stated Noetherian condition.
- A quasi-coherent ideal subsheaf is `I : X.IdealSheafData`, the shared ideal representation.
- Coh(O_X) is `AlgebraicGeometry.CoherentModules X`, the full subcategory defined using
  `RingedSpace.IsCoherent X.toRingedSpace`.
- Coh(X,I) is `AlgebraicGeometry.CoherentFormalModule X I`, the dependency's category of
  coherent adic inverse systems with compatible maps.
- Abelianity of both categories is expressed by the first and second
  `Nonempty (Abelian ...)` conjuncts. These assert existence, without choosing an abelian
  structure from a sorried theorem. ShortExact itself only needs the existing zero morphisms.
- The specified functor is `AlgebraicGeometry.completion X I`. Its underlying objects are
  `formalCompletionSystem I F.obj`: at `op n` the quotient is by I^(n+1), so it uses all and
  only positive levels. Its maps are `formalCompletionMap I`, the induced reductions.
- Additivity is `∃ h : (AlgebraicGeometry.completion X I).Additive, ...`. This is a conclusion,
  not an added hypothesis. The witness h supplies the explicit
  `Functor.preservesZeroMorphisms_of_additive` instance required by ShortComplex.map.
- Every input short exact sequence is covered by
  `∀ S : ShortComplex (AlgebraicGeometry.CoherentModules X), S.ShortExact → ...`.
  ShortExact comprises exactness, monicity of the first map, and epicity of the second.
- Its canonical image is `ShortComplex.map S (AlgebraicGeometry.completion X I)` with the
  explicit zero-preservation instance; the conclusion is precisely its `.ShortExact`.
  This is the node's stated meaning of exact, equivalent to finite-limit and finite-colimit
  preservation by Homology 010N (4); no extra preservation clause is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `AlgebraicGeometry.IsNoetherian` combines this with compactness.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`, used
  through CoherentModules (finite type and finite-type kernels of maps from finite free modules).
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `AlgebraicGeometry.CoherentModules`,
  `AlgebraicGeometry.CoherentFormalModule`, and `AlgebraicGeometry.completion`. The quotient,
  quotient-map, adic-system, and functor definitions were read in full.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`:
  `AlgebraicGeometry.coherentFormalModule_abelian`, the recorded abelianity and termwise
  cokernel theorem. Its module imports the shared categories used by this statement.
- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Abelian.Subcategory`: the recorded full-subcategory abelian instance;
  its companion `ObjectProperty.preservesKernels_ι`, `preservesCokernels_ι`,
  `ShortComplex.ShortExact.map`, and `ShortComplex.exact_map_iff_of_faithful` were read.
  These explain proof step 1; they are not additional hypotheses or new definitions.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `CategoryTheory.ShortComplex.ShortExact`;
  `Mathlib.Algebra.Homology.ShortComplex.Basic`: `CategoryTheory.ShortComplex.map`.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `CategoryTheory.Functor.Additive`
  and `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`.

Edge cases checked before writing: the empty scheme is allowed (no nonemptiness binder),
zero coherent modules and zero maps are allowed, I=0 and I=O_X are allowed, and no properness,
separatedness or base ring assumption is imposed. The n=0 index is positive level 1, not a
spurious quotient at level zero. Exactness is in the formal category, not termwise exactness
of quotient sequences (which would be false in general). No universe or characteristic
restriction beyond the shared scheme/module conventions is added.

Searches made:

- `msearch.py ... leanfinder "The adic completion functor on coherent sheaves on a Noetherian
  scheme is additive and exact"`: 8 results, including `AdicCompletion.map_exact`, local
  cohomology and condensed-category abelianity; none states sheaf-level formal completion.
- `msearch.py ... loogle "Functor.Additive, ShortComplex.ShortExact, PreservesFiniteLimits"`:
  0 hits, with unknown-identifier diagnostic for Functor.Additive; not used as evidence.
- `msearch.py ... leansearch "exact additive completion functor coherent sheaves"`:
  UNAVAILABLE (Internal Server Error). Recorded as unavailable, with no verdict.
- `msearch.py ... grep "completion.*exact|CoherentFormal|formalCompletion"`: 6 results,
  all in the ring-theoretic AdicCompletion API, no sheaf completion theorem.
- `rg -n "formal.*completion|CoherentFormalModule|completion functor|completionExact"`
  over the source `WeilConjectures` and project `lean/Sheaf`: project completion definitions
  and related theorems, no existing exactness statement.
- Search for the literal node id in source `WeilConjectures`: no match.

The local literature tree does not contain the Stacks TeX, so the authoritative source was
read at https://stacks.math.columbia.edu/tag/0881 (Lemma 30.23.4): locality reduces to affine
finite modules and Algebra 00MB. This agrees with the node's six-step proof, included in the
new declaration's docstring.

Validation: `scompile.py Q1 lem-weil-pbc-formal-completion-exact` compiled the module on the
server in 1.8 seconds with exit code 0 and no warnings. The dry run follows; the independent
second-reading section is reserved for the second worker.

## Second reading by Q1

Independent statement reading against the node and Stacks Lemma 30.23.4 (tag 0881):

- The scheme object is rendered by `X : Scheme.{u}`; verdict: exact object, with an
  explicit universe that permits every scheme.
- The Noetherian hypothesis (locally Noetherian plus quasi-compact) is rendered by
  `[IsNoetherian X]`; verdict: exact Mathlib/project predicate and no stronger
  separatedness, properness, finiteness, or characteristic assumption.
- The quasi-coherent ideal sheaf is `I : X.IdealSheafData`; verdict: exact shared
  ideal-subsheaf notion.
- `Coh(O_X)` is `AlgebraicGeometry.CoherentModules X`; verdict: the recorded full
  coherent-module subcategory.
- `Coh(X,I)` is `AlgebraicGeometry.CoherentFormalModule X I`; verdict: the recorded
  full category of coherent inverse systems with the adic quotient conditions.
- Abelianity of the two categories is rendered by the first two conjuncts,
  `Nonempty (Abelian (CoherentModules X))` and
  `Nonempty (Abelian (CoherentFormalModule X I))`; verdict: existence exactly as
  stated, with no selected or extra structure in the hypotheses.
- The completion functor is exactly `AlgebraicGeometry.completion X I`; verdict:
  its dependency definition has object `F/I^(n+1)F` at `op n` and induced reduction
  maps, hence represents the source's levels `n >= 1` and map reductions.
- Additivity is the conclusion witness
  `∃ h : (completion X I).Additive, ...`; verdict: additive exactness is concluded,
  not assumed.
- The universal short exact input is
  `∀ S : ShortComplex (CoherentModules X), S.ShortExact → ...`; verdict: this
  quantifies precisely over all short exact sequences in the coherent category.
- The image is
  `ShortComplex.map S (completion X I)` with the explicit zero-preservation
  instance obtained from `h`; verdict: this is the canonical mapped sequence and
  introduces no extra preservation clause.
- The final `.ShortExact` is the node's short exact conclusion in the formal
  category; verdict: exactness is stated in the abelian-category sense encoded by
  the node (equivalent to the source's finite-limit/finite-colimit formulation).

The source check found no missing clause or stronger hypothesis. Edge cases checked:
empty schemes and zero modules/maps are admitted; `I = 0` and `I = O_X` are admitted;
level `op 0` is the positive quotient by `I^(0+1)`; no nonempty-index, base-field,
characteristic, or separatedness condition is present; universe `u` is shared by the
scheme and its module categories.

Existing-definition searches were repeated with `rg` over `WeilConjectures/` and
`lean/Sheaf/`, and with the project's `msearch.py` LeanSearch, LeanFinder/Loogle,
and grep queries for `formalCompletion`, `completion.*exact`, and
`CoherentFormalModule`. They found only the dependency completion construction and
ring-theoretic adic-completion APIs, with no sheaf-level exactness declaration. The
Stacks page at <https://stacks.math.columbia.edu/tag/0881> states that this functor is
exact and reduces to finite-module completion, agreeing with the node and proof
steps.

No mismatch was found, so no statement or module repair was needed. The module
compiled with `scompile.py`; its sole proof remains the permitted named theorem
`sorry`, and all declarations carry the source and `(blueprint:
lem-weil-pbc-formal-completion-exact)` documentation.
