## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralUnitsFiniteValuationMap` states
`AlgebraicGeometry.Scheme.exists_integral_units_finite_valuation_map` with `sorry`.
No definition, hypothesis, statement correction, or extra node is needed. The
module and theorem docstrings cite Stacks Tags 04L5 and 04L4, read in
`literature/stacks-project/varieties.tex`, lines 5157–5283. The theorem docstring
records all nine proof steps of the accepted node, including the injective generic
germ, projective closure, normalization, finite chart-prime boundary index set,
valuation unit criterion, gluing, and proper connected global-sections argument.

Hypothesis and clause correspondence:

- The arbitrary algebraically closed field is `(K : Type u) [Field K]
  [IsAlgClosed K]`; both characteristic zero and positive characteristic are allowed.
- The integral scheme is `(T : Scheme.{u}) [IsIntegral T]`. Mathlib's integral
  scheme class includes nonemptiness and the integral-domain section-ring condition.
- Being over K is the specified structure morphism
  `(f : T ⟶ Spec (CommRingCat.of K))`; locally finite type is
  `[LocallyOfFiniteType f]`. There is no separatedness, quasi-compactness, normality,
  smoothness, affine, or finite-type assumption on T.
- B is literally `Γ(T, ⊤)`; its multiplicative group is `Γ(T, ⊤)ˣ`.
- A finite set J is represented by `Fin n`, with existentially quantified `n : ℕ`.
  Every finite set can be reindexed by such a set, and `n = 0` is allowed. This is
  an existence statement, not a fixed identification of the geometric valuations.
- The map is `v : Γ(T, ⊤)ˣ → (Fin n → ℤ)`. The codomain is the ordinary function
  additive group, not a direct-sum subgroup, a power quotient, or a valuation ring.
- Additivity on products is exactly
  `∀ a b : Γ(T, ⊤)ˣ, v (a * b) = v a + v b`.
- Kernel equality is stated pointwise by `∀ a, v a = 0 ↔ ∃ c : Kˣ, ... c = a`.
  Zero here is the zero function. The scalar-unit map in the right-hand side is
  `Units.map (((ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toMonoidHom)`.
  Thus it uses the actual structure morphism: identify K with the global sections
  of Spec K and pull back along f, then apply the canonical map on units. Both
  inclusions of the kernel equality are present. No arbitrary scalar map is supplied.

Statement dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`, lines 170–180;
  supplied through the public imports.
- `def-weil-algebraic-closure`: the `IsAlgClosed` part of its recorded Mathlib
  match, in `Mathlib.FieldTheory.IsAlgClosed.Basic`, lines 59–64. No algebraic
  extension of a second field is called for by this node.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, in
  `Mathlib.AlgebraicGeometry.Properties`, lines 238–245. Its full signature and
  docstring were read, including the nonempty-open section-ring condition.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 39–47. The node calls
  for this part of the dependency, not its separate quasi-compactness notion.
- Canonical existing interfaces: `Scheme.ΓSpecIso` in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 600–602, and `Units.map` in
  `Mathlib.Algebra.Group.Units.Hom`, line 75. No private versions are defined.

The recorded stated proof dependencies are imported without `public`, including
Mathlib's function-field, finite/proper morphism, quasi-compact cover, integral
closure, Noetherian-space and stalk interfaces, the upstream affine-space and
normalization modules, and the project's Nagata projective closure, reduced image,
and proper reduced global-sections modules. Three proof-only dependencies have
neither a recorded module nor a Mathlib match in the read clone:
`lem-sfb-finite-normalization-model-functoriality`,
`lem-trf-normalization-affine-stalk-closure`, and
`lem-trf-normal-domain-principal-divisor-kernel`. They are retained in the proof
plan and theorem docstring; their modules can be imported when they are stated.
They introduce no notion used in this theorem's type.

Edge cases checked mathematically before writing:

- The empty scheme is excluded by integrality, exactly as in the node.
- `T = Spec K`, integral proper T, and a zero-dimensional integral T allow `n = 0`:
  all global units are constants, so the unique map to the empty product works.
- For the multiplicative group, exponent of its coordinate gives a nontrivial
  integer coordinate, so the conclusion does not accidentally force all units to
  be constants.
- Singular integral schemes, nonseparated integral schemes (e.g. a doubled-origin
  line), and non-quasi-compact integral schemes remain admissible. Their global
  sections inject into a single nonempty affine chart by generic germs.
- Arbitrary finite index sets need no independent universe: every such set admits
  a bijection with `Fin n`. K and T have the standard common scheme universe;
  there is no quantification over test objects in a smaller universe.

Searches actually run (also recorded by the launcher in `searches.jsonl`):

- `msearch.py ... leanfinder "An integral scheme locally of finite type over an
  algebraically closed field has a map from global units to a finite product of
  integers with kernel the scalar units"`: 8 hits, including
  `finite_appTop_of_universallyClosed`, `isField_of_universallyClosed`,
  `Scheme.ker_toSpecΓ`, and Dedekind Selmer-group lemmas. None is this statement.
- `msearch.py ... leanfinder "Global units of integral schemes finite integer
  valuation map kernel constant functions"`: 8 hits, including `Set.coe_unit`,
  `selmerGroup.valuation_ker_eq`, `Set.unit_valuation_eq_one`, and the function-field
  instance. They concern Dedekind-domain S-units or power quotients, not this map.
- `msearch.py ... loogle "Units.map, AlgebraicGeometry.Scheme.ΓSpecIso,
  AlgebraicGeometry.LocallyOfFiniteType"`: successful response, zero hits.
- `msearch.py ... grep "Rosenlicht|units.*[Ff]inite|[Ff]inite.*[Uu]nits"`:
  25 hits, chiefly number-field units, finite fields, and valued local fields;
  no matching theorem on units of arbitrary integral locally finite type schemes.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item ID and units,
  valuation, quotient and finiteness patterns: curve-unit quotient results and
  `RelativelyClosedConstantsUnitsFG` were found. The former assume curve/affine/
  smooth hypotheses and conclude a power-quotient finiteness theorem; the latter
  is a consumer of this item and states a different quotient finite-generation
  result. Neither gives this statement. Its scalar map confirms the same existing
  canonical ΓSpecIso/appTop/Units.map interface used here.
- Exact declaration-name search in both source roots and
  `dag/lean_names_upstream.json`: no existing
  `exists_integral_units_finite_valuation_map` declaration.

No statement dispute or node fault was found. The source's statement explicitly
allows an integral scheme merely locally of finite type. Its proof supplies the
finite valuation map used by this node.

## Second reading by Q151

I reread the node and the completed signature clause by clause; no other agent
was started, as instructed. The maintainer's independent review remains separate.
Field, algebraic closedness, integral scheme, specified base morphism and local
finite type all have explicit binders. The quantified function has exactly the
unit domain and finite integer-function codomain. Its multiplication/addition
identity is explicit, and the kernel biconditional identifies exactly the image
of scalar units via the specified morphism. `Fin 0` is admitted. The signature
adds no compactness, separation, normality, affineness, or smoothness condition.
The only theorem has a whole-proof `sorry`; no definition contains postponed data.
No mismatch was found and no statement change was made.
