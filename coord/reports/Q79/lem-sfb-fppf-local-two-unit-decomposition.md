## Worker report

The module `Sheaf.AlgebraicGeometry.FppfLocalTwoUnitDecomposition` states
`AlgebraicGeometry.Scheme.exists_fppf_two_unit_decomposition`. Its only theorem
has proof `sorry`, as required in stage 2. It introduces no definitions, helper
statements, new nodes, or dependency repairs. The item's node copy changes only
its `lean` field. All variables and the universe are explicitly bound.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| An arbitrary scheme T | `(T : Scheme.{u})` |
| Arbitrary global sections u and v of its structure sheaf | `(u v : Γ(T, ⊤))` |
| There exists an indexed family of schemes over T | `∃ (I : Type u) (Ti : I → Scheme.{u}) (f : ∀ i, Ti i ⟶ T)` |
| The family is an fppf covering | `Presieve.ofArrows Ti f ∈ fppfPrecoverage T` |
| Sections a_i and b_i on each member | `∃ (a b : ∀ i, Γ(Ti i, ⊤))` |
| Every pullback of u equals a_i+b_i | `∀ i, (f i).appTop u = a i + b i ∧ ...` |
| Each a_i is a unit | `IsUnit (a i)` |
| Each b_i is a unit | `IsUnit (b i)` |
| Each 1+b_i f_i^*v is a unit | `IsUnit (1 + b i * (f i).appTop v)` |
| No invertibility assumption on u, v, or 1+uv | The only input binders are T, u, and v; there is no `IsUnit` hypothesis. |

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`. The scheme is a locally ringed space with
  local affine charts. `Scheme.Hom.appTop` in that same module is the canonical
  ring homomorphism on global sections, exactly the two pullbacks in the result.
- `def-pc-fppf-site`: `AlgebraicGeometry.Scheme.fppfPrecoverage` and
  `fppfTopology`, from `Mathlib.AlgebraicGeometry.Sites.Fpqc`. The definition of
  the precoverage is `precoverage (@Flat ⊓ @LocallyOfFinitePresentation)`.
  `Scheme.ofArrows_mem_precoverage_iff`, read in
  `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`, identifies membership with
  joint surjectivity and both morphism properties for every member. Thus this
  uses the recorded covering notion directly, without replacing it by arbitrary
  covering sieves in the generated topology. No slice topology is needed for
  this covering of T itself.

The proof-dependency imports are retained without `public`, as required by
stages/2-statements.md, rule 7. They supply `AffineSpace`, `Scheme.basicOpen`
(already public through Scheme), `RingedSpace.isUnit_res_basicOpen`,
`IsOpenImmersion`, smooth composition, `AffineSpace.smoothOfRelativeDimension_over`,
`smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`,
`Spec`, `Scheme.residueField`, and the polynomial-domain instance. The two
upstream modules are
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`; the remaining
imports are the Mathlib modules recorded by the corresponding nodes. The
statement docstring reproduces all four proof steps and their dependency ids.

Edge cases checked before writing:

- Empty T is included. There is no `Nonempty` or `Nontrivial` hypothesis.
  Its zero ring of global sections is permitted, and joint surjectivity onto
  its empty space is vacuous. The empty covering is not excluded either.
- u=0, v=0, and 1+uv=0 are all allowed. For example, v=0 makes the third
  unit condition the unit 1; u=0 asks for two opposite units, which is valid
  after the stated covering, including in characteristic two.
- A finite residue field need not contain a rational value avoiding all three
  roots. The node's prime-kernel argument uses the generic point of the affine
  line over the residue field and proves that the principal open has a point
  over the original base point. Hence no infinite-field hypothesis appears.
- There is no affineness, quasi-compactness, reducedness, base-field, or
  characteristic hypothesis. The construction uses the relative affine line
  and works over arbitrary schemes. The universe u is arbitrary. Taking
  `I : Type u` includes a lifted singleton, which the proof explicitly supplies,
  and all covering members have the same scheme universe as T.

Source inspected: Conrad, *Reductive group schemes*, printed p.129, after
(4.3.1), https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf (PDF page
index 128). The paper uses the decomposition in a context where 1+uv is a
unit. The accepted node explicitly gives the stronger arbitrary-section
avoidance lemma with its own open-polynomial proof. Inspection of that proof
shows that the omitted unit assumption is not needed for this lemma. The Lean
follows the node unchanged; no statement correction or dispute is needed.

Searches actually run in this session:

- msearch LeanFinder: `For any scheme and global sections u v there is an fppf
  cover on which u is a sum of units a b and 1+b*v is a unit`. Eight hits,
  concerning structure-sheaf fraction normalization, affine covers, local
  morphism properties, and restriction to basic opens. None states this result.
- msearch Loogle: `"IsUnit", "add"`. Twelve hits including
  `IsLocalRing.isUnit_or_isUnit_of_add_one`, nilpotent-unit formulas, and
  `Polynomial.not_isUnit_X_add_C`. These do not assert existence of an fppf
  covering with the three simultaneous unit conditions.
- msearch grep in AlgebraicGeometry:
  `two.units|sum.*units|exists.*[Ii]sUnit`. Two hits: the function-field germ
  unit lemma and an elliptic-curve unit coefficient calculation; neither is a
  match.
- msearch LeanSearch: `Given arbitrary functions u v on a scheme, fppf locally
  u equals a+b with a b and 1+b*v invertible`. Eight hits on basic-open addition,
  structure-sheaf sums, quasi-separated cancellation, and unrelated categories;
  none gives the simultaneous avoidance result.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for fppf/unit and two-unit
  terminology found existing fppf sites and other unit statements, but no
  decomposition statement. A literal grep for the item id in
  `lean/WeilConjectures` returned no matches. Direct rg of Mathlib, both project
  roots and `dag/lean_names_upstream.json` for
  `fppfLocalTwoUnitDecomposition|exists_fppf_two_unit_decomposition` returned no
  existing declaration. The found fppf precoverage API is reused, rather than
  defined again.

Validation: the prescribed scompile.py compiled the module both under its
sandbox name and its intended library name, with no errors or unexpected
warnings (approximately two seconds for each). No local or global build was
run. The dry run and final delivery are performed with deliver2.py.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
