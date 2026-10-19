## Worker report

The module `Sheaf.Paper.OpenComplementUnconditional` states the general theorem and its
finite-coefficient, nonempty-chart, and empty-chart specializations. All four theorem proofs
are `sorry`. It introduces no definitions, axioms, alternative coefficient rings, or alternate
sheaf/derived-category encodings. The node's statement and dependencies are unchanged.

Hypotheses and conclusions of the general assertion correspond as follows:

| Node text | Lean rendering |
| --- | --- |
| separably closed field k | `(k : Type u) [Field k] [IsSepClosed k]` |
| T a k-scheme | `[T.Over (Spec (.of k))]` |
| T finite type over k | `LocallyOfFiniteType (T ↘ Spec (.of k))` and `QuasiCompact (T ↘ Spec (.of k))` |
| d a nonnegative integer | `(d : ℕ)` |
| dim T at most d | `hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞)` |
| specified quasi-compact open immersion V into T | `(j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]` |
| finite commutative coefficient ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| prime ell different from char k | `(ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)` |
| some prime power annihilates A | `hkill : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0` |
| both open-complement clauses with c=2d | `HasOpenComplementCondition A j (2 * d)` |
| all sheaves M, not only constructible ones; all q>2d | the first conjunct of the imported predicate quantifies over every `Sheaf V.smallEtaleTopology (ModuleCat A)` and every `q : ℤ` above the bound |
| all constructible F, in every integer degree | the second conjunct uses `IsConstructibleEtaleModuleSheaf`, quantifying over all `q : ℤ`, including negative q |
| same bound for every such A | A, its ring/finite instances, ell and annihilating power are universally quantified after fixing T, d and j; the conclusion's bound contains none of them |

For a unital ring, annihilating 1 is equivalent to annihilating every element: multiply by
an arbitrary element. Requiring a positive exponent excludes no ring, including the zero
ring: if exponent zero kills the ring, the ring is zero and exponent one also kills it.
The coefficient universe is exactly that of the published open-complement predicate.
No separatedness, properness or algebraic closedness replaces the main hypotheses.

`hasOpenComplementCondition_finiteStage` uses the actual published
`WeilConjectures.PurityFiniteSetting`, with its finite-field datum, coefficient closure,
finite subextension E, and positive level n. Its ring is `P.Coefficient`, the standard ULift
of `Padic.coefficientExtensionRing ... P.level`, not an arbitrary finite ring. The structure
P ranges over all E and all positive n. The bound `2 * d` does not use P or its level.
The existential `hA : Finite P.Coefficient` supplies the finite-ring proof required to form
the imported predicate; finiteness is concluded, never added as a hypothesis. The ring
instance passed explicitly is the published `P.coefficientCommRing`.

`hasOpenComplementCondition_affineChart` states the chart clause. Y is finite type over
`P.field.k`, B is an affine open (`hB : IsAffineOpen B`) and is nonempty (`[Nonempty B]`).
The natural number b with `hb : topologicalKrullDim B.toScheme = b` names dim B. This is
an exact dimension, not an upper bound: a finite-type nonempty affine base has a unique
such natural dimension. The coordinate type `ULift (Fin m)` gives the recorded
`AffineSpace` on m variables over B. The map i is a closed immersion into this actual
affine space. The complement is the existing `i.openComplement`, with inclusion
`i.openComplement.ι`; no arbitrary open subset or unconstrained substitute map is used.
The first conjunct is exactly `m + dim B ≤ m + dim Y`. The second asserts the condition
with `2 * (m + b)`, for the actual finite-stage ring. It also supplies the
`QuasiCompact i.openComplement.ι` proof needed to instantiate the predicate. This proof is
an output, justified by the Noetherian argument in node Step 6; it is not an extra assumption.

Each chart of the separated finite-type assembly has precisely these data. No use is made
of its preservation/admissibility conclusion, and thus its currently unstated theorem is
not needed to form this statement. Conversely the chart formulation loses no geometric
hypothesis: a closed subscheme of this affine ambient space is affine and finite type over
k; its composite with the projection to B and the open immersion into Y is separated finite
type. Such a single affine chart is an instance of the assembly (and the remaining opens of
Y may be covered separately). Hence the chartwise statement does not assume a stronger
abstract assembly or a missing exceptional-image construction.

`hasOpenComplementCondition_emptyChart` keeps an affine B with `[IsEmpty B]`, and concludes
that both `AffineSpace (ULift (Fin m)) B.toScheme` and its actual open complement are empty,
together with the open-complement condition at bound zero. It supplies quasi-compactness
and coefficient finiteness as outputs, as above. This implements the explicitly permitted
alternative of retaining empty chart bases. Discarding them requires no additional theorem.

The node's final sentence compares independent dimension-zero and curve computations. It
asserts no additional mathematical property beyond the condition already stated, and the
module docstring records their independence. Neither their proofs nor the admissibility
conclusion are assumed as hypotheses. The recorded dimension theorem is imported for the
historical comparison, not used to obtain the separably closed result.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.OpenComplementCondition`:
  `AlgebraicGeometry.Scheme.HasOpenComplementCondition`. Its full definition contains both
  clauses, with the canonical `Etale.rightDerivedLowerStarPlus`, degree-zero insertion,
  and `DerivedCategory.Plus.homologyFunctor`.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Coefficient`,
  `.coefficientCommRing`, with its real published quotient construction and positive level.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and `.CoefficientDatum`,
  imported through the purity setting; k is the specified algebraic closure.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`. Its sheaf clause is the
  imported `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, used inside the condition.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `.rightDerivedLowerStarPlus`, through the predicate.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded set-valued predicates and
  `CategoryTheory.Sheaf.IsTorsion`; read in the shared framework checkout. Module-sheaf
  statements retain the established `Sheaf ... (ModuleCat ...)` convention.
- `Mathlib.CategoryTheory.Sites.Point.Basic`:
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, and
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`. Stalks occur only
  inside the recorded sheaf definitions/proof plan, so none is duplicated here.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, taking values in `WithBot ℕ∞`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, instantiated
  on `ULift (Fin m)`, and its canonical projection.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.Scheme.Hom.openComplement` (complement of the range), for the chart data.
- Proof imports include every currently recorded module of proof dependencies: direct-image
  finiteness input and its theorem; negative derived-functor vanishing; module-sheaf
  Grothendieck abelianness; the published relative torsion direct-image dimension theorem;
  finite-type dimension; coefficient-stage finiteness; and the Mathlib polynomial-dimension,
  finite-type, Noetherian-spectrum and subspace-dimension declarations. The generic torsion
  dimension module was missing in the older checkout: read its current full source using
  `scompile.py --source WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion`.

The dependency nodes `thm-pur-general-admissibility`, `lem-exc-open-complement-known`, and
`thm-exc-curve-open-constructible-general` have no recorded Lean statement in the read DAG.
They are context/comparison references, not missing objects needed to type any signature.
No declaration from them is silently replaced. Their complete natural-language statements
were read. In particular there is no downstream dependency on admissibility.

Edge cases checked: empty T or V; d=0; the zero coefficient ring; annihilating exponent
zero (equivalent positive exponent above); every negative degree in the constructibility
clause; arbitrary nonconstructible M; characteristic zero and positive characteristic;
n=1 and all larger n; m=0 (empty coordinate type, affine zero-space); nonempty B of
dimension zero; and empty B handled separately with c=0. No witness of nonemptiness is
required in the main theorem or finite-stage theorem. There are no implicit universe
variables or file-local instances/notation.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`, query: “A quasi-compact open immersion into a finite type
  scheme over a separably closed field has constructible higher direct images and
  cohomological dimension at most twice the dimension”. Eight hits concerned constructible
  images of subsets, quasi-finiteness and quasi-compactness; no theorem of the two required
  sheaf clauses.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsOpenImmersion, CategoryTheory.Functor.rightDerived`: zero hits.
- `msearch.py ... grep`, query:
  `HasOpenComplementCondition|higherDirectImage.*constructible|openComplementCondition`:
  zero Mathlib hits.
- `msearch.py ... leansearch`, query: “Higher direct images for a quasi compact open
  immersion of finite type schemes over a separably closed field preserve constructibility
  and vanish above twice dimension”: service unavailable, Internal Server Error.
- `rg` of the upstream `WeilConjectures` source and shared `lean/Sheaf` for
  `HasOpenComplementCondition|open-complement|OpenComplement` found the recorded definition,
  unrelated open-complement constructions and curve lemmas, not this complete statement.
- `rg` for the item id in upstream `WeilConjectures` and `dag/lean_names_upstream.json`
  found no declaration. The prospective full names were also searched before writing.

No statement correction, new node or dependency repair is needed. No STATEMENT-DISPUTED
issue was found. The finite-instance and chart quasi-compactness witnesses are explicit
outputs because Lean cannot infer them directly from the original data without the
geometric/finite-coefficient arguments that stage 3 will prove.

Validation: the first scompile run diagnosed only missing inferred quasi-compactness proofs
for the chart complements. These were repaired by concluding the required proofs rather
than adding hypotheses. The final `scompile.py Q30 thm-pur-open-complement-unconditional` run compiled both the
sandbox module and its library module without errors or warnings (13.7 s and 6.8 s).
The required `deliver2.py ... --no-push` checks the final delivery; nothing is pushed by
the worker.

## Second reading by Q30

I read the DAG statement, all eight proof steps, every statement-dependency node and
the four declarations in `OpenComplementUnconditional.lean`. The blueprint Markdown
and Stacks checkout are absent from this machine's read-only clone, so I read the
actual source on the server over SSH, under `/home/ubuntu/weil-newtargets/literature/`.
The blueprint is the stated node, order 2080. The current DAG already spells out d,
the finite-type chart setting and the empty-chart convention; this delivery does not
correct the DAG statement. I also read the relevant Stacks `.tex` definitions: Tags
01T0, 0055, 01HE, 01IO, 03RU and 095E. Their ambient assumptions require no additional
hypothesis here: the schemes are finite type over a field and the coefficient ring is
finite, hence Noetherian. In particular, the global finite-stratification description
in 095E applies to these quasi-compact, quasi-separated schemes.

The object/hypothesis/conclusion inventory and item-by-item verdict are:

| Node object or clause | Lean rendering checked | Verdict |
| --- | --- | --- |
| Arbitrary separably closed field k | `k : Type u`, `[Field k]`, `[IsSepClosed k]` | Exact; not algebraically closed or restricted to finite-field closures. |
| Finite-type k-scheme T | `T : Scheme.{u}`, `[T.Over (Spec (.of k))]`, `LocallyOfFiniteType` and `QuasiCompact` on its structure map | Exact finite type as defined in 01T0; no separatedness assumption. |
| Nonnegative integer d with dim T at most d | `d : ℕ`, `hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞)` | Exact upper bound; not an exact-dimension or nonempty assumption. |
| Specified quasi-compact open immersion j from V to T | `j : V ⟶ T`, `[IsOpenImmersion j]`, `[QuasiCompact j]` | Exact; V inherits its k-structure by composition and is not separately constrained. |
| Finite commutative coefficient ring A | `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` | Exact published coefficient convention, including the zero ring. |
| Prime ell different from the field characteristic | `ℓ : ℕ`, `hprime : ℓ.Prime`, `hchar : ℓ ≠ ringChar k` | Exact for fields; no characteristic is excluded. |
| A annihilated by a power of ell | `hkill : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0` | Equivalent: killing 1 kills the whole ring. A zero exponent can only kill the zero ring, which also admits exponent one. |
| Vanishing for every module sheaf M and integer q greater than 2d | First conjunct of `HasOpenComplementCondition A j (2 * d)` | Exact: opened the definition and checked the universal quantifiers, `IsZero`, degree-zero insertion, canonical bounded-below direct image and homology. M is not assumed constructible or finite. |
| Constructibility for every constructible F in every integer degree | Second conjunct of the same predicate | Exact: `IsConstructibleEtaleModuleSheaf`, with `q : ℤ` unrestricted, uses the dependency's finite constant module values on a finite locally closed stratification. |
| Bound uniform in all such coefficient rings | A and ell are quantified after T, d and j; conclusion uses `2 * d` | Exact simultaneous assertion; no coefficient-dependent choice of d. |
| Every actual finite coefficient stage with n at least one | `hasOpenComplementCondition_finiteStage (P : PurityFiniteSetting.{u})` | Exact: opened P, `P.Ring`, `P.Coefficient` and `coefficientCommRing`; the data include a finite subextension of the fixed closure and `level_pos : 1 ≤ level`. No ramification-divisibility assumption is introduced. |
| Same bound 2d at all stages | Finite-stage conclusion existentially supplies `Finite P.Coefficient`, then asserts the condition at `2 * d` | Exact quotient coefficients, with finiteness concluded rather than assumed. |
| Nonempty affine chart base B in finite-type Y | `B : Y.Opens`, `hB : IsAffineOpen B`, `[Nonempty B]`, the finite-type structure map of Y | Exact scope of the retained nonempty charts. |
| Affine ambient space and its actual closed-chart complement | `i : Z ⟶ AffineSpace (ULift.{u} (Fin m)) B.toScheme`, `[IsClosedImmersion i]`, `i.openComplement.ι` | Exact canonical complement of the closed image; not an arbitrary map or open. Every assembly chart has these data. Conversely such a Z is affine and its composite to Y is separated finite type, so no additional geometric case is asserted. |
| Chart dimension inequality | `hb : topologicalKrullDim B.toScheme = (b : WithBot ℕ∞)` and conclusion `(m + b : ℕ) ≤ m + topologicalKrullDim Y`, with casts | Exact inequality after naming the unique natural dimension of a nonempty finite-type affine B. |
| Chart condition at 2(m + dim B), independently of n | `hasOpenComplementCondition_affineChart` concludes the predicate at `2 * (m + b)` for every P | Exact. Quasi-compactness of the complement and coefficient finiteness are existential outputs, not extra hypotheses. |
| Empty bases may be retained with bound zero; ambient and complement empty | `hasOpenComplementCondition_emptyChart`, `[IsEmpty B]`, conclusion contains both `IsEmpty` assertions and the condition at `0` | Exact permitted alternative; no natural dimension is assigned to an empty base. |
| Independent dimension-zero/curve computations are comparison references | Module docstring and final theorem docstring record their independence | No further mathematical conjunct is required. No admissibility or low-dimensional theorem is assumed in any of the four signatures. |

I opened the dependency modules themselves, not just their records. In particular:
`OpenComplementCondition` uses the canonical `Etale.rightDerivedLowerStarPlus` and
the project's `IsConstructibleEtaleModuleSheaf`; `BoundedConstructibleComplexes`
uses that same sheaf predicate. I read `Etale.lowerStar` and its additive/left-exact
instances in the upstream source, the finite-field and coefficient structures in
`FiniteFieldFiber`/`PurityFiniteSetting`, Mathlib's affine-space fibre product and
projection, the upstream `Scheme.Hom.openComplement` definition, and the Mathlib
finite-type, open-immersion, separably-closed, dimension and geometric-stalk
declarations. The generic torsion direct-image theorem was read in its full current
server source using `scompile.py --source`; its signature has the required generality.
The context-only admissibility and low-dimensional nodes have no missing object needed
by these signatures. No new definition node or dependency module is required.

Edge cases: empty T or V are allowed by the main and finite-stage statements;
`topologicalKrullDim` takes value bottom on the empty space. d=0 gives bound zero.
The zero ring and every positive prime-power exponent are covered. Negative q are
included in constructibility, and nonconstructible M in vanishing. Characteristic
zero and every positive characteristic with ell different from it are included.
`P.level_pos` includes n=1 and every larger level. m=0 uses the empty coordinate
type and the canonical affine zero-space; b=0 is allowed for nonempty B. Empty B
is covered separately with bound zero. There is no indexed-family nonemptiness
assumption or hidden positive-dimension restriction. The explicit universe u is
arbitrary; the coefficient/module universe u+1 is the recorded small-etale convention,
not an equality imposed on independently varying site universes.

Independent duplicate searches, using different wording from the first worker:

- LeanFinder: “Higher direct images of finite locally constant etale modules under an
  open embedding are constructible with uniform finite cohomological dimension”. Eight
  hits concerned condensed locally constant modules and sheaf constructors; none states
  this theorem.
- Loogle: `AlgebraicGeometry.Scheme, IsSepClosed, CategoryTheory.Limits.IsZero`:
  zero hits.
- Mathlib grep through msearch: `rightDerivedLowerStarPlus.*constructible|two_mul.*open|cohomologicalDimension.*immersion`:
  zero hits.
- LeanSearch: “The etale direct image of a constructible sheaf along an open immersion
  into a finite type scheme over a separably closed field is constructible in each
  derived degree”: unavailable, Internal Server Error (recorded as unavailable).
- Direct `rg` on upstream `WeilConjectures/` and shared `lean/Sheaf/` for
  `open.complement`, `HasOpenComplementCondition`, open-immersion/constructibility
  combinations, the blueprint id and all four prospective theorem names. I inspected
  the relevant hits: they are the canonical predicate, general vanishing tools,
  low-dimensional results or hypotheses in exceptional-image stability, not an
  existing statement of both uniform clauses. The upstream name index also has no
  declaration for this item.

Mismatches found: none. I preserved the Lean and node record, and added only this
independent reading and its search/validation evidence. There are exactly four
theorems, each proved by `sorry`, and no new definitions, local instances, axioms,
private constructions or file-local notation. All declaration docstrings identify
the source and blueprint node and carry their respective proof steps; together they
cover all eight DAG steps. No line exceeds 100 characters. `autoImplicit false` and
the explicit `universe u` leave no unbound binder. The node's `lean.statement` was
compared byte-for-byte with the main signature and matches verbatim.

Validation: second-reader `scompile.py` compiled the sandbox file and the library
module cleanly (21.2 s and 18.3 s respectively), with no errors or warnings. The
required delivery dry run and final delivery are run after this report is complete.
