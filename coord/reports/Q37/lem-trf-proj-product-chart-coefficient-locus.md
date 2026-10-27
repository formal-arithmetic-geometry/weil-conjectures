## Worker report

Delivered module `Sheaf.AlgebraicGeometry.ProjProductChartCoefficientLocus`, with one
statement `AlgebraicGeometry.Proj.productChartCoefficientLocus`. Its proof is `sorry`.
There are no new definitions, new nodes, dependency repairs or statement changes.

Read the complete item, its two statement-dependency nodes, and the proof-dependency
leaf `lem-weil-pbc-proj-basic-open-intersection`. Read Stacks `constructions.tex`,
`lemma-principal-open` (Tag 01MV, lines 1918–1950) and
`lemma-standard-open-proj` (Tag 01MA, lines 1248–1266), including the coefficient
`b^n f/a^n` and the standard-open interpretation. No repair note exists for this item.
The original example CompactObject module is withdrawn; read its node's current
record and the actual upstream module `WeilConjectures.CategoryTheory.CompactObject`
for the module convention.

Hypotheses and clauses, in the same order as the node:

- `A : Type u`, `[CommRing A]`, `𝒜 : ℕ → σ`, `[SetLike σ A]`,
  `[AddSubgroupClass σ A]`, `[GradedRing 𝒜]` encode the arbitrary nonnegatively
  graded commutative ring. Both universes are declared explicitly. This is the
  general Mathlib grading interface, without a finite generation or nontriviality
  assumption. `Proj 𝒜` is precisely the scheme in `def-pc-proj`.
- `(d n α β : ℕ)`, `hd : 0 < d`, `hn : 0 < n`, `hα : α = β + d`
  encode all degree assumptions. `a b f : A`, `ha : a ∈ 𝒜 α`,
  `hb : b ∈ 𝒜 β`, `hf : f ∈ 𝒜 (n * d)` encode each homogeneity condition.
- The abbreviations h, k, V, R, R₀ are expanded as `a * b`, `α + β`,
  `basicOpen 𝒜 (a * b)`, `Localization.Away (a * b)`, and
  `HomogeneousLocalization.Away 𝒜 (a * b)`. The initial conclusion `0 < α + β`
  records positivity of k as a consequence, not an extra assumption. Mathlib's
  `basicOpenIsoSpec` identifies this V with Spec R₀; `basicOpenIsoAway` identifies
  R₀ with its functions. The statement uses their canonical ring map
  `awayToSection`, rather than an arbitrary chart identification.
- The two `IsUnit (algebraMap A (Localization.Away (a * b)) ...)` conjuncts
  state that a and b are units in R.
- `∃ c u w : HomogeneousLocalization.Away 𝒜 (a * b)` states membership of the
  coefficient, the specified unit, and its specified inverse in R₀. The next
  three equalities fix their images in R respectively as `b^n*f*a^(-n)`,
  `b^(2*n*α)*a^(-2*n*β)`, and `a^(2*n*β)*b^(-2*n*α)`.
  These formulas use Mathlib `Ring.inverse` on the images of a and b, which the
  preceding conjuncts assert to be units. Thus this is division by the units
  in the node, without adding a field or assuming nonzero-divisors.
  `HomogeneousLocalization.val` is injective, so these existential witnesses are
  exactly the specified fractions; they introduce no arbitrary maps or objects.
- `IsUnit u ∧ u * w = 1` gives the unit and the stated inverse in R₀.
  Because R₀ is commutative this is the full inverse condition.
- `c ^ (α + β) = u * HomogeneousLocalization.Away.isLocalizationElem
  (SetLike.mul_mem_graded ha hb) hf` is the power identity in R₀.
  The existing `isLocalizationElem` is exactly `f^(α+β)/(a*b)^(n*d)`;
  its degree proofs use ha, hb and hf. There is no replacement fraction definition.
- For every `x : basicOpen 𝒜 (a * b)`, the first equivalence identifies the
  unit status of the two germs, using `(Proj 𝒜).presheaf.germ` applied to their
  `awayToSection` images. The second equivalence identifies the unit status
  of the germ of c with `(x : Proj 𝒜) ∈ basicOpen 𝒜 f`; together they give all
  the node's equivalent conditions. The stalks of V and of Proj at x are
  canonically identified by open restriction, so the ambient Proj germ map is
  the germ of precisely the regular function on V in the node.
- The final equality of opens is `(Proj 𝒜).basicOpen (awayToSection ... c) =
  basicOpen 𝒜 (a * b) ⊓ basicOpen 𝒜 f`. `Scheme.basicOpen` is by definition the
  unit locus of the germ of its section; this is D_V(c) as an open of Proj.
  No side condition excludes an empty chart, zero f or nilpotent f.

Dependency declarations read and used:

- `def-pc-proj`: Mathlib matches `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.projIsoSpec`, `ProjectiveSpectrum.basicOpen`, from
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and its dependencies.
  The direct import `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` exposes
  these and the modern `Proj.basicOpen`, `Proj.basicOpenIsoSpec`, and
  `Proj.basicOpenIsoAway` interfaces (read full signatures and docstrings).
- `def-nagata-homogeneous-localization-degree-zero`:
  `HomogeneousLocalization.Away` in
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization` (publicly imported
  transitively). Read `NumDenSameDeg`, `HomogeneousLocalization`, `val`,
  `val_injective`, `Away`, `Away.mk`, and `Away.isLocalizationElem` with their
  docstrings. Away is exactly the node's degree-zero subring, even when h is
  nilpotent; `val` is its embedding into the ordinary localization.
- The proof dependency `lem-weil-pbc-proj-basic-open-intersection` is a Mathlib
  leaf. Read `Proj.awayι_preimage_basicOpen` with its full local variable context,
  and `opensRange_awayι`, `basicOpen_mul`, and `Scheme.mem_basicOpen`. Its module
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` is already public-imported
  because the statement uses `Proj.awayToSection` and `Proj.basicOpen` from it.
  No separate proof-only project import is necessary.

Edge checks before writing: β=0 is allowed, and then k=d>0 with no division by a
positive-degree b. For zero a or b, or nilpotent ab, R is the zero localization
and V is empty: zero is a unit in the zero ring, all fraction identities remain
valid, and the quantified point assertions are vacuous. For zero or nilpotent f,
D₊(f) is empty and the coefficient is nilpotent, so its unit locus is empty as
well. No `Nontrivial`, reducedness, domain, nonzero homogeneous element, or
nonempty-chart assumption was imposed. In arbitrary rings with zero-divisors,
a and b become units after localizing at ab, so all inverses used are valid.

Searches actually run (2026-10-24), all via the prescribed msearch wrapper where
applicable:

- LeanFinder: `For homogeneous a and b with degrees alpha=beta+d, the coefficient
  b^n*f/a^n on D_+(ab) has unit locus D_+(ab) intersect D_+(f)`. Eight hits,
  including `sectionInBasicOpen`, `NumDenSameDeg`, `Away.mk`,
  `awayMap_mk`, and `ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_mem_mul`.
  They construct fractions or give chart components, not this coefficient,
  unit-power identity, and complete locus statement.
- Loogle: `HomogeneousLocalization.Away, ProjectiveSpectrum.basicOpen`.
  Twelve hits, including `projIsoSpec`, `ProjectiveSpectrum.Proj.awayToΓ`,
  and `ProjIsoSpecTopComponent.toSpec`. None is the complete theorem.
- msearch grep: `coefficient.*[Ll]ocus|[Uu]nit.*basicOpen|basicOpen.*[Uu]nit`.
  Twenty-five hits, including `Scheme.mem_basicOpen` and
  `RingedSpace.isUnit_res_basicOpen`; these give general unit-locus components.
- LeanSearch: `In Proj the degree zero coefficient b^n*f/a^n on D_+(ab) has
  unit locus D_+(ab) intersect D_+(f)`. Eight hits, including
  `Proj.awayι_preimage_basicOpen`, `Proj.basicOpenIsoAway`, `Proj.basicOpen_pow`.
  Reused the chart interfaces; no complete coefficient theorem exists there.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `productChart|product_chart|coefficient.*[Ll]ocus`, plus the precise proposed
  declaration names in those roots and `dag/lean_names_upstream.json`.
  No match for this statement or proposed name; unrelated coefficient loci
  belonged to other topics. A narrower ProjectiveSpectrum/Proj-file coefficient
  search likewise found no existing theorem with this content.

No statement dispute or source fault found. The module docstring contains the
complete five-step proof plan of the node, and every theorem proof remains sorry.
The prescribed scompile.py checked this file successfully both in its sandbox
and at the actual module name; no errors or non-sorry warnings were reported.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
