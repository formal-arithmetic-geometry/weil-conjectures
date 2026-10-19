## Worker report

The module `Sheaf.GroupTheory.FsChartTorsionFactorization` states
`AlgebraicGeometry.fs_chart_torsion_factorization`, with its sole proof `sorry`.
It retains the current node's statement and all other fields unchanged, adding only `lean`.
No new notions, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The arbitrary additive commutative monoids are `(P : Type u) (Q : Type v)` with
  `[AddCommMonoid P] [AddCommMonoid Q]`, with independent, explicitly bound universes.
- The fs hypotheses are `hP` and `hQ`, using the dependency's existing
  `AlgebraicGeometry.IsFineSaturatedMonoid` on `Multiplicative P` and `Multiplicative Q`.
  The type tag changes additive notation to multiplicative notation without changing
  finite generation, integrality, or root saturation. It imposes neither sharpness
  nor torsion-freeness.
- `h : P →+ Q` is the chart homomorphism. Its group map is exactly
  `GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)`;
  `hinj` is its injectivity. Quotienting the completion of Q by this map's range is C.
- `hfinite : Finite (AddCommGroup.torsion (...))` is precisely the finiteness of C_tor.
  Mathlib's additive torsion subgroup consists of elements of finite additive order,
  equivalently those killed by a positive natural number.
- `∃ R : AddSubmonoid Q` together with its membership biconditional specifies exactly
  the root subset R. Its fs property uses the same existing predicate.
  Existential specification is part of the theorem, not a definition with missing data.
- `∃ H : AddSubgroup (GrothendieckAddGroup Q)` and its membership biconditional specify
  exactly H, with a positive natural multiple lying in the range of h^gp.
- `∃ e : GrothendieckAddGroup R ≃+ H` with the equation on every generator r identifies
  the completion with H by the ambient inclusion; the equation fixes the canonical map.
- `∃ a : P →+ R` and `R.subtype.comp a = h` give the factorization and the value
  a(p)=h(p). The map b is the actual inclusion `R.subtype`, rather than an arbitrary map.
- `Function.Injective a` is the injectivity in the stated Kummer condition. The next two
  injectivity clauses are exactly injectivity of the induced group maps a^gp and b^gp.
- The normalized additive equivalence from `H ⧸ (range h^gp).comap H.subtype` to
  `AddCommGroup.torsion C` is the canonical H/A = C_tor identification. The comap
  expresses A as a subgroup of H; the membership formula for H ensures A is contained in H.
  Its equation on every quotient generator says that it sends g+A to g+A in C.
- `IsAddTorsionFree (GrothendieckAddGroup Q ⧸ H)` gives the other torsion-free quotient.
- `∀ r : R, ∃ n : ℕ, 0 < n ∧ n • r ∈ Set.range a` is the positive-multiple
  clause, together with injectivity exactly the Kummer condition of ILO VI 2.1.
- The `Nat.card` equality is the claimed order of coker(a^gp). The positivity clause
  explicitly states that #C_tor is a positive integer; the final quantified equation
  states that this integer annihilates every element of coker(a^gp).

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` (def-trf-fs-log-blowup), which publicly
  imports `Sheaf.AlgebraicGeometry.LogRegularPair`, the owner of
  `AlgebraicGeometry.IsFineSaturatedMonoid`. Read its full definition: finite monoid
  generation, injectivity of the canonical completion map, and root closure in that
  completion. The broad dependency's log-scheme structures are unnecessary here.
- `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`:
  `Algebra.GrothendieckAddGroup`, `.of`, and `.lift`; `.lift` is the universal extension
  of an additive monoid map into an additive commutative group. Read the definitions
  and their docstrings in the multiplicative source and its `to_additive` declarations.
- `Mathlib.GroupTheory.Torsion`: `AddCommGroup.torsion`, the existing torsion subgroup.
- Proof-only import `Sheaf.GroupTheory.FineMonoidFiniteSaturation`:
  `fine_monoid_finite_saturation` (lem-trf-fine-monoid-finite-saturation). Its full
  signature includes fs root saturation, the normalized completion equivalence,
  finite translates, localization, and finite monoid algebra extension, without
  a torsion-free assumption. The theorem docstring includes all eight DAG proof steps.

Source reading: ILO Exposé VIII 3.1.17, printed p.101 (PDF page 107), defines root
saturation in the monoid's own completion; VI 2.1, printed p.71 (PDF page 77), defines
Kummer as injectivity plus a positive multiple of each target element in the image.
VI 2.2 states the finite cokernel annihilator condition. The ambient-group argument
is agent supplied, as the node explicitly records, and is reproduced in the docstring.

Edge cases checked mathematically:

- The identity map gives R=Q, H=Q^gp, trivial cokernels, and #C_tor=1.
- Multiplication by d>0 on N gives R=N, H=Z, C_tor=Z/d, and annihilator d.
- The diagonal N→N² gives R the diagonal monoid, H the diagonal subgroup,
  trivial torsion and torsion-free quotient Z. This also checks a non-surjective chart.
- N→Z gives R=N and H=Z: R must not be replaced by Q intersect H.
- The zero monoid into a finite abelian group gives R=Q and H=Q; saturation permits
  torsion groups. N plus a finite group likewise checks a nonsharp fs monoid.
- There is no empty-monoid case (a monoid contains zero), no n=0 root witness,
  and no assumption that a group completion is torsion-free. The trivial torsion
  subgroup has one element, so the required positive annihilator is 1, not 0.

Searches (all no exact match):

- `msearch.py leanfinder`, query “An injective map of fine saturated monoids factors
  through its root closure as a Kummer map followed by a map with torsion free group
  cokernel”: eight hits on Selmer groups, roots of unity and finite abelian duality;
  none states the monoid factorization.
- `msearch.py loogle`, query `"GrothendieckAddGroup", "torsion"`: zero hits.
- `msearch.py grep`, query `Kummer|kummer|NSMulSaturated|rootClosure`, GroupTheory:
  four hits in Subgroup/Saturated.lean, only the saturation property and kernel facts.
- Retained `searches.jsonl` records successful LeanSearch queries including “Injective
  map of fine saturated monoids factors as a Kummer map and a map with torsion free
  cokernel”: only completion injectivity and torsion-free transfer primitives.
- `rg` in upstream `WeilConjectures`, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the declaration name and Kummer/torsion
  factorization terms: no duplicate declaration. The upstream Kummer hits concern
  covers/classes; the landed consumer LogSmoothInvertibleTorsionLogRegular cites
  this node in its proof docstring but does not state this theorem.

The retained draft passed `scompile.py`; final compilation and preflight follow below.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q97

A second pass by the same dispatched worker (no additional agents were started) read
both the current node and the file again. The two fs assumptions, the group-map
injectivity and finite torsion hypothesis all match. R and H have precisely the two
membership formulas, with positive natural multiples. The completion equivalence and
H/A equivalence are normalized, so neither can be an arbitrary identification. The
factorization uses the actual inclusion b and pins down a on every p. Both group maps,
the torsion-free quotient, the Kummer clause, cardinality and positive annihilator are
present. Separate universes allow differently sized P and Q. No sharpness or ambient
torsion-free assumption slipped in. Removed the redundant pointwise a(p)=h(p) conjunct,
since equality of homomorphisms already states it and the factorization. Kept the legacy import format: the first dry run rejected the new `module` format
because the required proof dependency FineMonoidFiniteSaturation is not a `module`.
This is an import-format compatibility repair only. No mathematical mismatch or node
correction remains.

Final validation: `deliver2.py Q97 lem-per-fs-chart-torsion-factorization --no-push`
printed `OK (dry run)` after compiling both the sandbox name and the final library name
and passing the maintainer preflight. No errors or unexpected warnings remain.
