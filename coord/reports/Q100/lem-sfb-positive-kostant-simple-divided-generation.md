## Worker report

The module `Sheaf.Algebra.Lie.PositiveKostantSimpleDividedGeneration` states
`LieAlgebra.positive_kostantIntegralForm_eq_simple`, with its proof `sorry`.
It defines no new notions. The node changes only in `lean`.

Hypotheses and objects, clause by clause:

- The finite-dimensional rational Lie algebra is `L : Type u`, with `[LieRing L]`,
  `[LieAlgebra ℚ L]`, and `[FiniteDimensional ℚ L]`.
- Semisimplicity is `[LieAlgebra.HasTrivialRadical ℚ L]`, exactly the predicate of
  `def-wf-semisimple-lie-algebra`; it means no nonzero solvable ideal, by
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`.
- The splitting Cartan is `H : LieSubalgebra ℚ L`, `[IsLieAbelian H]`, and `hmax`.
  The eigenvector condition `he` together with the full Chevalley basis `B`, `Bh`, `Be`
  supplies the splitting: every `ad(h)` is diagonal on that basis, zero on `H` and
  with the specified root eigenvalues on `e i`. Thus no extra splitting assumption
  or weaker arbitrary root-vector family has replaced the node's Cartan datum.
- The finite reduced crystallographic root system is `I : Type v`, `[Finite I]`,
  `P : RootPairing I ℚ (Module.Dual ℚ H) H`, `[P.IsRootSystem]`,
  `[P.IsCrystallographic]`, and `[P.IsReduced]`. `heval` specifies evaluation as its
  pairing, so the root functions and coroots have the stated meaning on `H`.
- The simple roots are `Δ.support` for `Δ : P.Base`; positive roots are
  `{i : I // Δ.IsPos i}`. The latter predicate is positivity of the sum of simple
  coordinates, equivalent to the usual positive-root convention for a reduced base.
- Root vectors are `e : I → L`. `he` gives nonzero vectors in the ordinary weight
  spaces, hence `[h,e_i] = root_i(h) e_i`. `B : Module.Basis (Δ.support ⊕ I) ℚ L`
  with `Bh` and `Be` identifies the first block with the simple coroots and the
  second with the root vectors. The simple coroots form a basis of `H`, as given
  by `Δ.toCoweightBasis`. The full basis then forces each root space to be its
  corresponding one-dimensional span, just as in the recorded PBW interface.
- `hopp` states `[e_i,e_{-i}] = h_i`, with `P.reflectionPerm i i` the opposite root.
- `hadd` gives exactly the signed root-string coefficient for every root sum:
  an integer `ε` with `ε = 1 ∨ ε = -1` times `P.chainBotCoeff i j + 1`.
  A root sum in a reduced system forces the roots to be independent, so the
  chain coefficient is the maximal nonnegative p of the node, rather than its
  junk value for dependent roots.
- `hzero` gives zero bracket whenever the sum is neither a root nor zero.
- The ambient algebra is Mathlib's `UniversalEnvelopingAlgebra ℚ L`, its actual
  quotient of `TensorAlgebra ℚ L` by the enveloping relations. The generator is
  `UniversalEnvelopingAlgebra.ι ℚ`.
- The divided power is the existing `Algebra.rationalDividedPower`, defined as
  `(1 / (n.factorial : ℚ)) • x ^ n`, for every natural n, including zero.
- The positive integer algebra is the existing `LieAlgebra.kostantIntegralForm`
  applied to `fun i : {i : I // Δ.IsPos i} ↦ e i.val`. The same construction on
  `fun i : Δ.support ↦ e i.val` is the simple-positive integer algebra. Both
  are unital `Subalgebra ℤ (UniversalEnvelopingAlgebra ℚ L)` objects, not
  rational spans or reductions modulo a prime.

Conclusions, clause by clause:

- The first conjunct is equality of exactly these two integer subalgebras.
- The second conjunct quantifies over every positive root i and every n. It
  supplies a finite number t of terms, integer coefficients `c : Fin t → ℤ`,
  and finite words `w : Fin t → List (Δ.support × ℕ)`. Each letter records
  a simple root and an exponent. `List.map` followed by `List.prod` evaluates
  the word in its given order in the noncommutative algebra. The sum
  `∑ j : Fin t, c j • ...` is the required finite integer linear combination.
- The third conjunct explicitly handles `IsEmpty I`: both algebras equal `⊥`.
  The bottom unital integer subalgebra is exactly the scalar image of ℤ,
  which is the meaning of their being ℤ as subalgebras of this rational algebra.

Dependency declarations read and used:

- `def-wf-lie-algebra` is a Mathlib node, not a missing Lean record. The relevant
  declarations are `LieRing`, `LieAlgebra`, and `LieSubalgebra` from
  `Mathlib.Algebra.Lie.Basic` and `Mathlib.Algebra.Lie.Subalgebra`, together with
  the ordinary `LieModule.weightSpace` from `Mathlib.Algebra.Lie.Weights.Basic`.
- `def-wf-semisimple-lie-algebra` is likewise a Mathlib node: `HasTrivialRadical`
  and its no-solvable-ideals equivalence, in `Mathlib.Algebra.Lie.Semisimple.Defs`
  and `Mathlib.Algebra.Lie.Semisimple.Basic`. The relevant full class signatures
  and their docstrings were read.
- Public import `Sheaf.Algebra.Lie.KostantIntegralPBW` is the recorded module for
  `lem-sfb-kostant-integral-pbw`; its entire theorem
  `LieAlgebra.exists_kostant_integral_pbw_basis` and proof docstring were read.
  This theorem's evaluation pairing, weight-space condition, bracket-table
  conditions and Chevalley basis are used without making private replacements.
  The simple-root basis is indexed directly by `Δ.support`, rather than by an
  unnecessary finite enumeration. Its public import
  `Sheaf.Algebra.Lie.KostantIntegralForm` supplies `kostantIntegralForm` and
  `Algebra.rationalDividedPower`. Their definitions and docstrings were read.
- Proof-only import `Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition` supplies
  `LieAlgebra.exists_splitSemisimple_rootDecomposition`, whose full statement
  and proof plan were read. It is the recorded proof dependency.
- Proof-only import `Mathlib.LinearAlgebra.RootSystem.BaseExists` supplies
  `RootPairing.Base.mk'`, part of the Mathlib match for
  `lem-sfb-root-base-rational-integral-spans`. The other clauses use
  `RootPairing.Base.toWeightBasis`, `toCoweightBasis`, `span_int_root_support`,
  and `span_int_coroot_support` in `Mathlib.LinearAlgebra.RootSystem.Base`.
- The remaining recorded Mathlib proof dependencies are
  `RootPairing.Base.exists_eq_sum_and_forall_sum_mem_of_isPos` in
  `Mathlib.LinearAlgebra.RootSystem.Base`, and
  `RootPairing.root_add_zsmul_mem_range_iff` in
  `Mathlib.LinearAlgebra.RootSystem.Chain`. Their signatures and hypotheses
  were read; these modules are already publicly imported by the PBW module.
- `lem-sfb-root-string-divided-adjoint-triangular` has no Lean record or
  Mathlib match yet. It is only a proof dependency, so there is no import to
  add at this stage. The theorem docstring preserves its exact role in the
  two-level induction. This missing future proof import does not affect the
  item's ability to state its mathematical conclusion.

Edge cases checked before writing:

- Empty roots and the zero Lie algebra are admitted: neither I nor Δ.support
  has a Nonempty requirement. Both generating sets are empty and both unital
  adjoins are the scalar subalgebra. The final conjunct records this case.
- Exponent zero is allowed in the generators and in the finite-word clause.
  Its divided power is one; the empty word is a valid expression for it.
- The empty linear combination (`t = 0`) is allowed, as are the empty word,
  integer zero coefficients and negative integer coefficients.
- In type A1 all positive roots are simple, so the equality is immediate as
  sets of generators and the word clause uses a one-letter word.
- In nonsimply-laced types no division by 2 or 3 is imposed over ℤ: all
  factorial divisions are already in the rational ambient algebra; the proof
  plan uses sign-only isolation in the divided-adjoint triangular relation.
- The universes u and v are explicitly declared, all binders are explicit,
  and both autoImplicit options are false. There is no restriction of rank,
  root order, basis sign, or characteristic beyond the given rational setting.

Searches made for an exact existing statement:

- `msearch.py ... leanfinder "The positive integral Kostant form is generated
  over the integers by divided powers of simple positive Chevalley root vectors"`:
  8 hits, chiefly `RootPairing.RootPositiveForm` and Geck constructions. These
  concern root bilinear forms, not generation in the noncommutative enveloping algebra.
- `msearch.py ... loogle '"UniversalEnvelopingAlgebra", "span"'`: 0 hits.
- `msearch.py ... grep
  "Kostant|Chevalley.*divided|divided.*Chevalley|positive.*envelop"`: 0 hits in Mathlib.
- `msearch.py ... leansearch "Every positive root divided power belongs to the
  integer algebra generated by simple positive root divided powers"`: 8 hits
  on commutative divided-power ideals and the integer root lattice; none match.
- `rg -n` on `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, `kostantIntegralForm`,
  `rationalDividedPower`, and simple divided powers found the existing
  Kostant-form construction, PBW and Borel comparison interfaces but no
  simple-positive generation theorem. A broader Kostant/Chevalley search
  found the same relevant modules and unrelated Chevalley geometry results.
- The exact item-id search in `lean/WeilConjectures` has no result.
  Mathlib's `Algebra.adjoin_eq_span` was also read: it describes the general
  span of a multiplicative closure, not this Lie-theoretic generation assertion.

Sources read: the current blueprint's `sk-thm-sf-ctf-stability/_section.md`
and direct-images proof (3), which are the inherited higher-level context;
Mathieu's Section 1, printed pp.150–151, read at
https://www.imsc.res.in/~knr/vdk/mathieu.pdf (PDF pages 5–6). That passage
uses simple divided powers to specify the integral form and the positive
hyperalgebra. The node supplies the supporting integral comparison assertion
and its agent-written proof; its statement needs no correction. No disputed
statement or dependency-interface fault was found.

Validation: `scompile.py Q100 lem-sfb-positive-kostant-simple-divided-generation
<module>` passed in both sandbox and library-module modes (1.3 s / 1.4 s),
with no errors or warnings.

## Second reading by Q100

The original "second reading" was a re-check by the same worker; no separate reader
opened the node and the file. The maintainer's reviewer replaced it with this reading.
I read the node, `def-sfb-kostant-integral-form` (through `lem-sfb-kostant-integral-pbw`),
`Sheaf/Algebra/Lie/KostantIntegralForm.lean`, `KostantIntegralPBW.lean`, and the Mathlib
declarations `RootPairing.Base` (Base.lean:70), `Base.height`/`Base.IsPos` (:397, :476),
and `RootPairing.chainBotCoeff` (Chain.lean:120).

Objects and hypotheses, with their Lean renderings:

- Finite-dimensional split semisimple g over Q: `L : Type u`, `LieRing`, `LieAlgebra ℚ`,
  `FiniteDimensional ℚ`, `HasTrivialRadical ℚ L` (the Mathlib record of
  def-wf-semisimple-lie-algebra). Matches.
- Splitting Cartan h: `H`, `IsLieAbelian H`, maximality `hmax`. Diagonalisation comes
  from `he` together with the basis `B`. These are the hypotheses of the landed PBW
  dependency, word for word. Matches.
- Reduced crystallographic root system R: `I`, `Finite I`, `P : RootPairing I ℚ (Dual H) H`,
  `IsRootSystem`, `IsCrystallographic`, `IsReduced`. `heval` makes P the evaluation
  pairing. Matches.
- R^+ and Δ: `Δ : P.Base`, `Δ.support`, and `Δ.IsPos i := 0 < Δ.height i`. In a Mathlib
  base every root is a nonnegative or nonpositive integer combination of the support
  roots, so positive height means positive root. Nothing is assumed beyond a choice of
  simple system. Matches.
- Chevalley basis: `B : Basis (Δ.support ⊕ I) ℚ L`, with `Bh` sending the h_i to the
  simple coroots and `Be` sending the e_α to the root vectors. `he` gives
  [h,e_α]=α(h)e_α. `hopp` gives [e_α,e_{-α}]=h_α, via `reflectionPerm i i` = −α.
  `hadd` gives ±(chainBotCoeff i j + 1). By Chain.lean:116, chainBotCoeff is the node's
  p_{α,β} = max{q : β−qα ∈ R} for independent roots, and a root sum in a reduced system
  has independent summands. `hzero` gives the zero bracket. These are the same as the
  PBW dependency; indexing the toral block by `Δ.support` instead of `Fin r` with `δ`
  is equivalent.
- U_Q: `UniversalEnvelopingAlgebra ℚ L`, the tensor-algebra quotient. e^{(m)}:
  `Algebra.rationalDividedPower x m = (1/m!) • x^m`, for every m including m = 0.
  Matches.
- K_Z^+: `kostantIntegralForm (fun i : {i // Δ.IsPos i} ↦ e i)`, which is
  `Algebra.adjoin ℤ` of all positive divided powers. This is a unital ℤ-subalgebra,
  not a ℚ-span. The simple algebra is the same construction on `Δ.support`. Matches.

Conclusion clauses:

- K_Z^+ = Z⟨e_α^{(m)} : α ∈ Δ⟩: the first conjunct, an equality of `Subalgebra ℤ`.
  Matches, neither weaker nor stronger.
- The equivalent formulation: the second conjunct, `∀ i, IsPos i → ∀ n, ∃ t c w`, with
  integer coefficients and ordered words `List (Δ.support × ℕ)` evaluated by
  `List.prod`. Matches the integer span of finite words.
- R = ∅: the third conjunct, `IsEmpty I →` both forms are `⊥`, the image of ℤ. Since
  U_Q is a nonzero ℚ-algebra, that image is ℤ. Matches.

Edge cases: an empty I (then `Δ.support` is empty and the basis forces L = 0); n = 0
(divided power 1, empty word); t = 0; type A1 (every positive root is simple);
nonsimply-laced types, where no division by 2 or 3 is assumed. The universes u and v are
independent, and no variable or universe is left unbound.

Other checks:

- One definition per notion: the statement reuses `kostantIntegralForm` and
  `rationalDividedPower` and defines nothing new. I found no simple-generation theorem
  in clones/side-live lean/Sheaf, and the worker's Mathlib searches cover leanfinder,
  loogle, leansearch and grep.
- Records: the item node changes only in `lean`, and `lean.statement` is verbatim from the
  file. The docstrings carry the source (Mathieu §1, pp. 150–151; Milne 23.71, C.21–C.22)
  and `(blueprint: …)`. The theorem docstring carries the four proof steps. The only
  proof is `sorry`.
- Advisory: the private imports `SplitSemisimpleRootDecomposition` and `BaseExists` are
  for the proof only and are unused at this stage. They are harmless.

No change to the Lean was needed. The only fault was this section (H11).
