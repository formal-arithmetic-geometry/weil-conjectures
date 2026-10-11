## Worker report

The module `Sheaf.NumberTheory.Padics.CoefficientExtension` defines the data of
`def-weil-l-adic-coefficient-extension`. It introduces no theorem and proves nothing.
No new node, dependency replacement, or statement correction is needed.

Hypotheses and clauses, read against the node:

- The prime is `(l : ℕ) [Fact l.Prime]`; its field is Mathlib's `ℚ_[l]` (`Padic l`).
  Every declaration explicitly binds `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  and `[FiniteDimensional ℚ_[l] E]`. Thus the extension is arbitrary, not required
  to come with an embedding into a selected algebraic closure. The algebra map
  is the extension's structure homomorphism. The degree is
  `coefficientExtensionDegree l E := Module.finrank ℚ_[l] E`.
- Clause 1: `coefficientExtensionAbsoluteValue` converts Mathlib's
  `spectralMulAlgNorm ℚ_[l] E` to `AbsoluteValue E ℝ` via
  `MulRingNorm.mulRingNormEquivAbsoluteValue`. Its nonnegative real values are
  exactly the node's absolute value (using ℝ rather than ℝ≥0 does not change
  its values, since the bundled absolute value contains nonnegativity).
  The term `spectralNorm_extends (K := ℚ_[l]) (L := E)` supplies the restriction
  equality to the DVR theorem directly. Uniqueness is the recorded
  `spectralNorm_unique_field_norm_ext`; nonarchimedeanness is
  `isNonarchimedean_spectralNorm`; completeness is `spectralNorm.completeSpace`.
  These are already dependency statements, not claims to prove anew here.
- Clause 2: `coefficientExtensionIntegers` selects the `O : Subring E` witness
  from `Padic.extension_integers_dvr` for that exact absolute value and restriction
  equality. `coefficientExtensionMaximalIdeal` selects `m : Ideal O` from the
  same witness's `choose_spec`, not from a second unrelated invocation/choice.
  The first two conjuncts of that theorem say precisely
  `x ∈ O ↔ abv x ≤ 1` and `x ∈ m ↔ abv (x : E) < 1`.
  Its later conjuncts give the local/DVR and finite-residue claims in the node.
  `coefficientExtensionResidueField` is exactly `O ⧸ m`. This reducible type
  definition retains Mathlib's quotient ring structure. The proof that m is
  maximal, hence that the quotient is a field, is supplied by the dependency;
  this module does not install additional typeclass instances for those facts.
- Clause 3: `coefficientExtensionUniformizer` chooses the element of O from the
  fourteenth conjunct of the same theorem's witness, whose predicate is
  `Ideal.span {π} = m`. Thus it is one chosen generator, not extra input and not
  a zero or arbitrary element. The theorem's thirteenth, fifteenth and sixteenth
  conjuncts give respectively the largest-value characterization, association
  of generators by a unit, and `∃! p : Oˣ × ℤ` expressing every `x : Eˣ` as
  `((p.1 : O) : E) * (π : E) ^ p.2`. Existence and these facts remain in the
  recorded dependency. No unknown data is placed in a definition: all choices
  are ordinary `Exists.choose` applied to the named dependency theorem.
- Clause 4: `coefficientExtensionIdeal l E n` is `(Ideal.span {π}) ^ n`.
  `Ideal.span_singleton_pow` identifies this with `Ideal.span {π ^ n}`, exactly
  `ϖ_Eⁿ 𝒪_E` in the node. Since the chosen π generates m, it is also mⁿ;
  consequently its ideal is independent of the choice of uniformizer.
  `coefficientExtensionRing l E n` is the quotient by this ideal. It is reducible
  so Mathlib sees its quotient ring structure. `coefficientExtensionTransition`
  is `Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))`, a ring
  homomorphism from the quotient at n+1 to the quotient at n. By `factor_mk`,
  it sends the class of each integer x to its class, so it is induced by the
  identity, not an arbitrary surjection. `factor_surjective` gives surjectivity.
  Finiteness and locality for n≥1 are the already cited finite-DVR-quotient
  dependency: its finiteness declaration, span-power equality, locality of a
  proper quotient, and quotient-factor surjectivity are recorded Mathlib matches.
  As with the residue field, these mathematical properties are supplied by the
  dependency rather than repeated as new theorem statements or typeclass instances.

Dependency declarations read and used:

- `def-weil-l-adic-numbers`: `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers` (completion of ℚ for the p-adic norm).
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`, giving
  `algebraMap ℚ_[l] E`; `[Field E]` specializes its general ring-algebra notion.
- `def-weil-vector-space-dimension`: `Module.finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finrank`.
- `lem-weil-l-adic-extension-absolute-value`: `spectralMulAlgNorm`,
  `spectralNorm_extends`, `spectralNorm_unique_field_norm_ext`, and
  `isNonarchimedean_spectralNorm` in
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`; the equivalence from ring
  norms to absolute values is in `Mathlib.Analysis.Normed.Unbundled.RingSeminorm`.
- `lem-weil-l-adic-extension-complete`: `spectralNorm.completeSpace` in the same
  SpectralNorm module, for the spectral uniformity and a finite-dimensional E.
- `lem-weil-l-adic-extension-integers-dvr`: `Padic.extension_integers_dvr` in
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, read in full including its
  docstring and all sixteen conjuncts. This is the actual source of O, m and π.
- `lem-weil-valued-dvr-finite-quotients`: its recorded Mathlib pieces are
  `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`
  (`Mathlib.Topology.Algebra.Valued.LocallyCompact`), `Ideal.span_singleton_pow`
  (`Mathlib.RingTheory.Ideal.Operations`), `IsLocalRing.of_surjective'`, and
  `Ideal.Quotient.factor`/`factor_surjective`
  (`Mathlib.RingTheory.Ideal.Quotient.Defs`). We use the existing quotient-factor
  construction directly; no specialized duplicate of the general theorem is needed.

Edge cases: l=2 is included; no auxiliary characteristic or l≠p restriction is
introduced because this node concerns the coefficient extension alone. The degree-one
extension E=ℚ_[l] is included. A field cannot have dimension zero over this field,
so no artificial positivity assumption is added. The universe u is arbitrary.
The parameter n is a natural number, covering all the node's integers n≥1.
The same formula is additionally defined at n=0: the ideal is the whole ring and
the quotient is the zero ring; no locality/nontriviality claim at n=0 is made.
The transition for n=1 is the expected quotient at exponent 2 onto the residue
quotient at exponent 1. No selection of uniformizer is assumed canonical.

Searches for reuse:

1. `msearch.py ... leanfinder "finite extension of p-adic numbers valuation ring
   uniformizer finite coefficient quotient rings"`: eight hits, including
   PadicInt residue representatives and general valuation uniformizer theorems;
   no assembled finite-extension coefficient datum.
2. `msearch.py ... loogle "spectralMulAlgNorm, Ideal.Quotient.factor"`: zero hits
   for the combined query. Both individual declarations were found/read in source.
3. `msearch.py ... grep
   "CoefficientExtension|FiniteCoefficientDatum|ExtensionIntegers|spectralMulAlgNorm"`:
   five SpectralNorm hits, defining the existing spectral multiplicative norm,
   which is reused.
4. `msearch.py ... leansearch "finite extension p-adic numbers coefficient rings
   uniformizer"`: unavailable, Internal Server Error (not a negative result).
5. `rg` for coefficient/uniformizer/extensionIntegers names in project source and
   `lean/Sheaf`, and for the node id in all of `WeilConjectures`: no existing
   realization of this node. The source file
   `WeilConjectures/NumberTheory/Padics/Extension.lean` was read in full:
   `PadicAlgCl.integers` restricts along an input embedding
   `[Algebra E (PadicAlgCl l)]`, with a compatible scalar tower for finite-extension
   results. It does not give this node's data for an arbitrary extension carrying
   only `[Algebra ℚ_[l] E]`; this delivery requires no extra embedding data.
6. `rg` for the proposed coefficientExtension names in Mathlib, source, Sheaf and
   `dag/lean_names_upstream.json`: no existing names or assembly found.

Source verification: the local literature copies are absent. Read the master
`def-weil-finite-field-fiber.md` and slopmaster2
`01_final_weil_conjectures.tex:36-58` over ssh from the server. The master explicitly
uses every finite E/ℚ_l and O_E/ϖ_Eⁿ; the slopmaster2 auxiliary datum explicitly
names the transition quotient map. No statement fault or dispute was found.

Validation: `scompile.py C1 def-weil-l-adic-coefficient-extension` compiled the
121-line module cleanly, exit code 0, with no warning. Initial compilation exposed
an opaque quotient-type instance issue and one long line; the quotient type
aliases were marked reducible and the projection line wrapped, then compilation
was repeated successfully. The final dry run is recorded below after it finishes.

Dry run: `deliver2.py C1 def-weil-l-adic-coefficient-extension --no-push` printed
`OK (dry run)`: server compilation and preflight pass except for the independent
second reading, which the second reader writes. Nothing was pushed. The preflight
signature reader starts at `def`, so `lean.statement` records that keyword and
binders without the preceding `noncomputable` modifier.

## Second reading by C1

I independently read the node, its source place, all seven statement dependencies,
and `CoefficientExtension.lean`. The introduced objects and their Lean renderings
match item by item: a prime and finite-dimensional field extension are the binders
`(l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
[FiniteDimensional ℚ_[l] E]`; the degree is `coefficientExtensionDegree` using
`Module.finrank`; the unique extending absolute value is
`coefficientExtensionAbsoluteValue`; the valuation ring and maximal ideal are
`coefficientExtensionIntegers` and `coefficientExtensionMaximalIdeal`; the residue
field is their quotient; `coefficientExtensionUniformizer` chooses a generator;
and `coefficientExtensionIdeal`, `coefficientExtensionRing`, and
`coefficientExtensionTransition` give the powers, quotient rings, and maps for
each `n : ℕ`. The source's assertions are represented by the cited dependency
theorems, while this definition contains only noncomputable choices and no proof.

The conclusion clauses agree: the absolute value restricts through
`spectralNorm_extends`; the DVR witness supplies the membership descriptions,
local/DVR and finite-residue facts, maximal ideal, and uniformizer properties;
the coefficient ideal is the `n`th power of the uniformizer span; and the
transition is `Ideal.Quotient.factor` for `Ideal.pow_le_pow_right (Nat.le_succ n)`.
No extra field, embedding, characteristic assumption, or finiteness hypothesis
appears. The quotient aliases are marked `@[reducible]`, preserving the quotient
ring structures required by the node.

Edge cases checked: arbitrary universe `u`, `l = 2`, degree-one extension
`E = ℚ_[l]`, all natural `n` including `n = 0` (where the power convention gives
the zero quotient), and the required `n ≥ 1` coefficient rings. The source does
not require a nonzero or locality assertion at `n = 0`, and none is introduced.

I repeated searches with `msearch.py` (LeanFinder and Loogle queries), `rg` over
Mathlib, `WeilConjectures`, and `lean/Sheaf`, and the upstream-name index. They
found only the component declarations already cited; no assembled coefficient
extension notion exists. The source's auxiliary datum was checked against the
same fields and transition maps. No mismatch was found and no source, node, or
Lean change was required. The module compiles cleanly with `scompile.py`.
