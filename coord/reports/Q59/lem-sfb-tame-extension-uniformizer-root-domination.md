## Worker report

The module `Sheaf.RingTheory.TameExtensionUniformizerRootDomination` states
`RingTheory.tame_extension_uniformizer_root_domination`, with one whole-proof `sorry`.
There are no new definitions, nodes, dependency replacements or statement corrections.
The node copy changes only `lean`. The source read was Stacks Project,
`more-algebra.tex`, lemma-characterize-tame (Tag 0EXW), especially (1) => (2)
through (3), and lemma-pull-root-uniformizer (Tag 09EV). The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read; this is a supporting algebra lemma, not the unit's own statement.

Hypothesis and clause correspondence:

- A DVR domain is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Its fraction field is `(F : Type v) [Field F]
  [Algebra R F] [IsFractionRing R F]`.
- The residue field `k = R / maximalIdeal R` is exactly Mathlib's
  `IsLocalRing.ResidueField R`, not a separately chosen field. `(p : ℕ) (hp : p.Prime)`
  and `[CharP (IsLocalRing.ResidueField R) p]` express positive prime characteristic.
- The uniformizer is `(pi : R) (hpi : Irreducible pi)`. Mathlib's
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this precisely with
  generation of the nonzero maximal ideal.
- `T/F` is a field extension with `[FiniteDimensional F T]` and
  `[Algebra.IsSeparable F T]`. `[Algebra R T] [IsScalarTower R F T]` record the
  composite ring map needed to form the normalization, without an independent choice
  of an incompatible `R`-action.
- `C` is used directly as `integralClosure R T`. `htame` quantifies over **every**
  maximal ideal `n` of this ring, using `[n.IsMaximal]`. Its localization is exactly
  `Localization.AtPrime n`.
- For each `n`, `∃ e : ℕ, ¬ p ∣ e ∧ ...` gives its prime-to-`p` ramification exponent.
  The next equality is literally the node's
  `maximalIdeal R` extended to `C_n` equals `maximalIdeal C_n ^ e`.
  No assumption about a Galois extension, residue degree divisibility or completeness
  is imposed. No separate extra DVR hypothesis on `C_n` is added.
- The remainder of `htame` gives the finite separable extension `(C/n)/k` via
  an existential `Algebra k (C/n)`, `IsScalarTower R k (C/n)`,
  `FiniteDimensional k (C/n)`, and `Algebra.IsSeparable k (C/n)`.
  The tower makes the structure canonical: `R -> k` is surjective, so its
  compatibility with the fixed constant map uniquely determines `k -> C/n`.
  The residue field of `C_n` is canonically `C/n`, since `n` is maximal.
- The conclusion begins `∃ m : ℕ, 0 < m ∧ ¬ p ∣ m`, retaining `m = 1`.
  It then gives `T'` with `Field`, compatible `F`- and `R`-algebras,
  `FiniteDimensional F T'`, `Algebra.IsSeparable F T'`, an `F`-embedding
  `T →ₐ[F] T'`, and `a : T'` satisfying `a ^ m = algebraMap R T' pi`.
  A field algebra homomorphism is automatically injective.
- The intermediate field `K` satisfies **equality**
  `K = IntermediateField.adjoin F {a}`, so it is exactly `F(a)`.
  `aK : K` with `(aK : T') = a` is the root represented in this subtype.
- `A : Subalgebra R K` satisfies **equality** `A = Algebra.adjoin R {aK}`,
  so it is exactly `R[a]` inside `F(a)`. These equalities introduce readable names
  without a `let` in the statement and without replacing generated objects by
  arbitrary intermediate rings or fields.
- `∃ (_ : IsDiscreteValuationRing A), IsFractionRing A K ∧ ...` gives the required
  DVR and its fraction field. Its domain structure is inherited from the subfield.
  `∃ aA : A, (aA : K) = aK ∧ maximalIdeal A = Ideal.span {aA}` identifies the
  maximal ideal as `(a)`, not merely a principal ideal with some other generator.
- `Nonempty (IsLocalRing.ResidueField R ≃ₐ[R] IsLocalRing.ResidueField A)` expresses
  the **canonical** residue identification over constants; an `R`-algebra equivalence
  commutes with the quotient maps. Such an equivalence is uniquely determined because
  `R -> k` is surjective. No arbitrary field identification is substituted.
- The final universal quantifier is over every maximal ideal `h` of the actual
  `H = integralClosure A T'`. Its first clause is exactly
  `maximalIdeal A` extended to `H_h` equals `maximalIdeal H_h`.
- Its second clause uses an existential `Algebra k (H/h)`, together with the explicit
  constant identity
  `algebraMap k (H/h) (IsLocalRing.residue R r) =
   algebraMap A (H/h) (algebraMap R A r)` for every `r : R`.
  This uniquely fixes the canonical extension over `k`; `FiniteDimensional` and
  `Algebra.IsSeparable` give exactly its finiteness and separability.
  Explicit constants avoid requiring Lean to infer an additional scalar action of
  `R` on the iterated normalization quotient.
- No henselianity or completeness class occurs. All input universes `u v w` are
  explicit and independent. The existential finite extension is in
  `Type (max u v w)`, large enough to construct it from any of the input fields;
  the statement does not restrict those inputs to a common universe.

Statement dependency declarations used (their recorded signatures and docstrings read):

- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing`, and `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` (publicly available
  through the statement imports); field extensions and their embeddings use its API.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`; its definition includes algebraicity.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, publicly imported through
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. Quotient residue fields at
  maximal ideals use Mathlib's `Ideal.Quotient.field`; their identification with
  prime residue fields is supported by `Ideal.bijective_algebraMap_quotient_residueField`.

The standard generated-field and generated-ring notions use Mathlib's
`IntermediateField.adjoin` and `Algebra.adjoin`; the fraction field and finite-dimensional
notions use `IsFractionRing` and `FiniteDimensional`. All recorded project proof modules
are imported privately: `WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra`,
`WeilConjectures.RingTheory.DvrNormalizedCompositumLocalDiagram`,
`WeilConjectures.RingTheory.DvrAbhyankarLocalMaximalIdeal`, and
`WeilConjectures.RingTheory.DvrAbhyankarLocalResidue`. Mathlib proof imports cover
normalization finiteness, algebraic closure, separable scalar extension and transitivity,
and integral prime/maximal-ideal contraction. The normalization-structure proof node
currently has no recorded Lean declaration; no unstated proof dependency is fabricated.
The theorem docstring carries all seven steps of the supplied natural-language proof.

Edge cases checked: `m = 1` is allowed and gives `F(a)=F`, `R[a]=R`, with `a=pi`;
`m = 0` is excluded only as in the source. `e = 0` cannot satisfy `¬ p ∣ e`.
The identity extension `T=F` is allowed. Both equal and mixed characteristic are
allowed; only the residue characteristic is fixed. A DVR is not a field and its
uniformizer is nonzero. All maximal branches are quantified, without selecting one
or restricting the normalization to a local ring. Zero rings are excluded precisely
by the source's domain/field assumptions. Finiteness means vector-space dimension,
never finite cardinality. Compatible residue algebra structures are unique, so their
existential packaging neither weakens nor strengthens the finite-separable conditions.

Searches (all run before finalizing the statement):

- `msearch.py ... leanfinder "A tame finite separable extension of a DVR fraction field
  embeds into an unramified extension after adjoining a prime-to-characteristic root
  of a uniformizer"`: 8 hits, including `galLift`,
  `Algebra.IsUnramifiedAt.of_liesOver`, and infinite-place ramification declarations;
  none states this root-domination theorem.
- `msearch.py ... loogle "IsDiscreteValuationRing, Algebra.IsSeparable"`: 0 hits.
- `msearch.py ... leansearch "Every tamely ramified finite field extension is contained
  in an unramified extension of a uniformizer root field"`: 8 hits, including
  `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`,
  `Algebra.FormallyUnramified.iff_isSeparable`, and local unramified residue finiteness;
  no existence of the required dominating extension.
- `msearch.py ... grep "tame|Abhyankar"`: 3 unrelated Beta-distribution hits.
  Direct `rg` in the named Mathlib DVR, localization, integral-closure and residue
  sources was also used to read the exact standard notions and canonical APIs.
- `rg -n 'tame|uniformizer.root|root.domination'` on project
  `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory`: related local Abhyankar
  and uniformizer-root compositum results, not this existential domination statement.
- `grep -rn 'lem-sfb-tame-extension-uniformizer-root-domination'
  lean/WeilConjectures`: no match.
- `rg -n 'tame_extension_uniformizer_root_domination|uniformizer_root_domination'`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no match.

Validation: the prescribed `scompile.py` compiled the sandbox and final library module
cleanly after replacing the uninferrable nested scalar tower by its explicit equality
on constants. Additional private Mathlib proof imports were then added and are checked
again by the delivery dry run. No statement fault or mathematical dispute was found.

## Second reading by Q59

This is the dispatched author's second reading, not an independent review; the brief
assigns independent review to the maintainer and prohibits starting other agents.
I reread the node against the file and checked each correspondence above. In particular,
the potentially weak encodings were checked: both adjoins are fixed by equality; the
root lies in the resulting field and ring via equality of the coerced elements; the
residue-field equivalence is over `R`; and the final residue extension commutes on every
constant. These conditions remove arbitrary choices of a residue-field action. The
normalization in the last clause is over `A`, not over `R`, and the ideal equality is
asserted in every maximal localization. There are no extra local, Galois, henselian,
completeness, degree-divisibility or uniformizer hypotheses. The proof is wholly
`sorry`; no helper theorem or definition has been inserted. No node field other than
`lean` changed, and the recorded signature is copied verbatim from the theorem.
