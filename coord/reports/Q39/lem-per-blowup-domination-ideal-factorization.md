## Worker report

The module `Sheaf.AlgebraicGeometry.BlowupDominationIdealFactorization` states
`AlgebraicGeometry.AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq`.
Its sole theorem has proof `sorry`; no definitions or proved helper lemmas are added.
The original node is unchanged except for its `lean` record.

Clause-by-clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`, with `u` explicitly declared.
  There is no domain, Noetherian, nonzero-ring, or henselian-pair restriction.
- The two ideals are `(J K : Ideal R)`; finite generation is exactly
  `(hJ : J.FG) (hK : K.FG)`.
- Equality of radicals is `(hrad : J.radical = K.radical)`, using Mathlib's
  `Ideal.radical`. Mathlib allows exponent zero in its membership definition.
  This agrees with the node's positive-power definition: a witness zero means
  `1 ∈ H`, hence `H = ⊤`, so exponent one also witnesses membership.
- The base `X = Spec R` is the codomain `Spec (.of R)` of both `toSpec` maps.
  No independent base scheme or noncanonical identification is introduced.
- For each centre `H`, `AffineBlowup H` is the dependency's actual
  `Proj (reesGrading H)`; its canonical `toSpec H` is induced by degree zero.
- The existence of an `X`-morphism from `B_K` to `B_J` is
  `∃ f : AffineBlowup K ⟶ AffineBlowup J, f ≫ toSpec J = toSpec K`.
  The equation is the required compatibility with the canonical structure maps.
- “If and only if” is `↔`.
- A positive integer exponent is `∃ (n : ℕ) ..., 1 ≤ n ∧ ...`; positive natural
  numbers and integers at least one index exactly the same ideal powers.
- The factor is an actual ideal `(L : Ideal R)`, with the required `L.FG`.
- The factorization is precisely `K ^ n = J * L`, retaining its direction.

Statement dependencies read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-nagata-affine-blowup`: `WeilConjectures.Blowup.Affine.Defs`,
  `AlgebraicGeometry.AffineBlowup` and `AlgebraicGeometry.AffineBlowup.toSpec`.
  The full definitions were inspected: the former is Proj of the Rees algebra,
  the latter is `Proj.toSpecZero` composed with Spec of `reesGradingZero`.

Both modules are publicly imported. `Mathlib.RingTheory.Ideal.Operations` is also
publicly imported for radicals, ideal products, and powers. Recorded proof dependencies
are imported with plain `import`:

- `WeilConjectures.Blowup.FiniteDegree.Algebra`:
  `AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span` (finite generator chart cover).
- `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`:
  `Scheme.IdealSheafData.ideal_comap_appLE`.
- `WeilConjectures.Blowup.Principalization`:
  `Scheme.IdealSheafData.isInvertible_comap_blowupMap`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections`:
  `Scheme.Modules.invertible_sections_of_isAffineOpen`.
- `WeilConjectures.Blowup.BlowupUniversal`:
  `Scheme.IdealSheafData.IsInvertible.of_mul_left` and
  `Scheme.IdealSheafData.exists_lift_blowup`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`.

The theorem docstring carries all eight proof steps, including the regularity
argument after this particular pullback, torsion-aware denominator clearing, the
finite monomial bound, finite coefficient truncation, and the affine/global blowup
identification used for the reverse implication.

Source checked: the supplied local PDF of ILO, Expose XX section 4.4, printed p.373
(`pdftotext -layout ... -`). It defines `J ≤ J'` by an X-morphism from the blowup
at `J'` to that at `J`, and gives `(J')^n = J K` for `n > 0` when `V(J) ⊂ V(J')`.
The node is its equal-support specialization. Finite generation of the factor
follows by the finite coefficient truncation in proof step 6. No statement
correction or disputed statement is needed.

Edge cases checked mathematically before writing:

- The zero ring is allowed: its spectrum and both blowups are empty; the factor
  identity holds for its unique ideal with `n = 1`.
- For `J = K = ⊥`, both blowups are empty and `n = 1, L = ⊥` works.
- If `K` is nilpotent, radical equality and finite generation make `J` nilpotent
  as well. Both blowups are empty; a positive vanishing power of `K` and `L = ⊥`
  give the factorization. No excluded nonempty-source assumption is needed.
- If either ideal is the unit ideal, radical equality makes both unit ideals;
  their blowups are the base scheme and `n = 1, L = ⊤` works.
- For `J = K`, the identity morphism and `n = 1, L = ⊤` give both sides.
- Zero divisors are allowed: the forward proof clears localization equalities
  by extra powers, rather than claiming injectivity of `R → R[1/b]`.
- Finite generating lists may be empty; adjoining a zero generator handles that
  proof case without a nonzero-ideal hypothesis in the statement.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leansearch "Blowup domination of finitely generated ideals with
  equal radicals is equivalent to factorization of a positive ideal power"`:
  eight hits, including `Ideal.radical`, `Ideal.IsRadical`,
  `Ideal.exists_pow_le_of_le_radical_of_fg_radical`, and `Ideal.radical_pow`;
  none states the blowup equivalence.
- `msearch.py ... leanfinder "For finitely generated ideals with equal radicals
  a morphism between their blowups exists if and only if a positive power of one
  ideal is a product of the other ideal and a finitely generated ideal"`:
  eight hits, including `Ideal.exists_pow_le_of_le_radical_of_fg`, related
  radical-power bounds, local cohomology indexing, and
  `Algebra.zariskisMainProperty_iff'`; no exact match.
- `msearch.py ... loogle "AffineBlowup, Ideal.radical"`: zero hits;
  the search index does not know the project identifier `AffineBlowup`.
- `msearch.py ... grep "blowup|Blowup|reesAlgebra" AlgebraicGeometry`: zero hits.
- `rg` over project `WeilConjectures/Blowup` and `Sheaf/AlgebraicGeometry`
  for domination, ideal powers, factorization, and radicals found chart algebra,
  admissible product blowup comparisons, and unrelated geometric factorizations;
  none gives this equivalence. In particular, inspected
  `Blowup/AdmissibleBlowup.lean` has product comparisons, not this criterion.
- `grep -rn "lem-per-blowup-domination-ideal-factorization"` in
  `lean/WeilConjectures` found no declaration attached to this node.
- `rg "domination_iff_exists_pow|exists_hom_iff_exists_pow"` in
  `dag/lean_names_upstream.json`, `lean/Sheaf`, and `lean/WeilConjectures` found no
  name collision before the sandbox declaration was written.

Validation: `scompile.py Q39 lem-per-blowup-domination-ideal-factorization
<module path>` compiled both the sandbox form (8.1 s) and actual library module
form (9.0 s) successfully, with no compiler errors or unexpected warnings.
All imports use module mode; every universe and variable is explicitly bound.

## Second reading by Q39

Independent reading (maintainer reviewer, replacing the worker's self-check) with the node
`lem-per-blowup-domination-ideal-factorization`, ILO Exposé XX §4.4 (printed p.373), the
dependency declarations in `WeilConjectures/Blowup/Affine/Defs.lean`, and the delivered module
open.

Node clauses and their Lean:

- Commutative ring R: `{R : Type u} [CommRing R]`, `u` declared. No further instance is assumed. Exact.
- J, K finitely generated ideals: `(J K : Ideal R) (hJ : J.FG) (hK : K.FG)`. Exact.
- √J = √K with positive exponents: `hrad : J.radical = K.radical`. Mathlib's `Ideal.radical`
  allows exponent 0, but x^0 ∈ H forces H = ⊤, and then exponent 1 also works. Same ideal. Exact.
- X = Spec R (def-weil-affine-spectrum): `Spec (.of R)`, the codomain of `toSpec`. Exact.
- B_H = Bl_H(X) = Proj R_R(H) (def-nagata-affine-blowup): `AffineBlowup H := Proj (reesGrading H)`,
  with structure map `toSpec H = Proj.toSpecZero ≫ Spec.map (reesGradingZero H)`, which is the
  node's "induced by the degree-zero map". This is the recorded declaration. Exact.
- An X-morphism B_K → B_J exists: `∃ f : AffineBlowup K ⟶ AffineBlowup J, f ≫ toSpec J = toSpec K`.
  The direction agrees with ILO (J ≤ J' means Bl_{J'} → Bl_J, and J'^n = J·K). Exact.
- "iff": `↔`. Exact.
- ∃ n ≥ 1 and a finitely generated L with K^n = JL: `∃ (n : ℕ) (L : Ideal R), 1 ≤ n ∧ L.FG ∧ K ^ n = J * L`.
  The two existentials commute, so the order is harmless. Exact.

Edge cases:

- Zero ring: both blowups are empty, and n = 1, L = ⊥ works.
- J = K: the identity, with n = 1 and L = ⊤.
- Unit ideals: radical equality forces both ideals to be ⊤, both blowups are ≅ X, and L = ⊤.
- J = 0 with K nilpotent and FG: both Proj are empty, and K^n = 0 = J·⊥.
- Rings with zero divisors are allowed. The proof plan clears denominators by an extra power of b_i.
- Non-example in k[x,y]: J = (x,y), K = (x,y²). There is no domination and no factorization, so both sides agree.

Gates:

- No new definitions and no new nodes; the theorem's proof is `sorry` only.
- The module and theorem docstrings carry the source place and `(blueprint: …)`, and the theorem
  docstring gives proof steps 1–8 with their cited nodes.
- No line is over 100 characters.
- Imports: public for the statement dependencies, plain for the 8 proof-dependency modules. All
  8 exist in side-live.
- The node differs from live only in `lean`, and `lean.statement` is verbatim in the file.

Searches:

- `rg` over side-live `WeilConjectures/Blowup` for domination and `exists_hom_iff_exists_pow`
  found only `QuasiDominationExtension` and `ProperTargetExtension`. Both are admissible-blowup
  extension theorems, a different notion.
- Mathlib has no blowup API that matches.

Mismatches found: none in the Lean or the records. The earlier version of this section was a
self-check by the same worker; this section replaces it.
