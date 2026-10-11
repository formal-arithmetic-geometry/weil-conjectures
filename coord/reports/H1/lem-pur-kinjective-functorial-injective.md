## Worker report

The module `Sheaf.CategoryTheory.GrothendieckAbelian.FunctorialInjectiveComplexEmbedding`
states `CochainComplex.exists_functorial_injective_complex_embedding`, with its sole
proof `sorry`. No new definitions or dependency modules are needed, and no node
statement was changed.

Hypothesis and clause correspondence:

- The category is arbitrary: `(C : Type u) [Category.{v} C]`, with explicit independent
  object and morphism universes. Its abelian and Grothendieck assumptions are
  `[Abelian C] [IsGrothendieckAbelian.{v} C]`. The Grothendieck universe is the morphism
  universe, as the dependency's Mathlib match requires; local smallness in that
  universe is automatic. Small colimits follow from the Grothendieck instance.
- A single functor on all integer-indexed cochain complexes is
  `∃ (N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)`.
- A natural transformation from each complex to its image is
  `(j : 𝟭 (CochainComplex C ℤ) ⟶ N)`. The binder is outside `∀ M`, so this is a single
  functor and natural transformation, rather than unrelated choices for each complex.
- Clause (1), termwise monomorphism, is
  `∀ (n : ℤ), Mono ((j.app M).f n)` for every complex `M`.
- Clause (1), quasi-isomorphism, is `QuasiIso (j.app M)`, meaning the induced homology
  morphism in every integer degree is an isomorphism.
- Clause (2), for every integer degree, is `∀ (n : ℤ)` inside `∀ M`.
  The subobject is represented by an arbitrary object `I : C` with a monomorphism
  `b : I ⟶ (N.obj M).X n` and proof `Mono b`. This is precisely the usual
  representative of a subobject, without choosing a quotient representative.
  Its injectivity is `Injective I`. Factorization of the degree component of `j` is
  `a : M.X n ⟶ I` and `a ≫ b = (j.app M).f n`. The direction of composition matches
  the node. There is no additional compatibility requirement on these degreewise
  subobjects; the node does not require them to form a subcomplex or a functor.

Dependency declarations read and used:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, including its full
  definition, docstring, and small-colimit instance (lines 55–102).
- `def-pc-cochain-complex-modules`: `CochainComplex`,
  `Mathlib.Algebra.Homology.HomologicalComplex`, with arbitrary `C` substituted as
  the item explicitly asks. Its abelian-category instance was read in
  `Mathlib.Algebra.Homology.HomologicalComplexAbelian` (not imported: the statement does not use it; removed by reviewer R-kfi0928, H9). The dependent
  notation `.X`, `.f` uses the existing HomologicalComplex objects and morphisms.
- `def-pc-quasi-iso-modules`: `QuasiIso`, `Mathlib.Algebra.Homology.QuasiIso`;
  read its full definition and `quasiIsoAt_iff_isIso_homologyMap`. Again this is
  applied to `C`, exactly as the item requests.
- `def-sp-injective-resolutions`: the injective-object clause is
  `CategoryTheory.Injective`, `Mathlib.CategoryTheory.Preadditive.Injective.Basic`;
  the dependency's `mathlib_match.how` explicitly names this declaration for that
  clause. Both its definition and `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution` were read. No resolution
  is asserted by the item, so the resolution structure is not imported.

Edge cases checked before writing: zero complexes and the zero abelian category
are allowed; all integers, including negative degrees and zero, are quantified;
there is no boundedness condition. The injective factor need not be the entire
term of `N(M)`; claiming injectivity of all terms would strengthen the statement.
An empty category cannot satisfy the abelian hypotheses because it has a zero
object. Object universes are unrestricted and independent of morphism universes.

Source: the local literature copy of `injectives.tex` was unavailable, so the
statement and proof were read in the official Stacks source at
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex,
lines 1582–1643 (`lemma-functorial-injective`). They agree with the DAG node.
The theorem docstring transcribes all three DAG proof steps, including the
injective factor `0 ⊕ J(M)^n` and the quotient's contracting homotopy.

Searches for an existing statement:

- `msearch.py leanfinder`, query "functorial quasi-isomorphic embedding of cochain
  complexes factoring degreewise through injective subobjects": 8 hits, notably
  `CochainComplex.cm5b`, its auxiliary injective terms and projection, bounded
  K-injectivity, and derived-category fractions. No functor and natural
  transformation satisfying both clauses of this item.
- `msearch.py loogle`, query `CochainComplex, Injective, QuasiIso`: no hits;
  service reported unknown identifier `Injective`.
- `msearch.py grep`, query `functorial.*injective|injective.*functorial` in
  `Algebra/Homology`: no hits.
- `msearch.py leansearch`, query "functorial embedding cochain complexes
  quasi-isomorphism injective subobjects": service unavailable (Internal Server
  Error). This is recorded as unavailable rather than a negative result.
- Direct `rg` over the source `WeilConjectures` and project `lean/Sheaf`, query
  `functorial.*[Ii]njective|[Ii]njective.*functorial|lem-pur-kinjective-functorial-injective`:
  project hits concern embeddings of objects in other categories; upstream hits
  are in `CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean`. Read that
  whole file: it constructs functorial K-injective replacements and proves a
  monomorphic quasi-isomorphism, but has no assertion of the injective-subobject
  factorization clause of this node. These declarations are not the same statement.
- Direct `rg` in Mathlib's `CategoryTheory/Abelian/GrothendieckCategory`, query
  `functorial.*[Ii]njective|[Ii]njective.*functorial`: no matches.
- Name collision search in `dag/lean_names_upstream.json`, Mathlib, upstream
  `WeilConjectures`, and `lean/Sheaf` found no
  `functorial_injective_complex_embedding` or `functorialInjectiveComplexEmbedding`.

No statement dispute or dependency fault was found. All variables and universes
are explicitly bound. Server compile and dry-run preflight are the validation gates.

## Second reading by H1

I read the node `lem-pur-kinjective-functorial-injective` clause by clause against the Lean declaration.
The introduced objects render as follows: a Grothendieck abelian category is `(C : Type u)` with
`[Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]`; the functor is
`N : CochainComplex C ℤ ⥤ CochainComplex C ℤ`; and the natural transformation is
`j : 𝟭 (CochainComplex C ℤ) ⟶ N`. These match the node and retain independent object and
morphism universes. Clause (1)'s termwise monomorphism is
`∀ n : ℤ, Mono ((j.app M).f n)`, and its quasi-isomorphism is `QuasiIso (j.app M)`.
Clause (2) is rendered by
`∀ n, ∃ I a b, Injective I ∧ Mono b ∧ a ≫ b = (j.app M).f n`, with
`a : M.X n ⟶ I` and `b : I ⟶ (N.obj M).X n`; this is exactly a representative of the
injective subobject and the stated factorization. Quantifier order agrees with the node.
No hypotheses or conclusion clauses are added or omitted.

The zero category/zero complex, degree `n = 0`, negative degrees, and unbounded complexes are
covered. The integer index is unrestricted, and no characteristic, boundedness, finiteness, or
extra universe restriction is introduced. The injective factor is allowed to be any subobject,
including the zero object; requiring all terms of `N.obj M` to be injective would be stronger and
is not asserted.

I searched Mathlib and `WeilConjectures` with `msearch.py` LeanFinder, Loogle, grep, and direct
`rg` searches for functorial injective complex embeddings. The only related upstream result is a
K-injective replacement construction, which lacks this degreewise injective-subobject clause.
No existing declaration has this statement, so the new module is required.

No mismatch was found. I added the `lean` record below to this node; the module compiled cleanly
with `scompile.py`, with only the permitted `sorry` proof.
