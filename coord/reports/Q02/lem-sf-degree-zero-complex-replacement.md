## Worker report

The module `Sheaf.Algebra.Homology.DegreeZeroComplexReplacement` states
`CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree`, with its single proof
postponed by `sorry`. Its docstring contains all nine steps of the node's proof, including
zero-round stopping and construction by stabilized tails. No definitions or other DAG nodes
are introduced. The node copy changes only `lean`; its signature is copied verbatim from
the module. There is no statement correction or disputed statement.

Clause-by-clause correspondence:

- An arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`.
  Object and morphism universes `u`, `v` are explicit and independent.
- The nonnegative integer degree function is `(d : C → ℕ)`.
- The nonnegative integer bound is `(D : ℕ)` and its uniform bound is
  `hbound : ∀ A : C, d A ≤ D`. Encoding a nonnegative integer as a natural number
  retains exactly the stated possibilities, including zero.
- Every object embeds into a degree-zero object is
  `hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0`.
- The direct-sum bound is
  `hsum : ∀ A B : C, d (biprod A B) ≤ max (d A) (d B)`.
  Mathlib's `biprod` is the binary direct sum, supplied by the existing global
  `Abelian.hasBinaryBiproducts` instance; no additional biproduct hypothesis is needed.
- Every short exact sequence is quantified as `S : ShortComplex C` with
  `S.ShortExact`, and the required inequality is
  `d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)`.
  `ShortComplex` includes the relation `S.f ≫ S.g = 0`, and `ShortExact` means
  exactness, mono first map and epi second map. Thus all and exactly the stated
  short exact sequences are tested. Subtraction takes place in `ℕ`, hence is truncated.
- An arbitrary integer-indexed cochain complex is `(K : CochainComplex C ℤ)`;
  neither a lower nor an upper bound on its support is assumed.
- The replacement and its actual arrow out of K are
  `∃ (L : CochainComplex C ℤ) (f : K ⟶ L)`.
- The quasi-isomorphism clause is `QuasiIso f`, using Mathlib's isomorphism-on-every-
  cohomology definition, and the last clause is `∀ r : ℤ, d (L.X r) = 0`.
  No termwise monomorphism or extra conclusion is imposed.

Dependencies and source declarations read:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`;
  read the class docstring and signature, and the global binary-biproduct instance.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`; the statement uses the existing
  `CochainComplex` and `QuasiIso` notions of this interface. Also read their defining
  sources in `HomologicalComplex.lean` and `QuasiIso.lean`. No derived-category size
  assumption is necessary because the conclusion is about complexes, not localization.
- Proof-only import `Sheaf.Algebra.Homology.SubcategoryRightResolution` supplies
  `CochainComplex.exists_mono_quasiIso_in_subcategory` (05T6); read its full proof
  docstring and signature. It is used in proof step 2, not as an extra hypothesis.
- Proof-only Mathlib modules include `Algebra.Homology.HomologySequence` for
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₂`, and
  `CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels` for
  `CategoryTheory.Limits.isIso_cokernel_map_of_isPushout`. Read the recorded signatures.
  `CategoryTheory.Abelian.mono_pushout_of_mono_f` is in the already public Abelian import.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact` publicly supplies the short-exact
  sequence predicate occurring in the statement.

Read `literature/stacks-project/derived.tex`, the whole statement and proof of
`lemma-replace-resolution` (07K6), lines 9891–9987. The source permits infinite degrees
and a limiting condition; the node explicitly specializes to finite uniformly bounded
values. Its uniform bound implies the source's limiting condition, since
`r + d(K^r) ≤ r + D` tends to minus infinity. Thus no extra convergence hypothesis is
required and the node needs no correction.

Edge cases checked before writing: D = 0 gives L = K and the identity map; the zero
complex is covered since the embedding and short-exact assumptions force d(0) = 0;
all objects isomorphic to zero are covered since the short-exact inequalities force
isomorphism invariance. The cases d(A) = 0 and d(A) = 1 use genuine natural subtraction,
with no negative degree. Arbitrarily unbounded K and negative indices are included.
The zero category and different object/morphism universes are not excluded. There are
no finite/infinite colimit assumptions. The proof's initial resolution and stabilized
replacement tails require no enough-injectives assumption.

Searches for an existing statement (all services invoked through msearch.py for Q02
and this item; full outputs are also recorded in searches.jsonl):

- LeanFinder query: “An arbitrary cochain complex in an abelian category has a
  quasi-isomorphism into degree zero objects for a uniformly bounded nonnegative
  degree function decreasing on cokernels”. Eight results: `CochainComplex.cm5b`,
  its quasi-isomorphism instance, derived-category truncation representatives,
  `IsKInjective`, and truncation lemmas. None states replacement for an arbitrary
  bounded numerical degree on an unbounded complex. Read `CM5b.lean:127` and its
  context: it assumes enough injectives and explicit bounded-below support.
- Loogle query: `CochainComplex, QuasiIso`. Twelve results on shifts, truncation,
  localization, mapping cones and injective resolutions; no exact match.
- Mathlib grep query:
  `replaceResolution|replace_resolution|resolution.*degree|degree.*resolution`.
  Four hits: trivial injective/projective resolutions in degree zero and shifted
  continuous-cohomology resolutions; none matches.
- LeanSearch query: “Every unbounded cochain complex has a quasi-isomorphism into
  objects of degree zero for a bounded degree function decreasing in short exact
  sequences”. Eight hits on quasi-isomorphisms of short complexes, degree-zero
  homology, support and single complexes; none matches.
- `rg` over upstream WeilConjectures, side `lean/Sheaf`, and upstream-name records
  for `replaceResolution|replace_resolution|lem-sf-degree-zero-complex-replacement|`
  `exists_quasiIso.*degree|exists.*degreeZero`: only the downstream
  `FiniteCDDerivedUpperBound.lean` proof reference and an unrelated étale degree-zero
  comparison appeared. A broader degree-zero spelling search returned unrelated
  graded-ring, cohomology and representation theory declarations. Refined
  homology-directory searches for `degree.*(replacement|resolution)|bounded degree|`
  `degree function` found no replacement statement.

Validation:

The delivered file has maximum line width 92, all universes and variables are explicit,
and its only theorem has `sorry` as its entire proof. The prescribed scompile.py
attempt failed before checking this file: nt_local_compile.py unconditionally ensures
modules listed in its source-overrides.json manifest, including the unrelated
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
That module reports at line 119:18:
`AlgebraicGeometry.ProEt.overPullbackId has already been declared`.
Server confirmation failed on the same module and declaration. None of this delivery's
imports reaches that module; removing an import from the statement cannot repair the
unconditional overlay initialization. The wrapper and published overlay are read-only
for this worker, and no workaround or tool modification was attempted.

The required `deliver2.py Q02 lem-sf-degree-zero-complex-replacement --no-push`
dry run initially reproduced the unrelated overlay redeclaration before checking
this file. Re-running the prescribed command with the temporary overlay manifest
set to an empty list (the conflicting module is unrelated and not imported here)
compiled the file and printed `OK (dry run)`: the commit passed preflight except
for the required second reading. No second-reading section was written.

## Second reading by Q02

I independently opened the node, its Stacks source, and
`Sheaf/Algebra/Homology/DegreeZeroComplexReplacement.lean`. The node's objects,
hypotheses, and conclusion render as follows.

- The abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`; this is
  exactly the arbitrary category and independent object/morphism universes in the
  node. The dependencies are the recorded Mathlib `CategoryTheory.Abelian` and
  Mathlib's integer-indexed `CochainComplex`/`QuasiIso` interface.
- The numerical data are `(d : C → ℕ)`, `(D : ℕ)`, and
  `hbound : ∀ A : C, d A ≤ D`. `ℕ` is precisely the node's nonnegative integers,
  and the bound is uniform over every object.
- The embedding condition is rendered by
  `hembed : ∀ A : C, ∃ I j, Mono j ∧ d I = 0`, with `j : A ⟶ I` inferred from
  the existential. It introduces exactly the degree-zero overobject required by
  the node.
- The direct-sum condition is
  `hsum : ∀ A B, d (biprod A B) ≤ max (d A) (d B)`. `biprod` is Mathlib's
  canonical binary biproduct supplied by an abelian category, hence the same
  `A ⊕ B` object as the source convention; no extra finiteness or biproduct
  hypothesis is assumed.
- The short-exact condition is
  `hshort : ∀ S : ShortComplex C, S.ShortExact →
  d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)`. `X₁,X₂,X₃` are respectively the
  source, middle, and quotient objects, and `Nat` subtraction is truncated at
  zero, exactly as stated by the node. `ShortExact` supplies the short exact
  sequence condition; no stronger condition is added.
- The arbitrary complex is `(K : CochainComplex C ℤ)`, so all integer degrees,
  including negative and unbounded ones, are admitted. The conclusion is exactly
  `∃ (L : CochainComplex C ℤ) (f : K ⟶ L), QuasiIso f ∧
  ∀ r : ℤ, d (L.X r) = 0`: it introduces the replacement and its actual arrow,
  requires a quasi-isomorphism, and requires degree zero in every term.

The source is Stacks Tag 07K6, `lemma-replace-resolution`. Its hypotheses are
the three conditions on embeddings, binary sums, and short exact sequences, plus
the limiting condition `r + d(K^r) → -∞` at the negative end. The node's finite
uniform bound implies that condition (`r + d(K^r) ≤ r + D`), so the Lean theorem
correctly states the node's bounded specialization without an omitted source
hypothesis. Its proof docstring follows the source's splice, elementary
replacement, finite maximum elimination, stabilization, and cohomology argument
step by step.

Edge cases were checked: `D = 0` makes the identity of `K` a valid replacement;
`d(A)=0` and `d(A)=1` use truncated natural subtraction; the zero object and zero
complex are included through the stated embedding and exact-sequence hypotheses;
the empty/zero category is not excluded; negative indices and an unbounded input
complex are allowed; and no characteristic, Noetherian, enough-injectives, or
extra universe equality is present. The binary biproduct and all complexes use
the category's supplied abelian instances.

I repeated the existing-definition searches (LeanSearch, Loogle/LeanFinder, and
`rg` over Mathlib, upstream `WeilConjectures`, and `lean/Sheaf`) for replacement,
bounded-degree, and degree-zero complex statements. They found truncation and
injective-resolution results, but no declaration with this arbitrary bounded
degree-function statement. The two dependency nodes were also opened; both are
usable recorded declarations, so no new node or dependency module is needed.

No mismatch was found and no file or node field required change. The signature in
the node copy is verbatim the theorem signature. `scompile.py` compiles the module
successfully with no warnings; no proof was added, and the theorem remains a
statement with `sorry` only.
