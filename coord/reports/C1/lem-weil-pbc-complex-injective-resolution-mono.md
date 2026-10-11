## Worker report

The module states `CochainComplex.exists_mono_quasiIso_injective_boundedBelow`, the
bounded-below injective-complex resolution lemma (Stacks Tags 013K(3) and 05T6(1)).
It uses Mathlib's `CategoryTheory.Abelian`, `CategoryTheory.EnoughInjectives`,
`CochainComplex`, `Injective`, `QuasiIso`, `Mono`, and `IsZero`.

The binders render the node clause by clause: `C` with `[Category C] [Abelian C]
and [EnoughInjectives C]` is the abelian category with enough injectives; `a : ℤ`
and `K : CochainComplex C ℤ` are the integer bound and cochain complex; `hK` says
`K.X n` is zero for every `n < a`; the existential `I` and `α : K ⟶ I` are the
new complex and complex morphism; the first conjunct gives `I.X n = 0` below `a`,
the second says every term is injective, the third says every component `α.f n`
is a monomorphism, and `QuasiIso α` says the induced map on every cohomology
object is an isomorphism.

No dependency module was needed: `def-sp-abelian` is Mathlib's
`CategoryTheory.Abelian`, and `def-sp-injective-resolutions` records Mathlib's
`CategoryTheory.Injective`/`InjectiveResolution` (with enough injectives as a
separate Mathlib class).  The source proof is recorded in the declaration
docstring for stage 3: specialize Stacks Lemma 05T6(1) to injectives; zero is
injective and enough injectives gives the subobject embeddings.

Edge cases checked: `a` is any integer (including negative values); the index is
all of `ℤ`; the zero complex and zero terms satisfy the lower-bound predicate;
no nonempty-index or nonzero-object assumption is introduced.

Searches: the node's recorded LeanSearch, LeanFinder, Loogle, and Mathlib grep
searches found Mathlib's nearby `CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective`
(which lowers the bound by one) and `exists_quasiIso_injective` (which lacks
componentwise monomorphisms), so neither states this node exactly.  `rg` over
`lean/Sheaf` and `WeilConjectures` found no existing declaration with this
statement.  The module was compiled with `scompile.py`; it has only the expected
`sorry`.

## Earlier second reading (a previous round; superseded)

Reading the node and file independently, the declaration introduces exactly the
category, integer bound, complex, lower-bound hypothesis, target complex, and
morphism in the node.  The four conclusion clauses match termwise vanishing,
termwise injectivity, componentwise monomorphisms, and quasi-isomorphism.  No
mismatch was found.

## Second reading by C1

I independently opened the item node, its two statement-dependency nodes, the delivered
Lean module, and the source text in `/home/ubuntu/c1-stacks-review/derived.tex`.
The local repository does not contain the literature checkout; that separate Stacks
checkout supplies the source. I read `lemma-injective-resolutions-exist` (013K),
including its hypotheses and proof, and `lemma-subcategory-right-resolution` (05T6).
The former assumes only an abelian category with enough injectives; the latter assumes
an abelian category and a subset containing zero into which every object embeds.
Neither imposes a Grothendieck, finiteness, field, or scheme hypothesis.

The node's objects, hypotheses, and conclusion clauses match as follows:

- Abelian category A: `(C : Type u) [Category.{v} C] [Abelian C]`. Exact.
  I read `CategoryTheory.Abelian` in `Mathlib.CategoryTheory.Abelian.Basic:112`:
  preadditivity, normal monos/epis, finite products, kernels, and cokernels.
  Its derived zero-object and finite-biproduct instances render `def-sp-abelian`.
- Enough injectives: `[EnoughInjectives C]`. Exact. I read
  `CategoryTheory.EnoughInjectives` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic:64`; each object has an
  `InjectivePresentation`, containing an injective target and a monomorphism.
  This is the notion already carried by `def-sp-enough-injectives`, a dependency
  of `def-sp-injective-resolutions`; no missing definition or private copy is needed.
- Integer bound: `(a : ℤ)`. Exact; universally quantified before the complex.
- Integer-indexed cochain complex: `(K : CochainComplex C ℤ)`. Exact; morphisms
  are complex morphisms, so their components commute with the differentials.
- K vanishes below a: `(hK : ∀ n : ℤ, n < a → IsZero (K.X n))`. Exact.
  `IsZero` is categorical zero, the correct invariant reading of K^n = 0.
- New complex and augmentation: `∃ (I : CochainComplex C ℤ) (α : K ⟶ I)`.
  Exact; both are chosen after C, a, K, and the hypothesis, as in the node.
- I vanishes below the same a: `(∀ n : ℤ, n < a → IsZero (I.X n))`. Exact.
  No shift to a - 1 or merely existential lower bound is allowed or introduced.
- Every term is injective: `(∀ n : ℤ, Injective (I.X n))`. Exact. I read
  `CategoryTheory.Injective` in `Mathlib.CategoryTheory.Preadditive.Injective.Basic:32`:
  every map to I extends along every mono. This is precisely the injective-object
  clause of `def-sp-injective-resolutions`; the object-resolution structure
  `InjectiveResolution` is not needed for a resolution of a complex.
- Every augmentation component is monic: `(∀ n : ℤ, Mono (α.f n))`. Exact;
  this includes degree a, not only degrees strictly above it.
- The augmentation is a quasi-isomorphism: `QuasiIso α`. Exact. I read
  `HomologicalComplex.QuasiIso` in `Mathlib.Algebra.Homology.QuasiIso:139`,
  together with `quasiIso_iff` and `quasiIsoAt_iff_isIso_homologyMap`:
  it means an isomorphism on each cohomology object. Abelian C supplies the
  requisite homology instances, so none is an additional hypothesis.

Edge cases: a may be negative, zero, or positive; degree zero and degree a are
included without a special restriction. K may be the zero complex, and I's zero
terms are injective (read `Limits.IsZero.injective`). The category with only a
zero object is permitted. The index is explicitly Z, not an arbitrary possibly
empty index set; hence no empty-index case of the node is excluded. Schemes,
characteristics, rings, and fields do not enter this categorical statement.
The explicit independent universes `u v` allow arbitrary object and morphism
universe sizes. No variable or universe is unbound.

Independent searches (using different wording from the first worker):

- `msearch.py ... leanfinder "degreewise injective replacement of a cochain complex
  preserving its strict lower bound with an injective quasi-isomorphism"`: eight
  hits, including `CochainComplex.isKInjective_of_injective`, `cm5b`, and `cm5b.I`.
  These are a K-injectivity criterion or factorization/construction statements,
  not this existence statement with all four clauses.
- `msearch.py ... leansearch "abelian category enough injectives complex embedding
  quasi-isomorphism same vanishing degrees"`: service unavailable (Internal
  Server Error), recorded without a mathematical verdict.
- `msearch.py ... grep "exists.*(quasiIso|resolution)|cm5a_cof"
  Algebra/Homology/Factorizations`, followed by direct reading of CM5a:637-690.
  `exists_mono_quasiIso_injective` lowers the bound by one;
  `exists_quasiIso_injective` retains the bound but does not promise a mono
  in the boundary degree. `cm5a_cof` is a factorization of a given mono.
  None is an exact existing declaration of this node.
- `rg` for `exists.*(injective|Injective)|resolution.*mono|mono.*resolution` in
  `lean/Sheaf` and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.
  I opened the nearby modules `BoundedBelowInjectiveResolution`,
  `FunctorialInjectiveComplexEmbedding`, and `KInjectiveDegreewiseExistence`.
  The first is specific to module sheaves and lacks componentwise monos and the
  fixed lower bound; the others require Grothendieck categories and do not
  preserve the stated lower bound. No exact declaration was found.

No signature mismatch was found; the node and signature stay unchanged. Repairs:
the file lacked the standard copyright/license/authors header, which I added;
the proof docstring named the source lemma but omitted the exact DAG dependency
and did not explicitly carry its output clauses, so I expanded it into the
subset specialization, zero/enough-injectives checks, and the four outputs.
There are no new definition nodes, dependency modules, or statement corrections
to review, and no hollow definitions. The sole theorem remains `:= by sorry`.
Both source places and the blueprint marker remain in the docstrings.
I checked that `lean.statement` equals the signature verbatim, and all lines
have at most 100 characters. Server `scompile.py` compiled the repaired file
cleanly in 1.3 seconds with no warnings or errors.
