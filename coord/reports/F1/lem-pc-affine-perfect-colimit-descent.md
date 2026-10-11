## Worker report

The module `Sheaf.Algebra.Homology.AffinePerfectColimitDescent` states
`CochainComplex.exists_finite_projective_model_of_directed_colimit`, with proof `sorry`.
It descends the given bounded finite projective complex itself, including its differentials,
and concludes with an isomorphism in the category of complexes. No definitions or proofs were
added. The node copy changes only `lean`.

Clause-by-clause reading:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]` |
| Directed system of commutative rings A_i | `F : I ⥤ CommRingCat.{u}`; the preorder category supplies transition maps and the functor supplies their identities and composition laws |
| Colimit A = colim A_i | `[HasColimit F]`, with `A` written directly as `(colimit F : CommRingCat.{u})` |
| Complex P of A-modules | `P : CochainComplex (ModuleCat.{u} (colimit F : CommRingCat.{u})) ℤ`; the complex structure includes all differentials and the square-zero relations |
| P is bounded | `hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)` |
| Each P^n is finite | `hfinite : ∀ n : ℤ, Module.Finite (colimit F : CommRingCat.{u}) (P.X n)` |
| Each P^n is projective | `hprojective : ∀ n : ℤ, Module.Projective (colimit F : CommRingCat.{u}) (P.X n)` |
| There is an index i | `∃ (i : I)` |
| There is a complex P_i of A_i-modules | `Pi : CochainComplex (ModuleCat.{u} (F.obj i)) ℤ` |
| P_i is bounded | `∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Pi.X n)` |
| P_i has finite terms | `∀ n : ℤ, Module.Finite (F.obj i) (Pi.X n)` |
| P_i has projective terms | `∀ n : ℤ, Module.Projective (F.obj i) (Pi.X n)` |
| P_i tensor A is isomorphic to P as complexes | `Nonempty (((ModuleCat.extendScalars (colimit.ι F i).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pi ≅ P)` |

`ModuleCat.extendScalars` uses the canonical map `(colimit.ι F i).hom`, sends each module
M to A tensor_{A_i} M, and each differential to its scalar extension. For commutative rings
tensor symmetry identifies this with the node's M tensor_{A_i} A notation. The conclusion
requires an actual complex isomorphism. Bounds of the descended complex are existential,
exactly as the node says; no uniform amplitude or rank is imposed.

Dependencies read and used:

- `def-weil-pbc-projective-module`: `Mathlib.Algebra.Module.Projective`, declaration
  `Module.Projective`. Read its full signature/docstring and split-surjection-from-free
  definition. This is used verbatim in both projectivity clauses.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`, declaration
  `CategoryTheory.Limits.colimit`, with `colimit.ι`. Read the generated-dual declaration
  source/docstring. These give A and its canonical stage maps; Ring.Colimits supplies the
  commutative-ring-category infrastructure.
- `def-pc-perfect-complex`: `Sheaf.AlgebraicGeometry.PerfectComplex`, declarations
  `AlgebraicGeometry.Scheme.IsStrictlyPerfect`, `AlgebraicGeometry.Scheme.IsPerfect` and
  `perfectSubcategory`. Read the complete module, signatures and docstrings. This dependency
  is contextual in this node: the parenthetical identifies bounded finite projective module
  complexes as the affine form of perfect complexes; the node introduces no scheme or
  derived object and asks for no IsPerfect predicate. Thus the theorem uses the stated affine
  data directly, and does not import the scheme module merely for an unused name. No private
  replacement of IsPerfect was defined.

Other existing APIs read: `Module.Finite` in Mathlib.RingTheory.Finiteness.Defs means finitely
 generated; `ModuleCat.extendScalars` in Mathlib.Algebra.Category.ModuleCat.ChangeOfRings;
`CategoryTheory.Functor.mapHomologicalComplex` in Mathlib.Algebra.Homology.Additive.

Edge cases: Stacks [00D3](https://stacks.math.columbia.edu/tag/00D3) defines directed sets as
nonempty preorders with common upper bounds, so Nonempty is part of that hypothesis and
antisymmetry is not imposed. The index and ring universes are tied as required by the standing
brief. Zero complexes, complexes concentrated in one degree, zero rings, and zero terms are
included; no Nontrivial ring/module hypothesis or positive-rank requirement occurs. Empty
support is allowed even with bounds a > b, which just forces every term to be zero. Positive
and negative degrees are both included by ℤ. No characteristic or Noetherian condition is
added. No statement fault or disputed statement was found.

Source: local literature/stacks-project/more-algebra.tex is absent on this machine. Read
[Stacks 0BC7](https://stacks.math.columbia.edu/tag/0BC7) online instead, including the proof's
finite-projective-summand and finitely-presented-module descent argument. The existing node
records the bounded-complex form of this affine descent argument.

Searches on 2026-10-11:

- msearch LeanFinder: `bounded complex finite projective modules descends along directed
  colimit of commutative rings`: 8 hits (ModuleCat.enoughProjectives, projectivity criteria,
  Module.projective_of_localization_maximal, FGModuleCat finite carrier colimits). None
  states descent of a bounded complex.
- msearch Loogle: `ModuleCat.extensionOfScalars, Functor.mapHomologicalComplex`: zero hits,
  unknown identifier ModuleCat.extensionOfScalars. Direct source search found the actual API
  name `ModuleCat.extendScalars` and its full implementation was read.
- msearch grep: `descend.*perfect|perfect.*descend|extensionOfScalars`, subdirectory
  Algebra/Category/ModuleCat: zero hits.
- msearch LeanSearch: `bounded complexes of finite projective modules descend along filtered
  colimits`: unavailable (Internal Server Error); no verdict inferred from this failure.
- Direct rg of Mathlib: `colimit.*[Pp]erfect|[Pp]erfect.*colimit|descend.*[Pp]erfect|[Pp]erfect.*descend`:
  zero hits.
- Direct rg of WeilConjectures/, lean/Sheaf/ and dag/lean_names_upstream.json:
  `exists_finite_projective_model_of_directed_colimit|lem-pc-affine-perfect-colimit-descent|descend.*perfect|perfect.*descend`:
  zero hits. The proposed declaration name is unused.

Validation: server scompile passed with exit code 0 and no warnings. Its first pass required
explicit CommRingCat type annotations on the colimit when used as a coefficient ring; these
were added and the statement recompiled cleanly. The annotations fix elaboration without
changing any mathematical clause. All universe and variable binders are explicit.

## Second reading by F1

Independent second reading on 2026-10-11, with the repository node, sandbox node copy,
Lean file and dependency declarations open. Verdict: the Lean says exactly what the node
says. No mathematical or Lean mismatch was found; the module and node record are unchanged.
This section records the independent reading rather than relying on the worker's report.

Source check: the repository has no `literature/stacks-project/more-algebra.tex`. I fetched
current Stacks `more-algebra.tex` and `categories.tex` into this item's `scratchpad/` and read
Tag 0BC7, `lemma-colimit-perfect-complexes`, its proof, the chapter introduction, and Tag
00D3, `definition-directed-set`. I also opened the rendered tags online. The source treats
commutative rings and places no Noetherian, characteristic, field or nonzero-ring restriction
on this result. Its statement concerns derived perfect objects; its proof descends finite
projective modules using finite-presentation descent and finite-free summands. The DAG node
is explicitly the bounded-complex affine data argument implementing part (1), not a claim
that the entire derived-category statement has been formalized here. Descending the finitely
many differential maps and their square-zero equations gives the complex isomorphism in
this node. The source label is `lemma-colimit-perfect-complexes` (the node's shortened label
`more-algebra-lemma-colimit-perfect` is only a bibliographic locator discrepancy); Tag 0BC7
and lemma number identify the intended source unambiguously.

My object/hypothesis/conclusion inventory and its Lean match:

| Item in the node | Lean rendering | Verdict |
| --- | --- | --- |
| A directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]` | Exact: 00D3 includes nonemptiness and requires only a preorder, not antisymmetry. |
| Commutative rings A_i and their directed transition system | `F : I ⥤ CommRingCat.{u}` | Exact: the preorder category gives arrows for i ≤ j; functor laws give the system identities and compositions. |
| A = colim A_i, including the canonical maps | `[HasColimit F]`, `(colimit F : CommRingCat.{u})`, `(colimit.ι F i).hom` | Exact chosen categorical colimit in commutative rings; existence is categorical infrastructure, not a ring finiteness assumption. |
| Given complex P of A-modules | `P : CochainComplex (ModuleCat.{u} (colimit F : CommRingCat.{u})) ℤ` | Exact: integer cohomological degrees, A-linear differentials and d squared zero. |
| P bounded | `hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)` | Exact termwise vanishing outside a finite integer interval, not merely bounded cohomology. |
| P terms finite | `hfinite : ∀ n : ℤ, Module.Finite (colimit F : CommRingCat.{u}) (P.X n)` | Exact finite generation. |
| P terms projective | `hprojective : ∀ n : ℤ, Module.Projective (colimit F : CommRingCat.{u}) (P.X n)` | Exact recorded projective-module notion, not freeness or positive rank. |
| Existence of a stage i and a complex P_i over A_i | `∃ (i : I) (Pi : CochainComplex (ModuleCat.{u} (F.obj i)) ℤ)` | Exact quantifier order; no distinguished starting stage or extra later-stage condition. |
| P_i bounded | `(∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Pi.X n))` | Exact existential bounds, as in the node; no extra requirement that the bounds equal those of P. |
| P_i terms finite | `(∀ n : ℤ, Module.Finite (F.obj i) (Pi.X n))` | Exact. |
| P_i terms projective | `(∀ n : ℤ, Module.Projective (F.obj i) (Pi.X n))` | Exact. |
| P_i tensor A is isomorphic to P as complexes | `Nonempty (((ModuleCat.extendScalars (colimit.ι F i).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pi ≅ P)` | Exact actual complex isomorphism, preserving differentials, not only a quasi-isomorphism or degreewise unrelated isomorphisms. |

Dependency reading: I opened all three dependency JSON nodes, not merely their names.
`def-weil-pbc-projective-module` records Mathlib `Module.Projective`; I read its class and
`out` split-free-surjection field in `Mathlib.Algebra.Module.Projective` (lines 65–74).
`def-weil-pbc-category-colimit` records `CategoryTheory.Limits.colimit`; I read the
`to_dual` definitions of `limit`, `limit.π` and their generated `colimit`, `colimit.ι`
in `Mathlib.CategoryTheory.Limits.HasLimits` (lines 174–188). The ring coefficient is the
underlying carrier of the chosen `CommRingCat` colimit, not an unrelated supplied ring.
`def-pc-perfect-complex` records the scheme-level `IsStrictlyPerfect`, `IsPerfect` and
`perfectSubcategory`; I read `Sheaf.AlgebraicGeometry.PerfectComplex` in full. Those predicates
are contextual in the parenthetical affine interpretation: this node introduces neither a
scheme nor a derived object, and spells out the bounded finite-projective module data itself.
There is no private replacement predicate and no need for an unused scheme-module import.
I also read `Module.Finite` (the top submodule is finitely generated),
`ModuleCat.ExtendScalars.obj'`, `map'` and `extendScalars`, and
`Functor.mapHomologicalComplex`. Scalar extension sends terms to A tensor_{A_i} M and
maps to tensor extension of linear maps; commutative tensor symmetry identifies that with
M tensor_{A_i} A in the node. Mapping the complex applies this functor to its terms and
all differentials. None of these APIs adds an unmet external instance hypothesis.
No new definition node or dependency module is part of this delivery, so H12/H13 need no
additional node review.

Edge cases: empty I is excluded by the node's own directed-set hypothesis (00D3), exactly
as `[Nonempty I]` does. Empty support and the zero complex are allowed; `a > b` forces all
terms zero and introduces no extra case. A zero ring, rank-zero modules, and single-degree
complexes, including degree n = 0 and negative degrees, are allowed. No scheme is quantified,
so an empty scheme is not an object of this theorem; the corresponding zero-ring module
case is covered. There is no characteristic condition or Noetherian hypothesis. The same
universe u accommodates the index set, rings and modules as required by the standing brief;
u is arbitrary, and any set-sized data can be put in a common sufficiently large universe.
Finite-generation/projectivity impose no extra carrier-size condition after this choice.
All variables and the universe are explicitly bound, checked by eye and by server compilation
with auto-implicit disabled.

Independent searches (2026-10-11), using different wording from the first worker:

- `msearch.py ... leanfinder "finite projective cochain complex defined over a stage of a direct limit of rings"`:
  8 hits, principally K-projectivity and projective resolutions; none descends a complex over
  a ring colimit.
- `msearch.py ... loogle "ModuleCat.extendScalars"`: 12 hits, including the scalar-extension
  functor, adjunction, identity and composition isomorphisms. I read the actual functor;
  none of these hits is the proposed descent theorem.
- `msearch.py ... grep "finite_projective.*colimit|colimit.*finite_projective|projective.*descent"`:
  zero hits.
- Direct `rg` over Mathlib, `WeilConjectures/`, repository `lean/Sheaf/` and
  `dag/lean_names_upstream.json`, using descent/colimit/direct-limit with bounded or
  projective-complex wording and the proposed declaration name: no exact match. The project
  hits `FinitelyPresentedComplexDescent.lean` and `FlatBoundedComplexDescent.lean` were opened
  in full. They concern module sheaves on base-changed finitely presented schemes and assume
  Noetherian stage rings; they do not state this unrestricted ring-module result. Other
  source hits concern constructing K-flat models via colimits, not descending finite data.
  The proposed full declaration name is unused.

H5/H6/H8/H9: the module has one theorem with exactly `by sorry` and no new definition,
auxiliary proof, axiom or hollow hypothesis. Its docstring names Tag 0BC7 and the blueprint
id and follows all four DAG proof steps: finite term data; finite-presentation descent and
splitting identities; differentials and square-zero relations; assembling the complex
isomorphism. Header, namespace, topic path, imports and line lengths satisfy the conventions.
The sandbox node has no `statement_change`; there are no correction citers to verify.
I mechanically compared `lean.statement` with the file's complete signature before `:=`:
verbatim equal. The only change from this second reading is this appended independent report.

Validation: `scompile.py F1 lem-pc-affine-perfect-colimit-descent
lean/Sheaf/Algebra/Homology/AffinePerfectColimitDescent.lean` passed (exit 0, no warnings).
