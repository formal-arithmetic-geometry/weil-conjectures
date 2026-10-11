## Worker report

The module `Sheaf.Algebra.Homology.KInjectiveProducts` states
`CochainComplex.termwise_product_isKInjective_and_isLimit`, with `sorry` as its only proof.
The original node is unchanged except for `lean`. No new notions or dependency modules
are needed. All universes and variables are explicitly bound.

Source read: Stacks Project, Derived Categories, Lemma 13.31.5, Tag 0BK6,
https://stacks.math.columbia.edu/tag/0BK6 (the local literature checkout is absent).
Its hypotheses and both conclusions agree with the node. The title mentions ringed
spaces, but the statement and source concern arbitrary abelian categories.

Hypothesis and clause correspondence:

- Abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`.
- Set T: `{T : Type t}`, with its universe independent of C and its morphisms.
- Each integer-indexed cochain complex I_t: `(I : T → CochainComplex C ℤ)`.
- Each I_t is K-injective: `[∀ s : T, (I s).IsKInjective]`. This is precisely the
  predicate used by the recorded K-injective bridge: null-homotopy of every morphism
  from an acyclic complex. Applying it to all shifts is equivalent to acyclicity
  of the entire Hom complex, the node's convention.
- Products of this particular family exist in every degree:
  `[∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)]`.
  The discrete diagram has object `(I s).X n`; its limit is exactly the categorical
  product from `def-weil-category-product`. This does not assume all T-indexed
  products in C, or products for any other family.
- The termwise product complex I: the let-bound cone
  `P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)`.
  Its degree-n object is the chosen limit of the above degree-n discrete diagram;
  its differential is induced by the factors' differentials, and its projection
  chain maps have components the degreewise product projections. This existing
  Mathlib construction has genuine data and no new definition is introduced.
- The product complex is K-injective: the first conjunct `IsKInjective P.pt`.
- It represents the product of the Q(I_t) in D(C): the second conjunct
  `Nonempty (IsLimit (DerivedCategory.Q.mapCone P))`. This asserts the universal
  property for the localization of this exact product complex and these exact
  projections, with all derived objects as possible test objects.
- D(C) uses `[HasDerivedCategory.{w} C]`, the chosen localization and morphism-size
  convention already in `def-weil-abstract-derived-category`. This is localization
  data, not an assumption about K-injective resolutions or exact products in C.
  The standard localization exists with w = max u v for every abelian C.

Dependency declarations read and used:

- `def-sp-abelian`: Mathlib leaf `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Its class extends Preadditive and normal
  mono/epi categories, with finite products, kernels and cokernels; zero objects
  and finite biproducts follow. This is the node's exact abelian-category notion.
- `def-sp-kinjective-bridge`: `Sheaf.CategoryTheory.KInjectiveBridge`, read in full,
  particularly `CochainComplex.KInjectiveResolutionChoice.isKInjective`, whose type
  is `complex.IsKInjective`. The module is imported; its documented convention is
  used directly. Its recorded main declaration is
  `CategoryTheory.Functor.rightDerivedComplexWithResolution`; this item concerns
  K-injectivity itself and does not require a choice of resolution or a functor.
  The underlying declaration `CochainComplex.IsKInjective` was also read in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `def-weil-abstract-derived-category`: Mathlib leaf `DerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; also `HasDerivedCategory` and
  `DerivedCategory.Q`, all full signatures and docstrings read.
- `def-weil-category-product`: Mathlib leaf in
  `Mathlib.CategoryTheory.Limits.Shapes.Products`: `piObj`, `Pi.π`, `Pi.lift`,
  `Pi.map`, and `HasCountableProducts`. Their signatures/docstrings were read.
  `piObj` is `limit (Discrete.functor f)` under `HasProduct f`, which abbreviates
  exactly `HasLimit (Discrete.functor f)`. The statement uses the corresponding
  general cone/limit formulation `HasLimit` and `IsLimit`, without a separate
  definition of products or an unnecessary countability restriction.
- Construction read and used: `HomologicalComplex.coneOfHasLimitEval` in
  `Mathlib.Algebra.Homology.HomologicalComplexLimits`, including its full degreewise
  limit construction and the proof-carrying construction of its differentials.

Edge cases checked before writing:

- Empty T: each degreewise product is terminal and hence zero in an abelian
  category; the resulting zero complex is K-injective and its derived image is
  the empty product. There is no nonemptiness binder on T.
- Singleton T: the construction is isomorphic to its sole factor; both
  conclusions reduce to K-injectivity and the singleton-product property.
- Zero factors and the zero category are allowed.
- Unbounded complexes and every integer degree, including negative degrees and
  zero, are allowed; there is no boundedness or injectivity of individual terms.
- A category with only the required products still satisfies the hypotheses.
  Neither exactness of products in C nor Grothendieck conditions are required;
  the source proof uses exactness only in abelian groups.
- Universes u, v, w, t are independent; no countability or cardinal bound on T.

Searches for an existing statement:

- `msearch.py leansearch`: "Termwise products of K-injective cochain complexes are
  K-injective and are products in the derived category". Service unavailable:
  Internal Server Error. No mathematical verdict inferred from this failure.
- `msearch.py leanfinder`: "Termwise product of K-injective complexes represents
  product in derived category". Eight hits, including `IsKInjective`,
  `isKInjective_iff_rightOrthogonal`, and `IsKInjective.Qh_map_bijective`; none
  states the degreewise product theorem with both conclusions.
- `msearch.py loogle`: `CochainComplex.IsKInjective`. Twelve hits for the definition,
  bounded-below injective complexes, shifts, homotopy equivalences and Hom-complex
  coboundaries; no product theorem.
- `msearch.py grep`: `IsKInjective|isKInjective` under `Algebra/Homology`.
  Found Mathlib's predicate and comparison lemmas, not this product statement.
- `rg` in the source project and `lean/Sheaf` for KInjective and the node id;
  `grep -rn` of the node id in the whole source project found no tagged declaration.
  The project mentions this node in proof docstrings, but has no theorem for it.
- Read `WeilConjectures/Algebra/Homology/HomotopyCategory/Products.lean` in full:
  `HomotopyCategory.isLimitFanQuotient` gives only the homotopy product statement
  and assumes all products of the shape; `DerivedCategory.hasLimitsOfShape_discrete`
  gives existence of products and assumes K-injective resolutions. Neither has
  the exact node statement or identifies this particular termwise product in D(C).
- Name collision search in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures
  and `lean/Sheaf` for `termwise_product_isKInjective`, and product/K-injective
  combinations, found no existing declaration with the chosen full name.

Validation: server `scompile.py` compiled the final 56-line file cleanly in 1.4 s.
The first compile required writing `IsKInjective P.pt` explicitly because the cone
construction exposes `HomologicalComplex` rather than the cochain-complex alias
for field-notation resolution; no mathematical statement changed.
No disputed statement or node fault found. The theorem docstring carries all
three node proof steps with their named dependencies. No theorem is proved.


## Second reading by F1

Independent second reading with the sandbox node, its Lean file, all four statement
 dependency nodes and their declarations open. Verdict: the Lean says exactly what the
node says. No mathematical or syntactic mismatch found; no Lean or node change required.
Only this second-reading section was appended; the worker report is preserved.

Source checked independently: the actual Stacks `derived.tex`, downloaded into this
item's scratchpad from https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex,
section `section-K-injective`, definition `definition-K-injective`, and lemma
`lemma-product-K-injective` (Tag 0BK6, Lemma 13.31.5). Also checked the rendered tag at
https://stacks.math.columbia.edu/tag/0BK6. The section imposes no standing hypothesis
beyond an abelian category; in particular it does not assume enough injectives,
K-injective resolutions for arbitrary complexes, or exact products in the category.
The ringed-space wording of the title does not restrict the actual node or source.

Objects, hypotheses, and conclusions, listed before matching:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary abelian category A | `{C : Type u} [Category.{v} C] [Abelian C]` | Exact. Read `CategoryTheory.Abelian` in Mathlib: preadditivity, finite products, kernels/cokernels and normal monos/epis give precisely the dependency's abelian-category structure. |
| Arbitrary set T | `{T : Type t}` | Exact; t is independent of the other universes, and no nonempty/countable/finite instance is imposed. |
| Family of complexes I_t | `(I : T → CochainComplex C ℤ)` | Exact; `ComplexShape.up ℤ` is the unrestricted cochain convention, not bounded-below complexes. |
| Every I_t is K-injective | `[∀ s : T, (I s).IsKInjective]` | Exact. Read the bridge's `KInjectiveResolutionChoice.isKInjective` field and Mathlib's `IsKInjective.nonempty_homotopy_zero` field. This is null-homotopy of every map from an acyclic complex, precisely the source definition. The dependency's Hom-complex-acyclic formulation is equivalent by applying the degree-zero condition to every shift of an acyclic complex; no injectivity of individual terms is assumed. |
| Product of this family exists in each integer degree | `[∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)]` | Exact. Each evaluated discrete diagram has objects `(I s).X n`, and `HasProduct` abbreviates `HasLimit` of that discrete family. This does not demand other products. |
| The termwise product complex, with its projections | `let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)` | Exact. Opened the construction: `P.pt.X n` is the chosen degreewise limit, its differential is `limMap` of the factor differentials, and each projection has components `limit.π`. Choice of products does not alter the invariant statement. |
| The product complex is K-injective | `IsKInjective P.pt` | Exact first conjunct, using the same predicate as the factors. |
| Its image represents the product of the I_t in D(A) | `Nonempty (IsLimit (DerivedCategory.Q.mapCone P))` | Exact second conjunct. Read `Q`, `Functor.mapCone`, and the `IsLimit` fields `lift`, `fac`, `uniq`: these express existence and uniqueness of a map from every derived-category cone, commuting with these precise localized projections. `Nonempty` asserts the property without adding a choice of universal morphisms to the proposition. |
| D(A), under the dependency's size convention | `[HasDerivedCategory.{w} C]` and `DerivedCategory.Q` | Exact localization data at quasi-isomorphisms, as in `def-weil-abstract-derived-category`. Read `HasDerivedCategory.standard`: every abelian C has the standard choice at w = max u v. The arbitrary w binder permits every chosen localization universe; it does not impose a finiteness or resolution assumption. |

Dependency audit: opened the statements and records of `def-sp-abelian`,
`def-sp-kinjective-bridge`, `def-weil-abstract-derived-category`, and
`def-weil-category-product`. Read `Sheaf.CategoryTheory.KInjectiveBridge` in full:
the relevant shared notion is its Mathlib `IsKInjective` field, not the bounded-below
argument of its derived-functor definition. No boundedness, functor or resolution
choice from that separate definition leaks into this theorem. Read the Mathlib
product declarations `HasProduct`, `piObj`, `Pi.π`, `Pi.lift`, `Pi.map`, and the
cone universal property. There are no new nodes or delivered dependency modules to
review, and no missing notion, private definition, or unusable dependency record.
No statement correction is present or necessary, so the corrected-statement/citer
procedure does not apply.

Edge cases: empty T is allowed and yields the terminal/zero complex and empty
product in D(C); singleton T yields its sole factor up to the canonical isomorphism.
Zero factors and the zero category are admitted. Every integer degree, including
n = 0 and negative degrees, and unbounded complexes are covered. Categories with
only these particular degreewise products are covered. Empty schemes and all
characteristics are included when specializing to their abelian module categories;
there is no scheme, ring, field or characteristic restriction in the statement.
Explicit universes w, v, u, t cover arbitrary set size and independent morphism
size. No variable or universe is left unbound.

Independent searches, using different phrasing from the first worker:

- `msearch.py leansearch`: "Degreewise products of homotopically injective complexes
  compute products in the localization at quasi-isomorphisms". Service returned
  Internal Server Error; recorded unavailable, with no absence claim from it.
- `msearch.py leanfinder`: "An arbitrary family of homotopically injective complexes
  with degreewise products has a homotopically injective product". Eight hits:
  homotopy invariance/null-homotopy characterizations of `IsKInjective`, ordinary
  injective-object products, and mapping-cone injectivity; none states this lemma.
- `msearch.py loogle`: `"IsKInjective", "limit"`. Zero hits.
- `msearch.py grep`: `(product|limit|piObj).*(IsKInjective|isKInjective)|(IsKInjective|isKInjective).*(product|limit|piObj)`
  in Mathlib `Algebra/Homology`: zero hits.
- Independently ran case-insensitive `rg` with product/limit/piObj and K-injective
  combinations over Mathlib homology, `WeilConjectures`, and the repository's
  `lean/Sheaf`, plus exact declaration/node-id searches and the upstream-name index.
  Found upstream `HomotopyCategory/Products.lean` and project proof-docstring uses,
  but no existing declaration of this exact statement and no name collision.
  Read the upstream Products module in full: `isLimitFanQuotient` concerns only
  the homotopy-category product and assumes products for all families of the shape;
  `DerivedCategory.hasLimitsOfShape_discrete` additionally assumes K-injective
  resolutions and concludes existence, not the universal property of these exact
  termwise projections. Neither can replace the delivery with `existing: true`.

H5/H6/H8/H9 checks: the module contains one theorem with only `sorry` as proof and
no new definition, so no hollow data or proved helper. Both docstrings give Tag
0BK6 and the exact blueprint id. The theorem docstring carries all three proof
steps: acyclicity of the product Hom complex using exact products of abelian groups;
assembly of maps and homotopies to obtain the homotopy product; and K-injective
Hom comparison to obtain the derived product with the same projections. Namespace,
header, imports, topic path and line lengths follow the project conventions.
All three imports serve the degreewise construction, localization and recorded
K-injective convention respectively.

Validation: second-reader `scompile.py F1 lem-pc-ringed-space-product-kinjective`
compiled the sole delivered module successfully (exit code 0, 3.4 s; no warnings).
An exact string check confirms the node's `lean.statement` equals the signature
from `theorem` through the conclusion, excluding `:=`; all Lean lines are at most
100 characters. No mismatch was found, so the correct module and node were retained.
