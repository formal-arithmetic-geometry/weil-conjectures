## Worker report

Module: `Sheaf.CategoryTheory.FiniteProductFunctorLeftExact`.
Declaration: `CategoryTheory.finite_product_functor_left_exact`.
The single theorem has proof `by sorry`; no definition is introduced and nothing is proved.
The copied node changes only in `lean`. No correction, new node, or dependency module is needed.

Hypotheses and clauses, matched individually:

- Finite set I: `(I : Type u) [Finite I]`, without choosing an enumeration or requiring nonemptiness.
- Family of abelian categories: `(A : I → Type v) [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]`.
- Functors Γi to Ab: `(Γi : (i : I) → A i ⥤ AddCommGrpCat.{z})`.
- Each Γi additive: `[∀ i, (Γi i).Additive]`.
- Each Γi left exact: `[∀ i, PreservesFiniteLimits (Γi i)]`, the dependency's recorded Mathlib rendering.
- The product category: `∀ i, A i` with Mathlib's `CategoryTheory.pi` instance; objects are families and Hom is the dependent family of component Hom types, with coordinate identities and composition.
- The componentwise additive structure is supplied in the conclusion, not assumed: `∃ hPre : Preadditive (∀ i, A i)` followed by `∃ hEvalAdd : ∀ i, (Pi.eval A i).Additive`. Evaluation additivity forces `(f + g) i = f i + g i`, hence fixes the structure to the componentwise one. These are structural witnesses, not extra hypotheses. Explicit `letI` binders make their use in later types possible.
- Finite biproducts exist: `Nonempty (HasFiniteBiproducts (∀ i, A i))`. This includes the empty biproduct (zero object).
- Kernels exist: `Nonempty (HasKernels (∀ i, A i))`.
- Finite biproducts are computed componentwise: `∀ i, PreservesFiniteBiproducts (Pi.eval A i)` (inside the displayed conjunction). Evaluation takes the vertex, injections and projections of a biproduct to those of its ith component, so preservation expresses exactly the componentwise universal property, without imposing literal equality of noncanonical choices.
- Kernels are computed componentwise: `∀ i, ∀ (X Y : ∀ i, A i) (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (Pi.eval A i)`. A kernel is a limit of this diagram. Evaluation is additive and preserves zero, so the image diagram is the component's kernel diagram. No preservation of other colimits is asserted.
- Γ's object formula: `let Γ := Functor.pi Γi ⋙ Pi.functor I`. `Functor.pi` sends A to the family `(Γi i).obj (A i)`; `Pi.functor I` sends that family to its categorical product in Ab.
- Γ's morphism formula: the same composite uses `(Γi i).map (f i)` in each coordinate and then `Pi.map`, the product map induced by the coordinate maps.
- Γ is additive: `Γ.Additive`.
- Γ is left exact: `PreservesFiniteLimits Γ`. Between the stated preadditive categories with finite biproducts and kernels this is the standard equivalent form of additive preservation of kernels, as documented by the dependency's Mathlib match and `Functor.preservesFiniteLimits_of_preservesKernels`.

Dependencies read and used:

- `def-sp-abelian`: Mathlib match `CategoryTheory.Abelian`, module `Mathlib.CategoryTheory.Abelian.Basic` (imported by `Mathlib.Algebra.Category.Grp.Abelian`). Read the class docstring and full fields: Preadditive, normal mono and epi structures, finite products, kernels and cokernels. The same file supplies finite biproducts and zero objects.
- `def-sp-left-exact-additive`: its match explicitly lists one declaration per clause. Used `CategoryTheory.Functor.Additive` from `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and `CategoryTheory.Limits.PreservesFiniteLimits` from `Mathlib.CategoryTheory.Limits.Preserves.Finite`. Read their docstrings and signatures, and the kernel-to-finite-limits criterion in `Mathlib.CategoryTheory.Preadditive.LeftExact`. The match's primary `Functor.rightDerived` and `InjectiveResolution.isoRightDerivedObj` in `Mathlib.CategoryTheory.Abelian.RightDerived` were also read; those are the derived-functor clause of the dependency, which this item does not use.
- Existing helper notions: `Functor.pi` and `Pi.eval` in `Mathlib.CategoryTheory.Pi.Basic`, and `Pi.functor` in `Mathlib.CategoryTheory.Limits.Shapes.Products`; their definitions were read in full. `PreservesFiniteBiproducts` is imported from `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`.

Source: the local `literature/stacks-project/homology.tex` is absent on this machine. Read the authoritative source at https://stacks.math.columbia.edu/tag/060K instead: products of complexes of abelian groups have the product of their homologies. The node explicitly supplements it with componentwise product-category universal properties; the theorem docstring carries both proof steps and their dependency identifiers.

Edge cases checked before writing:

- I empty: the product category has its unique object and unique maps; its finite biproducts and kernels are that object. Γ is the empty product in Ab, i.e. the zero group, and is additive and left exact. Evaluation clauses are vacuous.
- I singleton: the assertion reduces to the given Γi up to the usual canonical isomorphisms.
- Zero morphisms: their kernel diagrams and evaluation maps are included, without requiring nonzero objects or maps.
- The empty biproduct is included by HasFiniteBiproducts and its preservation class.
- Index, object, Hom and coefficient universes are explicitly bound independently (`u v w z`); arbitrary finite sets are permitted even in a larger index universe than the coefficient groups. No auto-implicit variable is used.

Searches performed (real service searches recorded in `searches.jsonl`):

- LeanFinder via `msearch.py`: “The product of a finite family of additive left exact functors from abelian categories to abelian groups is additive and preserves finite limits”. Eight hits: additive functors preserve finite products, the additive/left-exact equivalence, exact products of abelian groups, and other general results; none states all clauses of this node.
- Loogle via `msearch.py`: `Functor.pi, PreservesFiniteLimits`. No hits; unknown identifier `Functor.pi` in the service index.
- LeanSearch via `msearch.py`: “finite product category abelian additive left exact componentwise product functors”. Service unavailable (Internal Server Error); no mathematical verdict inferred.
- Mathlib grep via `msearch.py`: `functor.*[Aa]dditive|preservesLimit|hasLimit|coneOfConeEval|bicone` in `CategoryTheory/Limits/Pi.lean`. Found componentwise cone assembly and its universal property, not the theorem. Additional query `Pi.functor|Functor.pi|piPreadditive` in `CategoryTheory` found the existing functor constructors and unrelated uses; no combined statement.
- Direct `rg` of the project's `lean/Sheaf` and upstream `WeilConjectures` for `finite.product|product.*left.exact|Functor.pi|piFunctor|Pi.*preserves`: found the already landed `Sheaf.CategoryTheory.DerivedFiniteProduct` (a stronger theorem with injective-resolution hypotheses, not this statement) and unrelated uses. Its formula for Γ agrees with this module.
- Direct item-id search in upstream `WeilConjectures`: no declaration tagged for this item.
- Direct declaration-name search `finite_product_functor_left_exact` in Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision before writing.

Validation: the initial server single-file compile succeeded without warnings; the final kernel-diagram version is compiled again and the required `deliver2.py --no-push` dry run is run before answering READY. The second reader supplies the independent reading and delivery.

## Second reading by M1

Independent reading of the node, both dependency nodes, the delivered module, and the
Mathlib declarations below. No mismatch found; the Lean and node record are unchanged.
Only this second-reading report is added.

Source checked: fetched the authoritative Stacks `homology.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex into
`scratchpad/homology-source.tex`. Read lines 7916–7933, including the section start and
`lemma-product-abelian-groups-exact` (060K); also read
https://stacks.math.columbia.edu/tag/060K. The section imposes no standing hypotheses:
it considers any set of complexes of abelian groups and identifies product homology.
The node expressly adds the product-category universal-property formulation and restricts
its index to finite sets. Its supplied formulation is valid, without additional assumptions.

Objects, hypotheses, and conclusions, item by item (all PASS):

1. A finite set I: `(I : Type u) [Finite I]`. No chosen enumeration or nonemptiness.
2. For every i an abelian category A_i: `(A : I → Type v)` with
   `[∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]`. Read `Abelian.Basic` lines
   103–120: preadditivity, normal monomorphisms/epimorphisms, finite products,
   kernels and cokernels give precisely `def-sp-abelian`, including zero objects
   and finite biproducts. There are no injective-resolution hypotheses.
3. Functors Γ_i : A_i → Ab: `(Γi : (i : I) → A i ⥤ AddCommGrpCat.{z})`.
   Each is additive: `[∀ i, (Γi i).Additive]`. Read `Functor.Additive`'s
   `map_add` signature, and the finite-product/additivity equivalence named in
   `def-sp-left-exact-additive`; these are the same notion between abelian categories.
4. Each Γ_i is left exact: `[∀ i, PreservesFiniteLimits (Γi i)]`.
   Read `Limits.Preserves.Finite` lines 40–55 and `Preadditive.LeftExact`
   lines 105–125. For additive functors on abelian categories this is exactly
   preservation of kernels as specified by `def-sp-left-exact-additive`, with no
   additional hypothesis. The dependency's derived-functor clause is unused here.
5. Product category, family objects and family morphisms: `∀ i, A i`.
   Read `Pi.Basic`'s `pi` instance: Hom is `∀ i, X i ⟶ Y i`, identities and
   composition are coordinatewise. This is the node's category, without a replacement.
6. Its componentwise additive structure: the conclusion supplies
   `∃ hPre : Preadditive (∀ i, A i)` and `∃ hEvalAdd : ∀ i, (Pi.eval A i).Additive`.
   Read `Pi.eval`'s object and map fields. Additivity says
   `(f + g) i = f i + g i`; function extensionality fixes addition, hence zero
   and the additive group structure, to the componentwise one. These witnesses
   supply structure implicit in the node, and impose no extra input hypothesis.
7. Finite biproducts exist: `Nonempty (HasFiniteBiproducts (∀ i, A i))`.
   Read the class's `∀ n, HasBiproductsOfShape (Fin n)` field, including n = 0.
8. Kernels exist: `Nonempty (HasKernels (∀ i, A i))`.
   Read the class in `Limits.Shapes.Kernels`: limits of `(f, 0)` for every morphism.
9. Both are computed componentwise: for every i the conclusion asserts
   `PreservesFiniteBiproducts (Pi.eval A i)` and, for every X, Y and f,
   `PreservesLimit (parallelPair f 0) (Pi.eval A i)`.
   Read `PreservesFiniteBiproducts` and its finite-shape field. Evaluation preserves
   zero by the additive witness, so the latter diagram is exactly the component
   kernel diagram. Preservation specifies the componentwise universal properties,
   without imposing equality on arbitrary choices of representing objects.
10. Γ on objects: `let Γ := Functor.pi Γi ⋙ Pi.functor I`.
    Read `Functor.pi` in `Pi.Basic` and `Pi.functor` in `Limits.Shapes.Products`
    lines 1008–1013: its value is the categorical product of `(Γi i).obj (X i)`.
11. Γ on morphisms: those same definitions first map each `f i` by `Γi i` and
    then apply `Pi.map`. This is exactly the node's product of component maps.
12. Γ additive and left exact: `Γ.Additive ∧ PreservesFiniteLimits Γ`, under
    the supplied componentwise structure. As for the hypotheses, left exactness
    is equivalent to additive kernel preservation. Every quantifier has the
    node's order: family and functors first, structural witnesses afterward,
    then evaluation assertions for all indices and morphisms.

Edge cases: empty I gives the terminal family category and Γ the zero group functor;
evaluation assertions are vacuous and the unique Hom group has its unique additive
structure. A singleton reduces to the component statement up to canonical isomorphism.
The zero object, zero morphism and empty biproduct are included. There is no scheme,
characteristic, or cohomological-degree parameter here; no such restriction is introduced.
All four universes u, v, w, z are explicitly bound and independent. Read the higher-universe
finite-limit preservation instance in `Preserves.Finite`; the low-universe class encoding
does not exclude finite shapes in higher universes. Finite biproduct shapes similarly
transport along equivalences with Fin n. No variable or universe is left auto-implicit.

Independent searches (different wording from the worker; service calls recorded in
`searches.jsonl`):

- LeanFinder: "dependent product categories evaluation preserves kernels biproducts
  product functor additive left exact". Eight hits, including
  `preservesBinaryProducts_of_preservesKernels` and biproduct/product preservation
  criteria; none states all the node's clauses.
- Loogle: `CategoryTheory.Pi.eval`. Twelve hits: evaluation, its formulas, coordinate
  extensionality and comparison isomorphisms; no combined theorem.
- LeanSearch: "The functor taking a family of abelian group valued additive functors
  to their finite product preserves kernels and is additive". Internal Server Error;
  recorded as unavailable, without drawing a mathematical conclusion.
- `msearch.py grep`: `PreservesFiniteLimits|Preadditive|HasFiniteBiproducts` in
  `CategoryTheory/Limits/Pi.lean`: no hits. Independently read that entire module's
  cone-assembly and `hasLimit_of_hasLimit_comp_eval` declarations: general componentwise
  limit construction, not this combined assertion.
- Direct `rg` in Mathlib category theory and abelian groups, upstream WeilConjectures,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`, using `piPreadditive`,
  `Pi.functor`, `Functor.pi`, `product.*[Ll]eft[Ee]xact`, `product.*left_exact`, and the
  proposed declaration name. Existing product constructors are used. Read the landed
  `DerivedFiniteProduct.lean` in full: it assumes component injective resolutions and
  concludes a derived-functor comparison, so it is not an existing statement of this node.
  No name collision or duplicate definition was found.

No new node, dependency module, or statement correction is present or needed. The theorem
is only `by sorry`; no definition or proof was added. Both docstrings identify the source
and blueprint node, and the theorem docstring follows both recorded proof steps with their
dependency identifiers. Imports use the existing notions; namespace and file conventions
are respected. The node's `lean.statement` was checked against the full file signature.
