## Worker report

The module `Sheaf.Paper.EtaleOriginDerivedCategory` states
`AlgebraicGeometry.ProEtale.EtaleOriginDerivedCategory` and its forgetful/restriction
constructions. It uses the retained witness rather than replacing the object by an
existence predicate. The only new postponed theorem is
`etaleOriginForgetfulPlus_essImage`, which is the essential-image clause explicitly
included in this definition node. Its docstring gives the complete elementary proof:
compose the existing witness isomorphism with the essential-image isomorphism, and
use the identity isomorphism in the reverse direction. All definitions contain real
data, and every theorem proof in this delivery is `sorry`.

Sources read: the item and every direct statement-dependency node; the source files
listed below, including the full signatures and docstrings of the constructions used;
Mathlib `InducedCategory.lean` and `EssentialImage.lean`; upstream
`WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean` (the exact
bounded-below restriction and its compatibility); upstream derived comparison
`Comparison.lean` (the competing essential-image predicate). The blueprint source files
were absent from this machine's literature mirror, so I read the exact two blueprint
files on the project server: `def-weil-compact-support-candidate.md`, order 1472, and
`def-weil-pbc-etale-origin-witness.md`, order 1289. The former refers to the full
subcategory together with witnesses, and the latter explicitly retains `(L, alpha)`.
For the dependency, I also opened [Stacks Tag 015F](https://stacks.math.columbia.edu/tag/015F)
and [Tag 099R](https://stacks.math.columbia.edu/tag/099R): exact inverse image is applied
termwise, without an injective resolution.

Clause-by-clause rendering:

- An arbitrary scheme `T` is `(T : Scheme.{u})`, with no Noetherian, finite type,
  affine, nonempty, or other restriction.
- A finite discrete commutative ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]`. There is no `Nontrivial Λ` hypothesis.
  The p-adic rings are an example, not a restriction on coefficients, so no prime,
  extension field, or level binder is imposed. The recorded coefficient-extension
  module is imported for this example; its ring and positive-level finiteness were read.
- `D(T_proet, Λ)` is the recorded `FiniteCoefficientDerivedCategory T Λ`, and
  `D^+(T_proet, Λ)` is `FiniteCoefficientDerivedCategoryPlus T Λ`. These use the
  coefficient sheafification of continuous functions on connected components,
  `ringedSiteModules`, and the standard derived localization. This is the precise
  encoding used by the recorded witness, not a replacement category of fixed-ring
  pro-etale sheaves. Its agreement with constant coefficients is already expressed
  by the recorded scalar map and canonical realization in the dependency module.
- `D^+(T_et, Λ)` is the recorded `DerivedCategory.Plus
  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, the six-functor encoding named
  in `def-weil-pbc-derived-categories`. Both plus categories use the standard
  cohomological bounded-below condition, with an arbitrary integer lower bound.
- The termwise comparison is the existing `finiteCoefficientComparison T Λ`;
  its unbounded derived functor is `finiteCoefficientDerivedComparison T Λ`.
  The supplied dependency `finiteCoefficientDerivedComparisonPlus T Λ` is exactly
  `(finiteCoefficientComparison T Λ).mapDerivedCategoryPlus`. The witness's existing
  `alpha` uses this same expression, definitionally.
- The triple `(K,L,alpha)` is encoded by
  `Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K`.
  The second component has actual fields `L` and `alpha : nu^* L ≅ K`; it is not
  truncated to a proposition. Commutativity is required at this item's outer binders,
  while the reusable witness permits all finite rings.
- The category is `InducedCategory (FiniteCoefficientDerivedCategoryPlus T Λ)
  (fun P => P.1)`. Its morphisms are all ambient morphisms on the `K`s, with the
  ambient identity and composition, by Mathlib's `InducedCategory.Hom` and category
  instance. The bounded-below category is full in the unbounded category. There is
  no additional morphism on `L`, no commuting-square requirement, and no dependence
  of Hom on the chosen `alpha`.
- `etaleOriginForgetfulPlus` is exactly `inducedFunctor (fun P => P.1)`.
  `etaleOriginForgetfulPlusFullyFaithful` supplies its full-faithfulness data directly
  from `fullyFaithfulInducedFunctor`; nothing is newly proved.
- The essential-image clause is the statement
  `(etaleOriginForgetfulPlus T Λ).essImage K ↔ Nonempty (EtaleOriginWitness T Λ K)`.
  This is existence only for the class of image objects, while the category objects
  still retain the full witness.
- `etaleOriginForgetful` composes this functor with `DerivedCategory.Plus.ι`, giving
  the full embedding into the unbounded category; `restrictToEtaleOrigin T Λ F`
  is exactly `etaleOriginForgetful T Λ ⋙ F`, for any target category and functor `F`.
  Explicit universes `v,w` on that target impose no equality between object and Hom
  universes. All site/coefficient conventions are those of the recorded dependencies.

Dependency declarations used (including the transitive import path):

- `Sheaf.Paper.EtaleOriginWitness`: `AlgebraicGeometry.ProEtale.EtaleOriginWitness`,
  with its actual `L` and `alpha` fields; confirmed again with `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientDerivedCategory`,
  `FiniteCoefficientDerivedCategoryPlus`, `finiteCoefficientComparison`, its additive
  and finite-limit/finite-colimit instances, and `finiteCoefficientDerivedComparison`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, via the finite-coefficient import:
  the recorded `DerivedCategory.Plus` of etale `ModuleCat` sheaves. The underlying
  module encoding is `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, via the finite-coefficient import:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`, and the
  upstream `comparisonUpperStar` used by `finiteCoefficientComparison`; the small site
  is Mathlib `Scheme.ProEt`/`Scheme.ProEt.topology`, also imported through the recorded
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` dependency.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing` and `Padic.finite_coefficientExtensionRing`, for
  the finite coefficient example only.
- `Mathlib.CategoryTheory.InducedCategory`: `InducedCategory`, `inducedFunctor`,
  `fullyFaithfulInducedFunctor`, for `def-sf-induced-category` (a Mathlib leaf).
- `Mathlib.CategoryTheory.EssentialImage`: `Functor.essImage`.
- `Sheaf.Paper.ComparisonDerivedPullback`: `finiteCoefficientDerivedComparisonPlus`;
  it uses upstream `CategoryTheory.Functor.mapDerivedCategoryPlus`, and the existing
  unbounded functor uses Mathlib `Functor.mapDerivedCategory`, the leaf
  `lem-sf-exact-functor-derived-triangulated`. No module is fabricated for that leaf.

Edge cases checked before writing: the empty scheme is allowed, as is the zero ring
and the zero complex, since there is no nonemptiness or nontriviality assumption. Any
integer cohomological lower bound is allowed by `DerivedCategory.Plus`. Two different
witnesses on the same `K` remain different stored objects and still have the underlying
identity as an isomorphism in the induced category. An arbitrary morphism between the
underlying `K`s is allowed regardless of its effect on the witnesses, exactly as in
the node. An object with no witness contributes no sigma object. No independent small
universe is imposed on the sites, and the recorded `u+1` coefficient encoding covers
arbitrary finite coefficients by the standard lift convention. The apparent word
"subcategory" does not assert literal injectivity of the object-forgetting map: the
node expressly says the witness-retaining category is regarded through a fully faithful
functor, which is what is defined.

Searches actually run, using `msearch.py Q19 def-sf-etale-origin-subcategory`:

- LeanFinder, query "The induced category of bounded below pro-etale complexes equipped
  with an etale origin witness retains the etale complex and an isomorphism from its
  comparison pullback": eight hits about etale schemes and ring maps; none about the
  derived category retaining a witness.
- LeanSearch, query "induced category retaining an etale origin witness for a bounded
  below pro-etale complex": unavailable (HTTP Internal Server Error), recorded by the
  search wrapper as unavailable, not as a negative result.
- Loogle, query `InducedCategory, inducedFunctor`: no usable hit (unknown identifier).
  Retried with `CategoryTheory.fullyFaithfulInducedFunctor`: one exact hit for the
  general categorical construction, which is reused.
- Grep, query `EtaleOrigin|etaleOrigin|plusEtaleOrigin|InducedCategory`, under
  `CategoryTheory`: general induced-category uses; no etale-origin category.
- Grep, query `etale.?origin|EtaleOrigin|pro.?etale|ProEtale`, under
  `AlgebraicGeometry/Sites`: small pro-etale site and ell-adic cohomology; no witness
  retaining derived category.
- Local `rg` over both source checkouts and `lean/Sheaf`, by the item id, names
  `EtaleOriginDerivedCategory`, `EtaleOriginCategory`, and
  `finiteCoefficientDerivedComparisonPlus`, and concept patterns
  `etale.?origin|origin.?subcategory|coming from the etale`: no item declaration.
  It found upstream `DerivedCategory.plusEtaleOrigin`, whose full signature and
  docstring were read: it is only an object property in the fixed-ring encoding,
  discarding the witness; it does not define the node's category of triples.
  It also found the recorded witness and unbounded finite-coefficient comparison,
  both reused. The declaration-name index has no conflicting name. A direct node-id
  search in the upstream Lean source likewise found no occurrence.
- `scompile.py --source Sheaf.Paper.ComparisonDerivedPullback` found no current server
  module of that name. I also inspected the server delivery branch
  `deliver/Q33/def-sf-comparison-derived-pullback` (54a9035933cd): it is a stage-1
  split with no `lean` record, so there is no delivered Lean interface to reuse.
  The current shared DAG likewise has no Lean record for this genuine prerequisite;
  its definition is supplied here using the existing finite-coefficient APIs.

No statement correction or disputed statement is needed. No new DAG node is added.

## Dependency modules

`def-sf-comparison-derived-pullback` is an existing genuine dependency node with no
usable Lean record (`lean: null`, no Mathlib match). Under the human's "nothing waits"
instruction it is supplied in this delivery with only its `lean` field changed.
`Sheaf.Paper.ComparisonDerivedPullback` reuses the already recorded unbounded
`finiteCoefficientDerivedComparison` and supplies its bounded-below restriction
`finiteCoefficientDerivedComparisonPlus`, the actual termwise exact module inverse
image in the same coefficient-ring encoding as the witness. The existing
`finiteCoefficientComparison` instances and generic exact-derived API provide
exactness, commutation with cohomology, and preservation of lower bounds needed for
this definition; the unstated general comparison-exactness theorem is not replaced
by a new assumption. No extra theorem or proof is required in this dependency module.
The module and declaration docstrings name Tags 015F and 099R and the dependency id.

## Validation

Both delivered modules compile separately through `scompile.py`, in dependency order,
under the prescribed local side overlay, with the expected essential-image `sorry`
and no errors or warnings. All definition data are real constructions. The node copies
preserve every original field except `lean`; signatures are taken verbatim from the
files, and the record date is the UTC date. The first delivery dry run compiled the files and found one record error: its
`lean.declarations` list included the imported unbounded project declaration. The list
is corrected to contain only the declaration owned by the dependency module; the
imported unbounded functor remains identified in `lean.note` and this report. The
independent second-reading section is intentionally left to the second reader. The
required repaired delivery dry run follows.

## Second reading by Q19

I read the item node, its source-place description, the retained-witness dependency, the
finite-coefficient pro-etale module, the derived-category dependency, the comparison-site
node, and the Mathlib `InducedCategory` and `Functor.essImage` declarations. The node's
objects and clauses match the delivered Lean as follows.

- `T` is the unrestricted `Scheme.{u}` binder in every declaration; no Noetherian,
  finiteness, affine, separated, or nonempty hypothesis is added.
- `Λ` is a finite discrete commutative ring, rendered by
  `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`, `[TopologicalSpace Λ]`, and
  `[DiscreteTopology Λ]`. The optional coefficient-extension example is only mentioned
  by the node and is not made a hypothesis.
- `D(T_proet, Λ)` and its bounded-below subcategory are exactly
  `FiniteCoefficientDerivedCategory T Λ` and
  `FiniteCoefficientDerivedCategoryPlus T Λ`; these are the recorded continuous-function
  coefficient sheaf and standard derived localization.
- `D^+(T_et, Λ)` is the node's
  `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- The comparison pullback is the recorded `finiteCoefficientDerivedComparisonPlus T Λ`,
  supplied by the dependency module as the canonical `mapDerivedCategoryPlus` restriction
  of `finiteCoefficientComparison`; no arbitrary functor or extra exactness assumption is
  introduced.
- A retained witness is the existing `EtaleOriginWitness T Λ K`, whose fields are the
  bounded-below étale object `L` and the comparison isomorphism `alpha`. The category's
  objects are precisely `Σ K, EtaleOriginWitness T Λ K`.
- `EtaleOriginDerivedCategory` is Mathlib's `InducedCategory` along the projection to
  `K`. Thus its morphisms, identities, and composition are exactly the ambient pro-etale
  morphisms, with no witness map or compatibility square.
- `etaleOriginForgetfulPlus` is Mathlib's `inducedFunctor`; the accompanying named
  theorem supplies full faithfulness. `etaleOriginForgetfulPlus_essImage` states the
  node's exact essential-image equivalence with `Nonempty (EtaleOriginWitness ...)`.
- `etaleOriginForgetful` is the composite with `DerivedCategory.Plus.ι`, and
  `restrictToEtaleOrigin` is precomposition by that forgetful functor into an arbitrary
  target category with independent object and morphism universes.

Edge cases checked: empty schemes, the zero finite ring, zero complexes, arbitrary lower
cohomological bounds (including no fixed bound), multiple witnesses on one `K`, objects
without witnesses, and arbitrary ambient morphisms all remain covered. No index type,
characteristic, nontriviality, or universe equality is silently imposed.

The existing-search results were rechecked by grep and Lean search tooling recorded in the
worker report; the only nearby upstream declaration, `DerivedCategory.plusEtaleOrigin`, is
an object property and discards the retained witness, so it is not this notion. Mathlib's
`InducedCategory` and `Functor.essImage` are used directly for the categorical construction.

I found one delivery issue: the worker imported the finite coefficient extension module
only for the node's parenthetical example, but the imports are intentionally retained so
that this mentioned recorded coefficient construction remains available. No statement,
object, hypothesis, or conclusion mismatch was found. I restored that import after a
minimal compilation experiment, and both sibling files compile cleanly with `scompile.py`.
