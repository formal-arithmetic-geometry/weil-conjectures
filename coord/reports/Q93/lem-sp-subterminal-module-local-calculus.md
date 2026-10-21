## Worker report

The module `Sheaf.CategoryTheory.SubterminalModuleLocalCalculus` states
`SheafOfModules.SubterminalLocal.subterminal_module_local_calculus`, with a single
postponed theorem proof. Its docstring carries all nine DAG proof steps verbatim, wrapped
at 100 columns. All other declarations are transparent aliases of the recorded categories
and constructions, the canonical adjunction mate `nested`, or packages of this theorem's
clauses. They contain real data or explicit propositions; no data is supplied by `sorry`.
The node is unchanged except for `lean`. No new node, dependency repair, statement
correction, or statement dispute is needed.

Hypotheses and clauses, read against the final file:

- Small site: `C : Type c`, `[Category.{v} C]`, and `J : GrothendieckTopology C`.
  The site object and morphism universes remain independent. `[HasFiniteLimits C]`
  and `[J.Subcanonical]` state precisely the two site hypotheses. Coefficients and
  module values use `max c v r`, the recorded localized-system dependency's size
  convention; there is no equality between site universes. Small-site sheafification
  infrastructure is inferred from the imported library, rather than imposed as an
  additional hypothesis on the theorem.
- The commutative coefficient sheaf is `R : Sheaf J CommRingCat.{max c v r}`.
  `coefficients R` forgets commutativity using `sheafCompose` and `forget₂`.
  `Modules R` is exactly the recorded `ringedSiteModules (coefficients R)`;
  `SliceModules R Z` uses the literal ring restriction `(coefficients R).over Z`.
  All morphisms in these categories are module-linear.
- `U V : C` and the two instances `Mono (terminal.from U)` and
  `Mono (terminal.from V)` give the subterminals. `hcover` is membership of the sieve
  `Sieve.ofArrows (fun b : Bool ↦ if b then U else V) ...` in `J (⊤_ C)`.
  This is the sieve of the binary family, including repeated members. The theorem
  uses `U ⨯ V` and `prod.fst`, `prod.snd` for W and its canonical projections.
- `jstar`, `jbang`, and `adj` transparently abbreviate the recorded
  `localizedSystemRestriction`, `localizedSystemExtension`, and
  `localizedSystemAdjunction`. Thus the left adjoint is the actual direct-sum
  presheaf followed by module sheafification, with the actual section-normalized
  adjunction. It is not an unspecified map or a new extension functor.
- The middle conjunct ranges over all three objects Z = U, V, W. `ExactRestriction`
  supplies additivity, preservation of finite limits, and preservation of finite
  colimits for both `jstar R Z` and `jbang R Z`. These are exactness in the abelian
  module categories. Their adjoint relation is already the type of `adj R Z`.
- `PresheafFormula R Z` gives a subsingleton (zero) module when no map X → Z exists.
  If a map a exists, it supplies an isomorphism of R(X)-modules to
  `F.val.obj (op (Over.mk a))`, taking the direct-sum injection of x to x.
  Subterminality makes the indexing set empty or singleton. The restrictions and
  scalar actions are those of `extensionByZeroPresheafSection` and the recorded
  `extensionByZeroPresheaf`, not replacement formulas. By the definition of `jbang`,
  the sheafification of exactly this presheaf is the extension in the theorem.
- `Intersection.kU` and `.kV` are extensions from W to the U and V slices, with
  `.adjU` and `.adjV` adjoint to the literal `overMap` along the product projections.
  `.exactU`, `.exactV`, `.restrictionU`, and `.restrictionV` assert exactness on both
  sides. `.composeU`, `.composeV` and their unit equations identify the composite
  extension with `jbang R W` by the adjunction-compatible unique isomorphism.
  These adjunctions and normalizations determine the slice extensions up to the
  unique compatible isomorphism; no data definition selects an arbitrary functor.
- `.selfU` and `.selfV` give the two self-restriction identifications, whose inverse
  transformations are the actual adjunction units (`.selfU_unit`, `.selfV_unit`).
  `.exchangeU` and `.exchangeV` give the two cross-identifications in Lean's
  left-to-right functor-composition convention. Their unit and counit equations
  use `overFunctorMap` for relocalization and fix the canonical module-linear maps.
- `nested` is defined by transposing restriction of the unit under the recorded
  adjunction. `.nestedU_self`, `.nestedU_cross`, `.nestedV_self`, and `.nestedV_cross`
  give its commuting diagrams with both restrictions and the intersection
  comparisons. The two `.nested*_counit` equations give compatibility with the
  ambient counits, including the inclusions into the terminal subterminal.
- `SheafificationRestriction R Z` gives a natural restriction/sheafification
  isomorphism for Z = U,V,W, with equality on every original unit section.
  `MapSheafificationRestriction` and `.sheafificationU/V` give the same comparison
  within the slices. The scalar identification is the actual
  `Sheaf.pushforwardOverMapIso`, retaining its coefficient map.
- `JointDetection` gives iff tests for `IsZero` of every module, zero of every
  module map, and `ShortComplex.Exact`. Testing successive triples gives arbitrary
  sequences; inserting zero objects gives the endpoint mono/epi tests. Zero map
  detection permits testing sequences before their composite is known to vanish.
- `ExactRestriction.homology` is the natural H^q comparison on all unbounded
  cochain complexes, for every integer q. `DerivedExact` supplies the termwise
  localization-factorization isomorphism, triangulatedness, and the natural H^q
  comparison on the ordinary derived categories. It quantifies over the available
  exactness and derived-category instances; the required exactness is supplied by
  the adjacent `ExactRestriction` clauses. The localization universe w is explicit.
- `JointDetection` also tests degreewise vanishing and `QuasiIso` for every cochain
  complex and chain map. Its last two clauses give degreewise vanishing and
  isomorphism detection in the ordinary derived categories. There is no boundedness
  condition or assumption that the site has points.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent alias of Mathlib's `SheafOfModules` with its abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`, for the ordinary unbounded localization.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `overMap`, `overFunctorMap`; the underlying ring and
  site use `Sheaf.over` and `GrothendieckTopology.over`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `extensionByZeroPresheaf` and `extensionByZeroPresheafSection`, their direct-sum
  construction, module structures, semilinear restrictions and singleton/empty cases.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`, with identity
  coefficient maps. The helper `sheafify` is only an explicitly sized abbreviation.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: the actual
  `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`,
  the six exactness instances, `localizedSystemAdjunction_existsUnique`, and
  `localizedSystemAdjunction`. This is the normalized independent-site-universe
  interface of the recorded proof dependency.
- `Sheaf.CategoryTheory.ModuleSheafificationRestriction`:
  `PresheafOfModules.exists_moduleSheafificationRestrictionIso` and its normalization
  on unit sections, plus `restricted_sheafification_hom_ext`. Imported as a proof tool.
- Mathlib's `ShortComplex.PreservesHomology`, homological-complex homology functors,
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and their triangulated
  instances give the recorded exact-functor proof tools. The natural transformations
  are in actual module categories throughout.

Edge cases checked against the formulas: U = V = 1 (both self-comparisons become
identity), U = 1 (the other restriction is the nested restriction), repeated covering
members (Bool indexing allows them), empty overlap/disjoint subterminals (extension
from W is zero), objects only locally over an open (sheafification is retained before
identification), zero coefficient ring and zero modules, and unbounded complexes with
arbitrary positive or negative q. No nonempty-overlap or points hypothesis was added.

Searches run (the raw launcher search log is `searches.jsonl`):

- LeanFinder: “Restriction of extension by zero for sheaves of modules to two covering
  subterminal objects, intersection exchange and joint detection of exactness”:
  eight hits, including `GrothendieckTopology.MayerVietorisSquare.shortComplex_exact`
  and topological sheaf gluing. None states the module intersection and normalized
  adjunction compatibilities together with the joint exactness/derived tests.
- Loogle: `SheafOfModules.overMap, SheafOfModules.extensionByZeroPresheaf`:
  zero hits, with the diagnostic that the project presheaf name is unknown to its
  Mathlib index. The project declaration was located and read directly instead.
- LeanSearch: “Restriction of module extension by zero to covering subterminal
  intersections jointly detects exactness and quasi-isomorphisms”: eight hits on
  short-complex exactness/homology and a hypercover restriction, with no exact match.
- msearch grep: `overFunctor|overMap|extensionByZero` in
  `Algebra/Category/ModuleCat/Sheaf`: five hits in `PushforwardContinuous.lean`.
  These restriction declarations are reused. Direct rg over `lean/WeilConjectures`
  and `lean/Sheaf`, and grep for this item id in the upstream source, found no exact
  declaration. The parent's `ringedTopos_binary_descent` discusses these facts in
  its proof but states a gluing equivalence and a triangle, rather than this calculus.

The source passages read are Stacks 03DI (`lemma-extension-by-zero`), 03DJ
(`lemma-extension-by-zero-exact`), and 0F6Z (`lemma-restrict-back`) in
`literature/stacks-project/sites-modules.tex`, with 04B8 and the DAG's explicit
intersection/cover specialization. No repair note exists for this item. The prescribed
`CompactObject.lean` example is now withdrawn and empty; its current node points to the
upstream definition, and the current module conventions were followed.

The final file was compiled through scompile.py against the live published library,
both as a sandbox module and at its intended module path, without errors or warnings.

## Second reading by Q93

This is a separate self-review pass, not an independent-worker review: the dispatch
explicitly forbids starting other agents, and the maintainer will review independently.
With the final node and file open, I matched the small subcanonical finite-limit site,
commutative ring, subterminal arrows, binary covering sieve, and product intersection.
I then checked all three Z cases, empty/singleton module formulas, all four natural
identifications, the unit/counit normalizations, both restrictions of each nested map,
and the sheafification-unit equations. I checked source and target categories of each
comparison, in particular that kU/kV extend W → U/V and overMap restricts in reverse.

This pass found and repaired the interrupted draft's wrong cover predicate and missing
joint exactness/cohomology clauses, restored all normalization diagrams, and diagnosed
the sheafification helper's universe argument order rather than identifying independent
site universes. The final checks include zero-morphism detection before forming a short
complex, all integer cohomology degrees, and derived isomorphism detection. The node's
natural-language statement was not changed. The sole sorry belongs to the item's named
theorem, and its full proof plan is present in its docstring. No definition is hollow.
