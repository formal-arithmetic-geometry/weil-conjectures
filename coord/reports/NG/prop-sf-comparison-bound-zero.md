## Worker report

The delivery states `AlgebraicGeometry.ProEtale.comparison_bound_zero` in
`Sheaf.Paper.ComparisonBoundZero`. Its sole proof is `sorry`. It defines no new
category, coefficient object, predicate, or comparison map. The node changes only
in `lean`; no statement correction or dependency repair is needed.

The blueprint statement and proof were read at
`literature/blueprint/master/blueprint/sec-smooth-purity/`
`sk-prop-sf-fullcd-etale-origin/prop-sf-comparison-bound-zero.md` in the available
literature checkout, together with the unit's `_section.md`. Stacks
`proetale.tex`, `lemma-fully-faithful` (099T) and `lemma-relative-comparison` (099V)
confirm that the scheme and sheaf are arbitrary. The DAG's five proof steps
correctly include the independent acyclicity argument; ordinary full faithfulness
alone is not used to infer derived vanishing. All five steps, including the
module-to-abelian transfer, are recorded in the declaration docstring.

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| Any scheme X | `(X : Scheme.{u})`; no further instance or property of X. |
| A finite discrete commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`. The fixed-coefficient category treats A as discrete, with no topological-ring input. |
| Small étale and pro-étale sites | `X.smallEtaleTopology` and `Scheme.ProEt.topology X`, the recorded sites. |
| Modules over the constant sheaves on these sites | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)`, the fixed-coefficient presentation explicitly sanctioned by the comparison node and the note of `def-weil-pbc-etale-sheaves`. |
| The specified inverse and direct images | `comparisonUpperStar (ModuleCat.{u + 1} A) X` and `comparisonLowerStar (ModuleCat.{u + 1} A) X`. Their definitions are left Kan extension followed by sheafification, and restriction along `Scheme.toProEt X`. |
| The actual adjunction unit is an isomorphism | `IsIso ((X.proEtaleSiteComparisonModules A).unit.app G)`, for every G. This is the recorded module adjunction's unit, not an arbitrary isomorphism of objects. |
| Right derived functors computed by injective module resolutions | `(comparisonLowerStar ... X).rightDerived q`, Mathlib's `Functor.rightDerived`. It is defined by applying the functor to `injectiveResolutions` and taking homology. The enough-injectives and injective-resolution instances are inferred from the existing Grothendieck sheaf-category instances. |
| R^q nu_* (nu^* G) = 0 for q > 0 | The first conjunct universally quantifies G and has `∀ q : ℕ, 0 < q → IsZero (((comparisonLowerStar ... X).rightDerived q).obj ((comparisonUpperStar ... X).obj G))`. |
| No constructibility or finiteness on G | G is an arbitrary object of the étale module sheaf category. No such predicate occurs. |
| No Noetherian or dimension restriction on X | No such binder occurs; q is compared only with zero. |
| Every F isomorphic to some nu^* G has the same vanishing | The second conjunct quantifies arbitrary pro-étale F with `(comparisonUpperStar ... X).essImage F` and concludes positive `rightDerived` vanishing. The recorded Mathlib definition expands to `∃ G, Nonempty (nu^* G ≅ F)`. It is a property, not a selected witness. |
| The bound is M = 0 independently of dimension | Both clauses use exactly `0 < q`; the same theorem works for every X without any dimension parameter. |
| The finite-field / ell-adic coefficient application | Instantiate A with `ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)`. `Padic.finite_coefficientExtensionRing l E n hn` supplies finiteness for `hn : 1 ≤ n`, and `ULift` preserves it and the commutative ring. The general scheme quantifier includes every finite-type scheme over the stated algebraic closure. The origin witness of `def-sf-fullcd-used-class` is exactly the final conjunct's `essImage` hypothesis. No finite-field condition is necessary for the universal theorem, so the application is a direct specialization rather than an additional assumption. |

In the constant-ring presentation, a constant scalar acts on every section,
compatibly with restriction. Conversely, locally constant scalar sections act by
gluing these constant actions. This is the same module notion as
`ringedSiteModules` / `SheafOfModules`; no new definition is made here. The
comparison dependency already records its adjunction in this ModuleCat-valued
presentation, and that exact declaration is used. The larger common coefficient
universe is the recorded site convention. It does not equate the object and
morphism universes of the sites. Any smaller finite coefficient ring can be
lifted as above.

The statement dependencies and declarations read and used are:

| Node | Module and declarations |
| --- | --- |
| `def-weil-pbc-constant-sheaf` | `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`. Its full construction is the constant presheaf followed by sheafification. |
| `def-weil-sheaf-of-modules-category` | `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`; read also Mathlib's structure and linear morphisms. This is the intrinsic interpretation of the sanctioned fixed-coefficient category, not a copied category. |
| `def-weil-pbc-etale-site` | `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`, with `Scheme.Etale` and the jointly-surjective cover criterion. |
| `def-weil-pbc-proetale-site` | `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `Scheme.proEtaleDerivedCategory`; read its constant-ring `SheafOfModules` expression. The present statement needs its underlying site and module category, not its derived-category abbreviation. |
| `def-weil-pbc-site-comparison-morphism` | `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`; also read `proEtaleSiteComparison`, `preservesFiniteLimits_proEtaleSiteComparison`, and the exact definitions of `ProEtale.comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction` in `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`. |
| `def-sp-left-exact-additive` | `Mathlib.CategoryTheory.Abelian.RightDerived`, `CategoryTheory.Functor.rightDerived` and `InjectiveResolution.isoRightDerivedObj`; the direct image is additive and left exact as the recorded restriction right adjoint. |
| `def-sp-injective-resolutions` | `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`, `CategoryTheory.Injective`, `CategoryTheory.InjectiveResolution`; `Mathlib.CategoryTheory.Abelian.Injective.Resolution` supplies resolution existence from enough injectives. |
| `def-weil-pbc-etale-sheaves` | `WeilConjectures.AlgebraicGeometry.EtaleSheaves`; read the recorded predicates and module-category note. The statement uses arbitrary sheaves, not its local-constancy or constructibility predicates. |
| `def-sf-fullcd-used-class` | `Mathlib.CategoryTheory.EssentialImage`, `CategoryTheory.Functor.essImage`, specialized to the recorded comparison inverse image exactly as its `mathlib_match` says. |
| `def-weil-l-adic-coefficient-extension` | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`, and the imported actual construction `Padic.coefficientExtensionRing`; this identifies the final application. |

Every available proof-dependency module is imported, without `public` when used
only by the future proof. The enough-injectives module and the existing
Grothendieck sheaf-category module are public because their instances are needed
to elaborate the signature itself. No proof import was omitted for a cycle.

Searches for an existing full statement:

- `msearch.py` LeanFinder: "The unit from an arbitrary etale sheaf of finite ring modules to the proetale comparison pushforward pullback is an isomorphism and every positive higher comparison direct image vanishes". Eight results concern generic pullbacks, pushforward isomorphisms and condensed discrete modules; none is this comparison statement.
- `msearch.py` Loogle: `CategoryTheory.Functor.rightDerived, CategoryTheory.Functor.essImage`. Zero results for that combined pattern. Both separate declarations were found and read directly.
- `msearch.py` grep in Mathlib AlgebraicGeometry: `proetale.*(acyclic|comparison)|comparison.*proetale`. Zero results.
- `msearch.py` LeanSearch: "Higher direct images of the proetale comparison vanish on etale origin module sheaves". The service returned Internal Server Error; no mathematical verdict is inferred from it. The other search kinds succeeded.
- Source `rg` / node-id search in the pinned `WeilConjectures` tree, and `rg` in `lean/Sheaf`, found no exact conjunction of the current node's clauses.
- The newer read-only `lean/WeilConjectures` tree does contain `ProEtale.isIso_comparisonAdjunction_unit` in `Comparison.FullyFaithful` and `ProEtale.isZero_homology_rightDerivedComparisonLowerStar` in `FullCohomologicalDimension`. Their full signatures and docstrings were read. The former states the underived unit only; the latter states vanishing as positive homology of the unbounded derived functor on the literal inverse image only, without the unit or the whole essential-image clause. Neither is an exact declaration of the present node. This delivery introduces no new notion; its single statement records the requested conjunction using the recorded injective-resolution `rightDerived` and existing `essImage`.
- Name searches for `comparison_bound_zero` / `comparisonBoundZero` in Mathlib, the pinned upstream tree, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

Edge cases checked before the final statement:

- The empty scheme is included; no point, nonempty cover, or dimension is selected.
- The zero coefficient ring is included; no `Nontrivial A` assumption occurs.
- The zero sheaf and arbitrary infinite-stalk / nonconstructible étale module
  sheaves are included; no `Finite`, finite generation, or constructibility is
  imposed on G or F.
- q = 0 is excluded only from the vanishing assertion. The degree-zero assertion
  is the actual unit isomorphism, as required. All positive natural degrees,
  including q = 1, are covered. Negative degrees are not part of the stated
  injective-resolution derived functors.
- The final finite-stage application uses n ≥ 1 precisely where coefficient
  finiteness is supplied. The general theorem itself also includes the zero-ring
  case without imposing such a stage parameter.
- The final essential-image condition allows every isomorphic copy and needs
  no chosen G or chosen isomorphism as additional structure.

No `STATEMENT-DISPUTED` issue was found in the current DAG statement. The
blueprint's old phrase identifying étale-origin sheaves with constructible
sheaves is not reintroduced; the current coefficient-class node has already
removed that identification.

Validation: `scompile.py NG prop-sf-comparison-bound-zero` compiles this module
both under its sandbox name and its library name without errors or warnings,
under the prescribed per-file limit. During elaboration, public imports of the
existing enough-injectives / Grothendieck sheaf-category instances were needed
for the public signature; no mathematical hypothesis was added to resolve this.
The independent second reader writes the second-reading section and delivers.

## Second reading by NG

I independently read the current DAG node, its sandbox copy and the entire
`lean/Sheaf/Paper/ComparisonBoundZero.lean`, then the dependency records and
signatures. Verdict: the Lean states the node exactly in the project's recorded
fixed-coefficient presentation. No mathematical mismatch was found, and I have
left the Lean module and node record unchanged. This section records my reading;
it does not rely on the first worker's claimed validation.

Source check: I opened the archived blueprint statement, its five-paragraph proof
and its unit `_section.md` in the launcher's literature checkout. I also read
`proetale.tex`, the opening of Comparison with the etale site, and the statements
and proofs at labels `lemma-describe-pullback-from-etale` (0GLZ),
`lemma-fully-faithful` (099T), and `lemma-relative-comparison` (099V). Their scheme
is arbitrary. The unit statement is for every etale sheaf; the derived statement
is for every abelian sheaf, or bounded-below complex, with no constructibility,
Noetherian, separation or dimension hypothesis. The unit's proper finite-type
setting concerns its separate pushforward theorem, not this absolute comparison
lemma. The current DAG supplies the scalar/module transfer explicitly; all five
of its proof steps are retained in the Lean docstring. In particular, step 2
uses acyclicity of pulled-back injectives, not just ordinary full faithfulness.
The old blueprint's constructibility wording is not an additional hypothesis:
the current `def-sf-fullcd-used-class` defines precisely the essential image.

Here is my object/hypothesis/conclusion inventory and item-by-item match.

| Node object, hypothesis or clause | Lean rendering and verdict |
| --- | --- |
| Any scheme X | `X : Scheme.{u}`. Exact; no geometric-property instance is assumed. |
| A finite discrete commutative coefficient ring A | `A : Type (u + 1)` with `[CommRing A] [Finite A]`. Exact. These are discrete coefficients, not condensed or continuous modules; no field or nontriviality condition is imposed. |
| Small etale and pro-etale sites of this same X | `X.smallEtaleTopology` and `Scheme.ProEt.topology X`. Exact. I read the Mathlib definitions: etale objects in the former, weakly etale objects with the pro-etale/fpqc topology in the latter. |
| Modules over the constant A sheaf | `Sheaf ... (ModuleCat.{u + 1} A)` on both sites. Exact in the sanctioned six-functor encoding. The record of `def-weil-pbc-etale-sheaves` explicitly permits this presentation alongside `SheafOfModules`; the theorem does not introduce another definition. Constant scalar actions extend to locally constant scalar sections by sheaf gluing, as the node's step 1 explains. |
| Canonical comparison inverse/direct image | `comparisonUpperStar (ModuleCat.{u + 1} A) X` and `comparisonLowerStar (ModuleCat.{u + 1} A) X`. Exact. I read their bodies in `Comparison.Defs`: Kan extension then sheafification, and restriction along `toProEt X`, respectively. They are not arbitrary maps or functors. |
| Every etale A-module sheaf G | `∀ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`. Exact; no condition on stalks, finite generation or constructibility. |
| The adjunction unit G to nu_* nu^* G is invertible | `IsIso ((X.proEtaleSiteComparisonModules A).unit.app G)`. Exact. I opened `ProEtaleSiteComparison.lean`: this adjunction is definitionally the recorded `comparisonAdjunction`, so the actual unit is used. |
| Right derived functors via injective module resolutions | `(comparisonLowerStar ... X).rightDerived q`. Exact. I read Mathlib's `Functor.rightDerived`, `InjectiveResolution` and `InjectiveResolution.isoRightDerivedObj`: these compute homology after applying the functor to an N-indexed injective resolution. No choice of an unrelated derived functor occurs. |
| Positive images of nu^* G vanish | In the first conjunct, `∀ q : ℕ, 0 < q → IsZero ((...rightDerived q).obj ((comparisonUpperStar ... X).obj G))`. Exact: all and only the requested positive right-derived degrees. |
| Any F isomorphic to nu^* G has the same vanishing | The second conjunct quantifies every pro-etale `F` and assumes `(comparisonUpperStar ... X).essImage F`. Exact. I opened Mathlib's definition: `∃ G, Nonempty (nu^* G ≅ F)`, with the required isomorphism direction and existence rather than chosen data. |
| The uniform bound is M = 0, independently of dimension | Both vanishings use `0 < q`, with no dimension parameter or bound on X. Exact; no stronger vanishing in degree zero is asserted. |
| Finite-field/finite-coefficient application | The universally quantified finite commutative A and arbitrary X include this specialization. I read `Padic.finite_coefficientExtensionRing` and its construction import: for `n ≥ 1` its quotient is finite. The common-universe lift `ULift` supplies the sanctioned coefficient presentation. The defining origin witness of `def-sf-fullcd-used-class` is exactly the second conjunct's hypothesis. The application needs no extra theorem clause or field assumption on the universal comparison. |

Dependency checks: besides the comparison declarations above, I opened
`ringedSiteModules` (the transparent abbreviation of Mathlib's `SheafOfModules`),
`Scheme.proEtaleDerivedCategory` (constant CommRingCat sheaf followed by forgetting
commutativity), Mathlib's `constantSheaf` (constant presheaf then sheafification),
`Injective` (extension across every mono), and the enough-injectives/Grothendieck
sheaf instances. None substitutes structure-sheaf modules for constant-coefficient
modules. The larger coefficient-value universe is the recorded convention,
while both site object universes remain u+1 and site morphism universes remain u.
There is no added equality of these universes. Enlarging the ambient scheme
universe and transporting smaller coefficients by `ULift` covers arbitrary
set-sized schemes and sheaves. Every variable in the signature is explicitly
bound. There are no new definition nodes or dependency modules in this delivery,
and no `statement_change`, so no correction/citer repair is needed.

Edge cases: the empty scheme is allowed, with no chosen point or nonempty cover.
The zero ring and zero sheaf are allowed, with no `Nontrivial` assumption.
Arbitrary infinite/nonconstructible sheaves are allowed. Degree q=0 is excluded
from vanishing and covered by the actual unit assertion; q=1 and every larger
natural degree are included. Negative degrees are outside the node's
injective-resolution convention. No index set is introduced, so empty covering
families and their sheaf conditions remain those of the underlying sites. No
restriction on characteristic is present. The stage parameter n occurs only in
the application; its n≥1 finiteness input is exactly the node's. The universal
comparison also covers the zero coefficient case without requiring an n.

My independent duplicate searches used different terms from the first worker:

- `msearch.py ... leanfinder "higher direct images vanish for pullbacks from the small etale site along the comparison geometric morphism"`: eight results, consisting of generic sheaf pullback/transport declarations and the site definitions; no matching statement.
- `msearch.py ... grep "rightDerived.*comparison|comparison.*rightDerived"`: five generic localization-comparison hits, no pro-etale comparison vanishing theorem.
- Direct `rg` for `comparisonLowerStar.*rightDerived`, `rightDerived.*comparisonLowerStar`, and essential-image/comparison combinations in Mathlib's algebraic geometry, the pinned upstream project, and `lean/Sheaf` found the already recorded comparison infrastructure and `siteComparison_finiteLevel`. I opened that entire theorem: its vanishing assumes `Injective I`, so it does not state this node for arbitrary G or the entire essential image.
- I opened `isIso_comparisonAdjunction_unit` in the exact source and `isZero_homology_rightDerivedComparisonLowerStar` in the newer framework. The former only states the underived unit. The latter gives positive integer-degree homology of the unbounded derived direct image on a literal pullback; it does not state the present conjunction or its injective-resolution/essential-image form. The present module introduces no duplicate definition of any notion.
- The extra literal-name LeanFinder query returned unrelated tactic bounds, and the unqualified Loogle query was rejected for an unknown identifier. Neither was used as evidence of absence; the successful semantic and direct-source searches above supply that evidence.

H5/H6/H8/H9 checks: the module contains one named theorem with sole proof `sorry`,
no definitions and no proofs of additional claims. Its module and theorem
docstrings name the source and blueprint id, and the theorem docstring follows
the node's five steps including the independent abelian acyclicity and scalar
transfer. All lines are at most 100 characters; there are no private definitions,
file-local notations or local instances. Public imports supply signature notions
and instances; ordinary imports supply the recorded proof dependencies.

Validation: my own prescribed `scompile.py NG prop-sf-comparison-bound-zero
lean/Sheaf/Paper/ComparisonBoundZero.lean` run compiled the sandbox and library
names cleanly (4.4 s and 4.6 s), with no warnings. A direct string comparison
confirmed `lean.statement` is verbatim the file's theorem signature before
`:= by`, and comparing node copies confirmed that `lean` is their only differing
field. No mismatch required repair; the only authored change is this independent
second-reading section.
