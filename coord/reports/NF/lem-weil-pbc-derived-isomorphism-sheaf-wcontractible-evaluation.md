## Worker report

The delivery states `lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation`
without changing its mathematical statement. The primary declaration is
`AlgebraicGeometry.Scheme.derivedMorphism_weaklyContractible_evaluation` in
`Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation`.
Its two bijections are bijectivity assertions about explicitly constructed canonical
functions, rather than existence of unspecified bijections. Additional declarations
in this module give every compatibility clause. All theorem proofs are `sorry`;
every definition has actual data. Every declaration has source and blueprint
documentation, and every postponed theorem has a natural-language proof.

The objects and hypotheses correspond as follows.

| Node text | Lean rendering |
| --- | --- |
| A scheme X | `X : Scheme.{u}` |
| A finite commutative ring B | `B : Type (u + 1)`, `[CommRing B]`, `[Finite B]` |
| Small etale/pro-etale sites and their comparison | `X.smallEtaleTopology`, `ProEt.topology X`, `toProEt X`, `proEtaleSiteComparison X`, `ProEtale.comparisonUpperStar (ModuleCat B) X` |
| E in D(B) | `E : DerivedCategory (ModuleCat.{u + 1} B)` |
| Bounded E | `(DerivedCategory.TStructure.t (C := ModuleCat B)).bounded E` |
| Finite B-module cohomology | `hEf : ∀ n : ℤ, Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat B) n).obj E)`; finite generation over a finite ring is equivalent to finite underlying module |
| K in D(X_et,B) | `K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat B))` |
| Bounded K | `hK` uses the same standard t-structure on this derived category |
| Finite locally constant cohomology | `hKf : ∀ n : ℤ, IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor ... n).obj K)`; this is the recorded upstream class, including local constancy and finite stalk modules |
| Constant sheaf complex E | `(constantDerivedEtale X B).obj E`, the derived functor of Mathlib's exact `constantSheaf` |
| Affine pro-etale object | `U : X.ProEt`, `[IsAffine U.left]` |
| Weak contractibility in the stated topos sense | `hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U`; the upstream definition says that every epimorphism of set sheaves is surjective on sections at U |

The coefficient universe is the same larger universe as the sites' objects; the
site morphisms have universe u. This is the authorized fixed-coefficient encoding
`Sheaf J (ModuleCat.{u+1} B)` documented in the recorded
`def-weil-pbc-etale-sheaves`, used by the existing comparison and constructible
sheaf APIs. We do not force the site object and morphism universes equal. The
other encoding, `SheafOfModules` of a constant ring sheaf, remains available in
the dependency's general ringed-site record. Here `J.over U`, `Sheaf.over`,
`J.overPullback`, and `J.overMapPullback` are Mathlib's existing localizations in
the fixed-coefficient encoding, not copies of the slice construction.

The conclusions and maps correspond as follows.

| Node clause | Lean rendering |
| --- | --- |
| Actual local derived Hom presheaf | `derivedLocalHomPresheaf J B A D`, with object type `(derivedSliceRestriction J B U).obj A ⟶ (derivedSliceRestriction J B U).obj D` |
| Actual local derived Isom presheaf | `derivedLocalIsoPresheaf J B A D`, with actual category-theoretic `≅` as its sections |
| Etale sheafification H and I | `derivedLocalHomSheaf X.smallEtaleTopology B ...` and `derivedLocalIsoSheaf ...`, using `presheafToSheaf` |
| Pullback of these set sheaves | `(comparisonSetUpperStar X).obj ...`, exactly the constructed set inverse image in the recorded comparison adjunction |
| Actual derived comparison inverse image | `derivedComparison X B`, the existing exact module comparison applied to the derived category |
| Actual derived categories on the localized site | `derivedSliceRestriction (ProEt.topology X) B U` lands in `DerivedCategory (Sheaf ((ProEt.topology X).over U) (ModuleCat B))`; the recorded localization theorem identifies this site with U_proet |
| Constant source on that localized site | The source is the restriction of `derivedComparison.obj (constantDerivedEtale.obj E)`. Exact inverse image preserves constant sheaves, so this is precisely the node's constant E on U; it is not a chosen local model or a replacement complex. |
| The canonical maps | `derivedHomSheafComparison` and `derivedIsoSheafComparison` transpose actual local pullback first along sheafification and then along the comparison adjunction. `derivedHomEvaluation` and `derivedIsoEvaluation` compose them with the unique inverses of the pro-etale sheafification units at U. |
| Both canonical bijections | The primary theorem asserts `Function.Bijective derivedHomEvaluation ∧ Function.Bijective derivedIsoEvaluation` for exactly E,K and the hypotheses above |
| Extend actual etale-local pullback | `derivedMorphism_evaluation_extends_local`, both Hom and Isom clauses, on `pulledbackEtaleLocalHom`/`pulledbackEtaleLocalIso`; arbitrary `U ⟶ toProEt.obj V` is allowed |
| Preserve identities | `derivedMorphism_evaluation_identity`, using sections represented over the terminal etale object |
| Preserve composition whenever defined | `derivedMorphism_evaluation_composition` and `derivedMorphism_isoEvaluation_composition`, with a third matching derived argument G and the actual `≫`/`≪≫` composites |
| Natural in E,K | `derivedMorphism_evaluation_natural` for pre/postcomposition, applied to the constant image of a map of E's and a map of K's; the Isom version `derivedMorphism_isoEvaluation_natural` allows isomorphisms of arguments, as required for the Isom functor |
| Natural in restriction between such U | `derivedMorphism_evaluation_restriction`, with U,V affine weakly contractible and any `g : V ⟶ U`, for both Hom and Isom |
| Finite coefficient homomorphism B → C | `B' : Type (u+1)`, `[CommRing B']`, `[Finite B']`, `φ : B →+* B'` in `derivedMorphism_evaluation_scalarExtension` |
| Derived scalar extension | Its T,S and all their localized functors are left adjoints to the *existing* `Sheaf.derivedRestrictScalars ... φ`. This is the upstream universal property of derived tensor, not ordinary tensor or an unconstrained functor. |
| Canonical tensor/restriction and comparison identifications | The three displayed adjunction-unit equations uniquely fix `T.restrictionIso`, `S.restrictionIso`, and c as their mates of the canonical restriction-of-scalars isomorphisms. Those latter isomorphisms are explicitly constructed. |
| Maps of Hom and Isom sheaves induced by f tensor C | `T.homSheafMap` and `T.isoSheafMap` apply `T.localFunctor` to each actual local derived morphism (respectively isomorphism), conjugate by the canonical restriction isomorphism, then sheafify |
| Scalar extension evaluates to the same operation | The last two formulas in `derivedMorphism_evaluation_scalarExtension` give this equality on every section, with `scalarEvaluationTransport` identifying the actual target objects |
| Transformed objects remain bounded finite | The compatibility formulas themselves are structural identities for all derived arguments. Apply them to A = constant E and D = K. When E tensor C and K tensor C remain bounded with finite/finite locally constant cohomology, the primary bijectivity theorem applies on both sides. Thus the node's stated conditional compatibility follows; no assertion of preservation of boundedness is made. Exact constant sheaf commutes with the derived tensor construction on K-flat representatives. |
| No finite Tor dimension | There is no such hypothesis anywhere. Tensor is characterized by its unbounded derived adjunction and computed by K-flat resolutions in the proof plan. |

The structural compatibility declarations deliberately state properties of the
canonical constructions for arbitrary derived arguments. The finite-source
comparison bijectivity is only asserted under the node's bounded finite
hypotheses. In particular, nothing asserts internal RHom base change for a
nonperfect source.

Dependency interfaces read and used:

- Mathlib `AlgebraicGeometry.Scheme.Etale`, `Scheme.smallEtaleTopology` (the
  etale-site leaf), and `GrothendieckTopology.over`, `Sheaf.over`,
  `overPullback`, `overMapPullback` (the localized-site leaf).
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`, read for the pro-etale site's size and
  module encoding. This statement uses the coexisting fixed-coefficient
  encoding specified by `def-weil-pbc-etale-sheaves`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`,
  `preservesFiniteLimits_proEtaleSiteComparison`,
  `proEtaleSiteComparisonModules`; underlying framework
  `ProEtale.comparisonUpperStar` and `comparisonAdjunction`.
- Mathlib `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.homologyFunctor`, and `DerivedCategory.TStructure.t`;
  exact-functor derived comparison and composition from
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- Mathlib `CategoryTheory.constantSheaf`, `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; existing exactness of constant sheaf and slice
  constant comparisons from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and
  `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.IsFiniteLocallyConstantSheaf`, including its
  `IsLocallyConstantSheaf`/`IsFiniteSheaf` fields.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.weaklyEtale_localization`, identifying the slice with the
  small pro-etale site of the object, including its coefficient transport.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`:
  `GrothendieckTopology.IsWeaklyContractible`.
- Existing `CategoryTheory.Sheaf.derivedRestrictScalars`,
  `Sheaf.IsDerivedBaseChange` and its unit-compatible uniqueness theorem
  in `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange`.

The main module privately imports every stated proof-dependency module, including
the bounded-free RHom model, finite-ring derived local constancy, K-injective
slice restriction, localization adjunction, weakly contractible evaluation,
canonical tensor pullback, and finite-level site comparison. Their theorem
proofs are not used or changed in this stage.

Edge cases checked mathematically before recording the statements:

- B may be the zero ring; all module objects and their local Hom/Isom sets
  then have their expected zero-category behavior. No nonzero-ring hypothesis
  or cardinality division was introduced.
- E or K may be zero, and E may be nonperfect with infinite projective
  dimension. The primary hypotheses say bounded finite cohomology, not a
  bounded finite-projective representative. The proof docstring uses a
  bounded-above finite-free source and finite diagonals against a bounded-below
  target, exactly as the node's proof does.
- X or U may be empty. The empty localized topos has the zero module category,
  with a singleton Hom and Isom between its objects. The raw presheaves preserve
  the empty disjoint union; this case is included in the 0F63 argument.
- For distinct objects with no isomorphism, Isom may be empty; its presheaf
  uses genuine isomorphisms, and evaluation does not choose an isomorphism
  from an existence proposition.
- Identity restrictions and arbitrary maps between the allowed U's occur in
  the formulas, as do the identity coefficient map and nonflat quotient maps.
  If tensor loses boundedness, only the structural map equality is asserted;
  the finite-range bijectivity theorem is not applied to an inadmissible input.
- All cohomology indices are integers, with no implicit bound or missing
  negative-degree cases; no qcqs, noetherian-scheme, separatedness, or
  affineness assumption on X was introduced.

Searches: `msearch.py` LeanFinder query "derived morphism sheaf evaluation on
weakly contractible proetale affines" returned eight affine-limit/formal-
unramified hits, none the statement. The query "presheaf of morphisms in derived
categories of localized sheaves of modules and sheafification" returned eight
ordinary module-sheafification declarations, none the required presheaf.
Loogle queries `DerivedCategory, Sheaf` and
`Sheaf.over, sheafificationAdjunction` had zero hits (unknown short identifiers).
Mathlib grep `homPresheaf|isomPresheaf|derivedHomPresheaf` in CategoryTheory
had zero hits. LeanSearch queries for evaluation and for sheaves of derived
morphisms were unavailable (Internal Server Error), recorded as unavailable.
The exact tool logs are retained in `searches.jsonl` and their query/result
records are copied into each new node. `rg` on upstream WeilConjectures, the
side library, and DAG nodes found only proof prose or internal/underived Hom,
not these canonical local-derived presheaves or their comparison. Both
`blueprint_refs.py` searches, "derived morphism presheaf" and
"derived morphism sheaf comparison", returned zero blueprint matches.
The existing weakly-contractible sheafification node was also read: it concerns
point-Lan presheaves from profinite sets, so does not already state the generic
local-derived presheaf construction here. Stacks 0F63 supplies the general
finite-disjoint-union criterion used in the helper's proof.

No statement correction and no mathematical dispute. The helper maps were
missing interfaces, not a false or ambiguous node. The original node's other
fields are unchanged except the authorized addition of the two new definition
nodes to `stmt_deps`.

Validation: all three delivered modules compile separately in dependency order
through `scompile.py`, with no errors or warnings. The final validation command is
`deliver2.py NF lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation --no-push`.
No delivery is pushed by this worker; the independent second reader delivers it.

## New nodes

`def-weil-pbc-derived-morphism-presheaves`, module
`Sheaf.CategoryTheory.DerivedMorphismPresheaf`, defines actual Hom and Isom on
localized *derived* categories, their restriction maps and sheafifications,
unique composition extensions, maps in both arguments, and coherent localized
functors with their induced sheaf maps. Source: Stacks localized sites,
Cohomology on Sites 0946/09BE, and the amplification proof's actual-morphism
presheaves. It also exposes the canonical scalar-restriction/slice comparison.
All naturality and exactness obligations needed by these constructions are
named theorems with proof docstrings in the owning module and are included in
the new node's statement. It does not duplicate the existing internal-Hom or
underived sheaf-Hom notions. The searches above found no existing node or
exact declaration; sheafification and slice primitives are reused.

`def-weil-pbc-derived-morphism-sheaf-comparison`, module
`Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison`, defines the canonical
slice comparison by transposing the restricted adjunction unit, then the
canonical Hom/Isom sheaf maps by the two adjunction transposes. Evaluation is
composition with the unique inverse of the specified pro-etale
sheafification-unit bijection at U, as justified by the finite-disjoint-union
criterion of Stacks 0F63. It also defines the represented local sections,
product-comparison composition, identities, and the specified scalar-
restriction comparison. The node includes the continuity, invertibility,
naturality and unit-bijectivity obligations, with proof docstrings beside their
named theorem statements. The sources are Stacks 0F63/09B1 and the amplification
proof. Existing site-comparison functors are reused; the searches above found
no existing canonical derived morphism-sheaf comparison to reuse. No definition
chooses arbitrary data from an unproved existence theorem: the only choices
are unique extensions or inverses of explicitly specified bijections.

## Second reading by NF

I independently read the shared node, the sandbox node, all three delivered
modules, and the recorded statement dependencies. The Lean says what the node
says. I found no mathematical or signature mismatch and left the Lean and node
records unchanged. This reading adds only this review to the report.

Source check: the local literature checkout lacks the two Stacks source files,
so I read the published tags and downloaded the corresponding upstream `.tex`
files into this item's scratchpad. In `proetale.tex` I read
`lemma-presheaf-value-weakly-contractible`,
`lemma-w-contractible-is-weakly-contractible`, and `lemma-compare-derived`;
in `sites-cohomology.tex` I read the opening definition in the weakly
contractible section, `lemma-w-contractible`, the paragraph constructing the
constant derived functor, and `lemma-locally-constant-map` with its preceding
lemma. Sources: [0F63](https://stacks.math.columbia.edu/tag/0F63),
[09B1](https://stacks.math.columbia.edu/tag/09B1),
[0946](https://stacks.math.columbia.edu/tag/0946), and
[09BE](https://stacks.math.columbia.edu/tag/09BE).
The final-object hypothesis in 09BE is supplied by each localized site. Its
perfect-source hypothesis belongs to that cited lemma, not to this node's
explicitly documented bounded finite-source extension. The six-step argument
in the node and main docstring supplies that extension using a bounded-above
finite-free source and a bounded-below target. Neither the node nor the Lean
silently identifies finite cohomology with perfectness. The other source
statements introduce no Noetherian or separatedness condition on the scheme.

My object/hypothesis/conclusion checklist, made from the node before accepting
the declarations, is as follows. All names below are in `CategoryTheory` or
`AlgebraicGeometry.Scheme`, as indicated by the modules' namespaces.

| Object, hypothesis, or clause in the node | Actual Lean rendering and verdict |
| --- | --- |
| Scheme X, with no additional scheme hypotheses | `X : Scheme.{u}`. Matches; no qcqs, Noetherian, connectedness, or separatedness instance. |
| Finite commutative coefficient ring B | `B : Type (u + 1)`, `[CommRing B]`, `[Finite B]`. Matches, including the zero ring. |
| The small etale and pro-etale sites and their comparison | `X.smallEtaleTopology`, `ProEt.topology X`, and `toProEt X`; `comparisonSetUpperStar` unfolds to the left adjoint of the recorded `proEtaleSiteComparison`. `derivedComparison` derives the existing `ProEtale.comparisonUpperStar (ModuleCat B) X`. Matches the specified comparison. |
| E an object of D(B) | `E : DerivedCategory (ModuleCat.{u + 1} B)`. Matches the actual localization, rather than a complex or an underived module. |
| E bounded | `hE : (DerivedCategory.TStructure.t ...).bounded E`. Matches the standard cohomological boundedness condition. |
| Every cohomology module of E finite | `hEf : ∀ n : ℤ, Module.Finite B ((DerivedCategory.homologyFunctor ... n).obj E)`. Over finite B, finite generation is equivalent to a finite underlying module. Matches, without projectivity. |
| K an object of D(X_et,B) | `K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))`. Matches the authorized fixed-coefficient encoding. |
| K bounded | `hK` uses the standard t-structure on that same derived category. Matches. |
| Every cohomology sheaf of K finite locally constant | `hKf : ∀ n : ℤ, IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor ... n).obj K)`. I opened `ConstructibleSheaf/Defs.lean`: this class extends both the etale-cover local-constancy class and geometric-stalk finite-generation class. For finite B these are exactly finite locally constant module sheaves. Matches. |
| Constant complex underline E | `constantDerivedEtale` is `(constantSheaf X.smallEtaleTopology (ModuleCat B)).mapDerivedCategory`. It applies the existing exact constant-sheaf functor, rather than choosing a local model. Matches. |
| Etale local derived Hom and Isom presheaves | `derivedLocalHomPresheaf` and `derivedLocalIsoPresheaf` have object values actual Hom and actual `≅` in `DerivedCategory (Sheaf (J.over V) (ModuleCat B))`. Their maps are derived restriction conjugated by `derivedSliceMapIso`. Matches the localized derived categories. |
| H and I their etale sheafifications | `derivedLocalHomSheaf` and `derivedLocalIsoSheaf` apply `presheafToSheaf` to precisely those presheaves. Matches. |
| U an affine object of X_proet | `U : X.ProEt`, `[IsAffine U.left]`. Matches; affineness is on U rather than X. |
| U weakly contractible for set sheaves | `hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U`. The current server source defines this as sectionwise surjectivity for every locally surjective morphism of set sheaves. On this sheaf topos locally surjective is equivalent to epi, so this is exactly the node's condition. |
| Both displayed canonical bijections | `derivedMorphism_weaklyContractible_evaluation` asserts `Function.Bijective derivedHomEvaluation ∧ Function.Bijective derivedIsoEvaluation`. Both functions start at sections of the pulled-back etale sheaf and end at actual local derived Hom/Isom for the same pulled-back objects. Matches both directions and all quantifiers. |
| Constant source and U_proet identification on the right | The target uses `derivedSliceRestriction (ProEt.topology X) B U` of `derivedComparison.obj (constantDerivedEtale.obj E)` and `derivedComparison.obj K`. The recorded `ProEt.weaklyEtale_localization` identifies this slice with U's small pro-etale site for arbitrary value categories; constant coefficients and exact inverse images give the specified constant source. Matches. |
| Canonical, rather than arbitrarily chosen, evaluation | `derivedComparisonLocalHom`/`LocalIso` apply the actual slice comparison. `derivedHomSheafComparison`/`IsoSheafComparison` transpose this map through the sheafification and comparison adjunctions. `derivedHomEvaluation`/`IsoEvaluation` then use the inverse of the specified pro-etale sheafification unit. Matches. |
| Extends etale-local pullback | `derivedMorphism_evaluation_extends_local` has both Hom and Isom equations for every etale V and every `g : U ⟶ (toProEt X).obj V`, using `pulledbackEtaleLocalHom`/`Iso`. Matches actual pullback, with no chosen neighbourhood restriction. |
| Identities | `derivedMorphism_evaluation_identity` states both the Hom identity and `Iso.refl` equation. The represented sections use `Scheme.Etale.mk (𝟙 X)`. Matches. |
| Composition whenever arguments match | `derivedMorphism_evaluation_composition` and `derivedMorphism_isoEvaluation_composition` quantify over a third derived object G and both input sections. Products are transported through the inverse-image product comparison. Their right sides use `≫` and `≪≫`, respectively. Matches. |
| Naturality in E and K | `derivedMorphism_evaluation_natural` is contravariant in the first derived argument and covariant in the second; specialize its first morphism to `constantDerivedEtale.map`. `derivedMorphism_isoEvaluation_natural` gives the corresponding functoriality for isomorphisms of arguments. Matches the Hom functor and Isom functor on its groupoid. |
| Naturality under restrictions between allowed U | `derivedMorphism_evaluation_restriction` quantifies over two affine weakly contractible objects and every `g : V ⟶ U`, with both Hom and Isom equations. Matches without requiring g to be a covering or an immersion. |
| Finite ring homomorphism B to C | `derivedMorphism_evaluation_scalarExtension` takes arbitrary `[Finite B']` and `φ : B →+* B'`. Matches, including nonflat maps. |
| Derived scalar-extension operation | The existential T and S have global and every-slice adjunctions to the existing `Sheaf.derivedRestrictScalars ... φ`. This universal property specifies derived tensor. The three displayed unit equations identify `restrictionIso` and c as the canonical mates of the actual scalar-restriction comparisons. Matches; these are not arbitrary functors or isomorphisms. |
| Scalar extension commutes with evaluation | The last conjunction in `derivedMorphism_evaluation_scalarExtension` gives the two sectionwise squares, using `T.homSheafMap`/`isoSheafMap` and `S.localFunctor.map`/`mapIso`, with `scalarEvaluationTransport` on the objects. Matches f tensor C on both sides. |
| Conditional bounded finite hypotheses after tensor | Those squares are structural identities for arbitrary derived arguments. For the node's E and K, apply the main bijectivity theorem on each side when the scalar-extended objects have its bounded finite hypotheses. Exact constant sheaf commutes with this derived tensor construction. This formulation neither assumes preservation of boundedness by all ring maps nor omits the node's conditional case. |
| No finite Tor dimension | No such binder occurs, and no perfectness or flatness assumption occurs. Matches. |

Dependency review: I opened the signatures of the recorded site, comparison,
constant-sheaf, sheafification, abstract-derived-category, local-constancy,
localized-site, and weakly-etale-localization declarations. The fixed-module
encoding is expressly permitted by `def-weil-pbc-etale-sheaves`; it is not a
private substitute for the ringed-site encoding. Mathlib's `J.over`, `Sheaf.over`,
`overPullback`, `overMapPullback`, and `pushforwardOverMapIso` provide the existing
restriction data. The inverse-image functor is the existing constructed
comparison functor, not another geometric morphism with the same name. I also
read `coord/pefw-upstream-framework.md` and the actual upstream comparison
declarations. For the two modules absent in the older local source checkout,
I read their current sources using `scompile.py --source`: the weakly
contractible predicate and `Sheaf.derivedRestrictScalars`/
`Sheaf.IsDerivedBaseChange`. In particular the latter really specifies
unbounded derived scalar extension, not ordinary scalar extension.

New-node review: `def-weil-pbc-derived-morphism-presheaves` introduces the
missing localized derived Hom/Isom presheaves and their sheafifications, and
includes the exactness, restriction-law, unique-composition, and coherent-local-
functor obligations that its module postpones. Its source descriptions agree
with actual restriction of derived sheaves and sheafification; they do not
claim that 09BE already states the main finite-source extension.
`def-weil-pbc-derived-morphism-sheaf-comparison` introduces the missing
canonical comparison by the specified adjunction transposes. Its statement
also includes slice continuity/exactness, invertibility and naturality of the
specified maps, and bijectivity of the sheafification units at the allowed U.
The latter follows from 0F63 because finite disjoint unions induce product
decompositions of module-sheaf categories and hence derived Hom/Isom; the empty
union has the singleton Hom/Isom values. I checked every helper theorem against
these node clauses and its proof docstring. Both nodes have exactly the required
field set, empty proof fields, null `mathlib_match`, the item's chapter/unit and
ancestor path, search records, and their own module/declaration lists. Both are
added to the item's `stmt_deps`. There are no dependency-module repairs in this
delivery. The item itself changes only `lean` and the two permitted added deps.

No hollow data: the only choices in definitions are unique extensions
(`∃!` for sheafified composition), the inverse of a specified bijection, and
the inverse of a specified isomorphism. All restriction functors, maps, and
presheaf components have actual data. T and S in the scalar statement are
existentially quantified with their adjunctions and unit normalizations; no
definition chooses them from an unspecified existence theorem. All theorem
bodies remain `by sorry`; the structural instance/definition fields use actual
sectionwise data and the named postponed obligations. The main docstring
contains all six proof steps of the item, and helper docstrings give the
arguments for their own postponed claims. No variables or universes are
implicitly unbound (`autoImplicit false` in each module).

Edge cases: all cohomological degrees are integers, including zero and negative
degrees. There is no field or characteristic restriction. The zero coefficient
ring, E = 0, K = 0, empty X, empty U, and empty Isom sets are allowed. The
finite-disjoint-union argument explicitly includes the empty union; on the
empty localized site the module category is zero, giving singleton Hom/Isom.
The source is allowed to be nonperfect. Coefficient maps include identities,
zero-ring maps whenever defined, and nonflat quotients; the boundedness proviso
after tensor has the precise role described above. Identity restriction and
all morphisms between the allowed affines occur in the restriction theorem.
Sites have object universe u+1 and morphism universe u; coefficients and
sections use u+1, as required by the recorded APIs. No equality between these
site universes, or extra derived-category instance chosen from `Nonempty`, is
imposed.

Independent searches: `msearch.py ... leanfinder` with query "sheafification of
Hom in localized derived categories evaluation at projective objects of a
topos" returned eight hits (Ext, sheaf cohomology presheaves, projective
resolutions), none the local derived Hom/Isom comparison. A second query,
"functor of local derived category morphisms as a sheaf with composition and
change of coefficients", returned eight infrastructure hits, including
`Sheaf.cohomologyPresheafFunctor`, `sheafCompose`, and `mapDerivedCategoryFactors`,
with no match. `msearch.py ... grep` with
`local.*derived.*morphism|derived.*morphism.*sheaf|presheaf.*isomorphism`
returned nine ordinary presheaf/sheafification hits, not these notions.
`msearch.py ... leansearch` with "Evaluation of the sheafification of local
derived category Hom on a weakly contractible proetale affine" was unavailable
(Internal Server Error); it is recorded as unavailable, not as a negative
search. `rg` directly on Mathlib, upstream WeilConjectures and shared
`lean/Sheaf` found no declarations of `derivedLocalHom`,
`derivedHomSheafComparison`, `constantDerivedEtale`, or the main theorem.
Conceptual searches in those trees and the DAG found internal/underived Hom
and proof prose, not the two new constructions. `blueprint_refs.py search`
for "local derived Hom" and "derived morphism sheaf" each returned zero
blueprint matches. Thus neither a dropped module nor an `existing: true`
replacement is indicated.

Validation: I compiled all three files separately, in dependency order, in one
authorized `scompile.py NF lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation`
invocation. The wrapper's library checks took 7.5 s, 5.0 s, and 5.6 s, all
without errors or warnings. I also compared each node's `lean.statement`
verbatim against its module signature; all three match. No mathematical
statement correction was required, so there is no `statement_change` or
changed-citer audit. The delivery dry run and final push follow this reading.
