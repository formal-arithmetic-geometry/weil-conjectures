## Worker report

The retained attempt consisted only of a draft Lean file. Its existential functor and
comparison were unconstrained and its continuity hypothesis asked only for some
isomorphism, so it did not state the node. It had no node record or report. I retained
the module path and replaced that draft with an evaluation-normalized representative
formulation of the entire statement. No natural-language statement or proof field changes.

Module: `Sheaf.Paper.DerivedInternalHomFilteredColimit`.
Primary declaration:
`WeilConjectures.SfbHomFilteredColimit.derivedInternalHom_filteredColimit_comparison`.
Every theorem has `sorry` as its whole proof and a source/proof docstring. All definition
data are real constructions. `comparison` and `scalarComparison` are selected only from
named existence-and-uniqueness theorems whose component formulas determine the maps.
There is no arbitrary choice of a scalar-extension functor or comparison isomorphism.

### Hypotheses and objects

- A site small in the module universe: explicit `u v r w`, `C : Type u`,
  `Category.{v} C`, topology `J`; rings and modules in `max u v r`. The site object,
  site arrow, coefficient, and derived-Hom universes are independent. In particular
  the pro-etale object/arrow sizes need not be equal. The sheafification and locally
  bijective-equivalence binders are the usual module-category infrastructure.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{max u v r}`.
  `Modules` is a transparent abbreviation of the dependency's `ringedSiteModules`,
  itself Mathlib `SheafOfModules`; there is no second module category or abelian
  instance. `homFixed` uses exactly the recorded `homComplexFunctor` and fixed
  `coefficientHomResolution`, hence computes `derivedInternalHomOfUniverses`.
- The small filtered category is `I : Type (max u v r)`, `[SmallCategory I]`,
  `[IsFiltered I]`. This includes non-poset filtered categories and parallel arrows;
  `IsFiltered` includes nonemptiness. The main statement's
  `[HasFilteredColimitsOfSize.{max u v r, max u v r} ...]` and
  `[AB5OfSize.{max u v r, max u v r} ...]` state existence and exactness of all
  filtered sheaf-module colimits at this size, exactly as in the node. The auxiliary
  filtered-roof theorem uses their specialization to shape I. No exactness of
  arbitrary colimits or Grothendieck-abelian structure is added as a hypothesis.
- The algebra diagram is `S : I ⥤ Sheaf J CommRingCat`, with structural natural
  transformation `algebra : const R ⟶ S`. The resulting algebra is literally
  `colimit S`, not an unrelated coefficient ring. `φ` and `hφ` specify its induced
  structural map from R.
- `ModuleDiagram ... S algebra φ` presents the underlying sheaf-module diagram:
  `stage` identifies its objects with the actual restrictions of the unit modules
  of the S_i; `transition` requires the given algebra maps on all sections.
  `colimitIso` identifies the module colimit with restriction of the unit of
  `colimit S`; `colimit_normalization` requires the actual algebra-colimit injections
  on all sections. Thus it supplies the underlying-module colimit asserted in the
  node, not an additional flatness or base-change assumption.
- `hfree` is exactly `∀ i, ∃ d : ℕ, Nonempty (T.modules.obj i ≅ R^d)`.
  Here `R^d` is the finite categorical product of the actual unit module, and in
  this additive category is also the finite direct sum. No bases or compatibility
  between chosen bases are part of the input.
- `P` is any K-flat complex (`IsKFlatIndependentCoefficients`). It represents the
  arbitrary K in D(R). Every K has such a representative by the recorded K-flat
  resolution theorem; no degree bound or finite Tor amplitude on P is imposed.
- The second input `L` is any complex with `hL : ∀ n, n < b → IsZero (L.X n)`.
  This is a representative presentation of bounded-below cohomology, not a
  restriction to a smaller collection of derived objects: the good lower
  truncation in the node's step 1 represents every such derived object. The
  statement is universal over every P and L with these representative properties.
  Neither `I_R(L)` nor the Hom complex is assumed bounded below.
- `Continuous ... P` quantifies over every strict I-diagram M of complexes and
  every common termwise lower bound. It requires `QuasiIso (colimit.post M
  (homFixed ... P))`, which is exactly the canonical cocone map from the termwise
  colimit of the functorial RHom representatives to the functorial representative
  at the termwise colimit. After Q this says the evaluation-induced map in the
  node is an isomorphism. It does not replace that map by mere existence of an
  isomorphism, and does not incorrectly ask for an ordinary categorical filtered
  colimit of arbitrary diagrams in the triangulated category.
- `E`, `h`, `hmap`, `[E.Additive]` are the ordinary change-of-rings presentation
  supplied by `derivedChangeOfRingsIndependentCoefficients`: both objects and maps
  are specified by the existing `changeOfRings`/`changeOfRingsHom`. These are
  presentation parameters, not an arbitrary functor or an assumption of a desired
  Hom comparison. Finite-free stages and exact filtered colimits imply E is exact;
  consequently termwise E computes its derived scalar-extension functor on every
  complex, including the unbounded Hom representative. No hypothesis of exactness
  or flatness of E was added.
- `HasDerivedCategory.{w}` is the recorded localization-size infrastructure for
  the final target D(S). The remaining intermediate constructions are on actual
  complexes and do not require an unnecessary extra choice of D(R).

### Every conclusion and compatibility clause

- The canonical R-linear stage map is `comparison.app T`. `Normalized` specifies
  it on every actual sheafified tensor generator and every actual Hom-product
  projection: `(t tensor f)(x)` is the fixed augmentation of `t tensor f(x)`.
  `comparison_existsUnique` makes this a genuine natural transformation in T.
- The scalar version is `scalarComparison`. `ScalarNormalized` requires
  `(s tensor f)(t tensor x) = eta_S(st tensor f(x))`, for all site sections and
  all homogeneous components. The evaluation is supplied by
  `coefficientHomComponent`, not by an arbitrary map with an informal label.
- `derivedComparison` is the actual morphism in D(S): localize scalarComparison,
  invert the localized specified denominator, and use the inverse of the fixed
  `coefficientHomResolutionIso`. Its source is Q(E(Hom(P,I_R(L)))); exactness of
  E identifies this with S tensor^L H_R(K,L). Its target is literally the recorded
  `derivedInternalHomOfUniverses` applied to Q(E(P)), Q(E(L)), i.e. the node's
  H_S(S tensor^L K, S tensor^L L).
- `scalarComparison_quasiIso` asserts that both specified arrows of this roof
  are quasi-isomorphisms. The primary theorem supplies the denominator's proof
  and asserts `IsIso` of `derivedComparison` in D(S). The existential proof is
  only what permits inversion of the already specified denominator; it does not
  introduce any arbitrary morphism or derived functor.
- The first isomorphism in the node's displayed composite is
  `IsIso (colimit.post T (tensorFixed ... (homFixed ... P).obj L))` in
  `filteredColimit_comparison`, inverted after localization.
- The second isomorphism is the colimit of `comparison.app (T.obj i)` and the
  inverses of `roofDenominator ... (T.obj i)`. The theorem asserts their
  stagewise quasi-isomorphism. Exact termwise filtered colimits preserve these
  quasi-isomorphisms. `comparison` is a natural transformation, so these are
  maps of strict diagrams, not an unsupported inference from separate derived
  coprojections.
- The third isomorphism is `Continuous` applied to `T_i tensor L`. These
  complexes have the same strict lower bound b. `roofDenominator` compares
  them with `T_i tensor I_R(L)`, without assuming this latter diagram has a
  lower bound. The two explicit square clauses of `filteredColimit_comparison`
  identify the colimit roof with the global evaluation roof. This is precisely
  the composite in the node, including its normalization, after localization.
- `scalarComparison_restriction` explicitly asserts the restriction square
  identifying the S-linear map with that same R-linear roof. Its iso ν sends
  each tensor generator to the actual scalar-extension generator. Its iso θ
  is ordinary scalar adjunction on chain Hom, fixed by `f ↦ (x ↦ f(1 tensor x))`.
  The final equality includes the actual fixed resolution units, hence provides
  the evaluation-normalized scalar-adjunction identification. No arbitrary
  `Nonempty` iso substitutes for the needed comparison. This chain statement
  supplies exactly the normalization needed from the still-unstated full proof
  dependency `lem-sfb-dc-hom-scalar-adjunction`; it does not restate that node's
  more general derived theorem.
- `scalarComparison_naturality` is the explicit chain equation for precomposition
  in P and postcomposition in L, using both functorial resolutions. It descends
  to arbitrary derived morphisms and inverse quasi-isomorphisms. The
  `comparison_diagram_naturality` equation applies to every coefficient-module
  diagram morphism. Together with the normalized restriction square, it gives
  the compatibility for compatible algebra-diagram morphisms. All transition
  maps are included in the natural transformation `comparison`. The formulas
  never choose a basis, so they assert independence of choices of finite bases.
- There is no constructibility condition on L and no finite Tor-amplitude
  condition on K anywhere in the module.

### Dependency declarations read and used

Statement dependencies, including the two already-landed representative interfaces
added to stmt_deps (no new nodes, no dependency-record changes):

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`, the actual sheaf tensor.
- `Sheaf.Algebra.Homology.KFlat`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`,
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` and its underlying
  ring-sheaf abbreviation; its ordinary functor presentation is used verbatim.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses` and its localization normalization.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `colimit`, `colimit.post`,
  `colimMap`, `colimit.ι`; `Mathlib.CategoryTheory.Filtered.Basic`, `IsFiltered`.
- `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`.
- `def-weil-size-convention` is metatheoretic, with no declaration to import;
  explicit independent universes implement its existing convention record.
- `def-coef-ringed-tensor-hom-model`, module
  `Sheaf.Paper.CoefficientRingedTensorHomModel`, `coefficientTotalTensor`,
  `coefficientTensorGenerator`. These are the already recorded actual K-flat
  tensor constructions, not a second tensor definition.
- `def-coef-hom-representative-evaluation`, module
  `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, `coefficientHomResolution`,
  `coefficientHomComponent`, `coefficientHomResolutionIso`.

The recorded, available proof modules are imported without `public`:
`TensorColimitsIndependentCoefficients` (read with `scompile --source` because
absent from the older local checkout), `SiteTensorFunctoriality`,
`KFlatResolutionIndependentCoefficients`, `QuasiIsoHomComplexMap`,
`HomTensorTotal`, `HomComplexGlobalHomotopy`, `KInjectiveHomComplex`,
Mathlib `DerivedCategory.KInjective`, upstream `HomotopyCategory.Acyclic`, and
`WeilSiteDerivedTensorDescent`. The Hom, tensor, K-flat and functorial K-injective
modules needed by both statement and proof are already exposed by public imports.
The full scalar-adjunction proof-dependency has no recorded declaration yet and
therefore no import; the needed chain comparison is stated explicitly as a helper
of the owning node, with its pure-tensor characterization and full proof docstring.
No dependency module is replaced or privately copied.

### Edge cases

Rank zero is allowed (`d : ℕ`, `Fin 0`); a zero algebra/module and zero input
complexes are not excluded. Constant and singleton diagrams are included. Parallel
arrows and transition matrices in arbitrary finite bases are included because the
map is natural in the coefficient module, not defined by choosing a basis.
Negative lower bounds and odd-degree Hom components are included; the scalar has
degree zero and the recorded Hom/total tensor supplies the signs. Neither target
K-injective replacements nor the Hom complex require a lower bound. Empty sites
and the zero ring are not excluded. An empty filtered index category is correctly
excluded by `IsFiltered` itself, as in the node. Different object/arrow universes
and a larger coefficient universe remain available.

### Searches and primary source

- `msearch.py ... leanfinder "derived internal Hom base change filtered colimit
  finite free coefficient algebras continuity"`: eight hits on light-condensed
  internal projectivity/ihom sections; none states this conditional comparison.
- `msearch.py ... loogle "CategoryTheory.Limits.colimitComparison,
  CategoryTheory.PreservesColimit, SheafOfModules.changeOfRings"`: zero hits;
  first identifier unknown. Direct Mathlib source inspection locates the actual
  canonical map as `CategoryTheory.Limits.colimit.post`.
- `msearch.py ... grep "filtered.*[Hh]om|[Hh]om.*filtered" Algebra/Homology`:
  two hits, on eventually constant/cofiltered complexes and Grothendieck complex
  categories; no coefficient-Hom comparison.
- `rg` of `WeilConjectures`, `lean/Sheaf/Paper`, and
  `lean/Sheaf/Algebra/Homology` for the filtered-Hom patterns found other filtered
  derived categories and filtered-cohomology lemmas, but no copy of this statement.
  Searches for the intended declaration/namespace and for this blueprint id in
  upstream source and the upstream-name index returned no matches.
- Inspected the existing abstract `coefficientBaseChangeHom` in
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`. It defines the categorical
  evaluation mate once a strong tensor comparison is supplied; it does not state
  this filtered-colimit theorem or give its strict chain/colimit representative.
  This delivery's canonical chain comparison is fixed directly by the actual
  scalar generators and normalized resolution square, with no arbitrary strong
  tensor comparison assumed.
- Read the full signatures/docstrings of the recorded statement dependencies.
  The existing `CoefficientRingedTensorHomModel` and
  `CoefficientHomRepresentativeEvaluation` provide the missing generator and
  representative APIs, so I use them and add their already-landed node ids.
- Read the actual Bhatt--Scholze PDF, Lemma 6.8.12, Proposition 6.8.14 and Remark
  6.8.15, and all eleven steps of the node. The node already says explicitly that
  the conditional general ring-sheaf formulation is an extracted agent argument,
  not a verbatim assertion in the paper; this delivery follows that formulation.

No STATEMENT-DISPUTED issue or statement correction. The representative formulation
exposes the node's own argument without weakening or adding mathematical assumptions.

### Validation

`scompile.py Q10 lem-sfb-dc-hom-filtered-colimit` compiled the sandbox file and
its library module separately and cleanly, with no errors or warnings. All variables
and universes are explicitly bound (`autoImplicit false`). The delivery dry run passed
server preflight and compilation, including the literal all-filtered-colimits
`AB5OfSize` hypothesis. Only the owning module, owning node record, and report are
staged. The final delivery wrapper repeats preflight and compilation before pushing.

## Second reading by Q10

Independent maintainer reading, 2026-10-17, of immutable delivery
`1364b57e4adc247c55c2c4622da77ba5435888cb`. The reader did not write or
previously second-read this delivery. This section replaces the worker's explicit
placeholder saying that no second reading occurred; it does not attribute this
review to an earlier Q10 worker.

Result: the Lean says the conditional node's statement, using universal
representatives and the explicit auxiliary compatibility statements. No change
to the Lean module, mathematical statement, dependency list or Lean record is
needed. The only repair is this report section (delivery-errors H11).

### Statement and dependency checks

1. **Site, universes, coefficients.** The section binds `C : Type u`,
   `Category.{v} C`, `J`, and the sheafification infrastructure in `max u v r`.
   `R` is a commutative ring sheaf at that coefficient size. Site object and arrow
   universes remain independent; no pro-etale universe equality is imposed.
   The size convention is metatheoretic and correctly has no Lean declaration.
   The sheafification hypotheses are infrastructure available at the stated
   small-site size, not stronger geometric hypotheses.
2. **Module sheaves and derived categories.** `Modules` transparently abbreviates
   `CategoryTheory.ringedSiteModules`, which is Mathlib `SheafOfModules`, with
   Mathlib's abelian structure. The target is the ordinary `DerivedCategory`,
   with its localization `DerivedCategory.Q` and an explicit, independent
   `HasDerivedCategory.{w}`. No replacement category or abelian structure is made.
3. **Tensor, K-flatness, internal Hom.** `tensor` and `tensorFixed` use the
   recorded `coefficientTotalTensor`; its construction is the actual total
   tensor with the signed differential. `hP` uses the recorded
   `IsKFlatIndependentCoefficients`. `homFixed` uses the actual
   `homComplexFunctor` and `coefficientHomResolution`. `homValue` projects by
   `coefficientHomComponent` and evaluates on the identity object over U.
   `resolutionUnit` uses precisely the augmentation of that fixed replacement.
   `derivedComparison` ends in the recorded `derivedInternalHomOfUniverses`,
   through the inverse of its actual `coefficientHomResolutionIso`.
4. **Filtered diagram and exactness.** `I : Type (max u v r)`,
   `SmallCategory I`, and `IsFiltered I` implement a general small filtered
   category, including parallel arrows. `HasFilteredColimitsOfSize` and `AB5OfSize`
   express existence and exactness at that size. The auxiliary colimit theorem
   requires only existence and exactness for the given shape. No arbitrary-colimit
   exactness is assumed.
5. **Algebras, colimit, finite freeness.** `S : I ⥤ Sheaf J CommRingCat` and
   `algebra : const R ⟶ S` give the algebra diagram. Its colimit is literally
   `colimit S`; `φ,hφ` specify the induced R-algebra structure. `ModuleDiagram`
   identifies stages and transitions with the underlying algebra modules and
   the module colimit with the underlying algebra colimit, including the actual
   colimit injections. These are presentation data for the node's stated
   underlying-module colimit, not an assumed Hom comparison. `hfree` asks for an
   isomorphism to a finite product of the unit module; this is R^d and also the
   finite direct sum. No basis compatibility is required.
6. **K and continuity.** `P` ranges over arbitrary K-flat representatives of K,
   with no bound or Tor-amplitude assumption. The existing K-flat resolution
   theorem supplies such a representative for every K. `Continuous` quantifies
   over all strict I-diagrams of complexes with a common termwise lower bound
   and requires `QuasiIso (colimit.post M (homFixed ... P))`. This is the
   canonical functorial-representative cocone map, not mere existence of some
   isomorphism. Exact filtered colimits preserve quasi-isomorphisms, so this
   formulation is invariant under replacement of P.
7. **L and scalar extension.** `L,b,hL` range over strictly bounded-below
   representatives. Good lower truncation, as in node step 1, represents every
   derived L with bounded-below cohomology. Neither its K-injective resolution
   nor the Hom complex is bounded in the statement. `E,h,hmap,E.Additive`
   specify ordinary scalar extension on both objects and maps, exactly as the
   recorded derived-change-of-rings interface supplies. They do not leave E
   arbitrary or assume the desired isomorphism. Finite freeness and exact
   filtered colimits make scalar extension exact, so its termwise computation
   represents derived scalar extension even on the unbounded Hom complex.
8. **Canonical map and invertibility.** `Normalized` and `ScalarNormalized`
   prescribe the evaluation formulas on actual sheafified tensor generators
   and all Hom-product projections. The two existence-and-uniqueness theorems
   determine actual maps; choosing them is permitted by the no-hollow-data rule.
   Their formulas are respectively `t tensor f(x)` and `st tensor f(x)`, followed
   by the fixed augmentation. `derivedComparison` localizes the scalar map,
   inverts the specified denominator, and applies the fixed Hom factorization.
   The main theorem supplies that denominator's quasi-isomorphism proof and
   asserts that this particular morphism is an isomorphism in D(S).
9. **Displayed composite and scalar adjunction.**
   `filteredColimit_comparison` gives the tensor-colimit isomorphism, stagewise
   quasi-isomorphisms of the actual roof, and strict cocone equations. Together
   with `Continuous` these give exactly the node's three arrows. The second
   denominator equation is stated stagewise in complexes and extends to the
   colimit by its universal property there. No invalid detection of derived
   morphisms by separate stage restrictions is used. `scalarComparison_restriction`
   fixes the tensor identification ν and chain-Hom scalar adjunction θ by
   `f ↦ (x ↦ f(1 tensor x))`, and states the resolution-normalized square.
   This is a genuine helper for the required comparison, not an assumed
   arbitrary scalar-adjunction isomorphism. It suffices here without replacing
   or presupposing the whole more general scalar-adjunction DAG theorem.
10. **Naturality and bases.** `comparison` is a natural transformation for every
    coefficient module map; `comparison_diagram_naturality` gives its colimit
    equation. `scalarComparison_naturality` gives contravariant P and covariant
    L naturality with the actual resolution maps. These equations and the
    normalized restriction square descend to derived morphisms and give
    compatible algebra-diagram naturality. Finite bases enter only the proof of
    stage invertibility, never the maps. No constructibility assumption on L is
    introduced.

All eleven statement dependency records were read. Their exact interfaces were
checked in `RingedSiteModules.lean`, Mathlib's `DerivedCategory/Basic.lean`,
`HomologicalComplex.lean`, `Limits/HasLimits.lean`, and `Filtered/Basic.lean`,
`KFlat.lean`, `DerivedChangeOfRingsIndependentCoefficients.lean`,
`DerivedInternalHomOfUniverses.lean`, `CoefficientRingedTensorHomModel.lean`, and
`CoefficientHomRepresentativeEvaluation.lean`. In addition the fixed-resolution,
Hom-product, and K-flat-resolution definitions/signatures were inspected. The
public imports expose the statement interfaces; the non-public imports supply
the proof tools described in the docstrings. There are no delivered dependency
repairs or new nodes. The two added dependencies are already recorded notions.
No statement correction is claimed or needed, so no §1(C) citer audit is required.

### Sources and one-definition-per-notion

Read the actual Bhatt--Scholze PDF, printed pp. 61–62, Lemma 6.8.12,
Proposition 6.8.14, Remark 6.8.15. The node accurately labels this as a conditional
general ring-sheaf extraction rather than a verbatim theorem about arbitrary
ring sheaves in that paper. Its continuity hypothesis replaces the source's
constructibility input; no geometric hypothesis from the pro-etale application
has silently been substituted for this general conditional statement.

Read Stacks `sites-cohomology.tex`: the Hom-complex construction at line 8571,
chain adjunction `lemma-compose` at 8616, RHom well-definedness at 8754,
K-flat-to-K-injective and internal-Hom construction through `lemma-internal-hom`
at 8896, and derived base change at 3585. Read
`sites-modules.tex`, `lemma-tensor-commute-colimits` at 4001. The Hom differential,
degree-zero coefficient formulas, evaluation order, exact-colimit argument, and
lower-truncation argument agree with these constructions and the node's eleven
steps. In particular no Koszul interchange is needed for degree-zero scalars.

Independently searched the permitted project and upstream trees and Mathlib's
homology sources for filtered/Hom and base-change/Hom terminology and the exact
namespace/declaration/blueprint id. No existing statement of this conditional
finite-free coefficient theorem was found. Inspected the existing
`coefficientBaseChangeHom` in `CoefDerivedSystemEvaluationCalculus.lean`: it is
an abstract closed-category mate requiring supplied tensor data, not the present
strict representative construction or filtered-colimit assertion. The delivery
reuses the recorded tensor, Hom, resolution, colimit and scalar-extension notions;
its abbreviations, restrictions and generators are presentations of those, not
competing notions. The worker records semantic, type-pattern and textual searches.

### Edge cases and pilot gates

Checked rank zero (`Fin 0`), zero ring/algebras/modules/complexes, an empty site,
singleton and constant diagrams, arbitrary parallel arrows and transition
matrices, negative lower bounds, odd Hom degrees, and unbounded resolutions and
Hom complexes. The empty index category is correctly excluded by `IsFiltered`.
All these cases are compatible with the formulas and quantifiers. Universe
parameters u,v,r,w are bound explicitly and independently where required;
`autoImplicit false` is set.

All 25 recorded declarations occur in the module, with source/blueprint
docstrings. The proof docstrings cover steps 1–11 across the colimit,
restriction, scalar and main statements. All eight theorem proofs consist solely
of `sorry`; definitions contain no `sorry`. Unique normalized maps and inverse
localized quasi-isomorphisms are determinate constructions, not hollow choices.
There is no overlength line, declaration under a `Sheaf.` namespace, or detected
upstream declaration-name collision. No pro-etale substitute, global build, or
live Lean write was used.

The node's `lean.statement` equals the whitespace-normalized signature verbatim,
from `theorem` through the conclusion before `:=`. An initially suspected Unicode
escape mismatch was a display-escaping misreading: direct decoded-string
comparison found zero literal Unicode escape sequences and exact equality.
It is not a delivery defect and no record fix is supplied.

### Compiler evidence

Reproduced with:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q10 lem-sfb-dc-hom-filtered-colimit snapshot/lean/Sheaf/Paper/DerivedInternalHomFilteredColimit.lean
```

Exit code 0; no errors or warnings. Output reported the sandbox
`Sheaf/Stage2/Sandbox0.lean` compile in 8.5 seconds and the library
`Sheaf/Paper/DerivedInternalHomFilteredColimit.lean` compile in 11.8 seconds,
with private artifacts under `/dev/shm/nt-tmp/nt-local-compile-a9z2t4fw/.lbuild`.
The installed wrapper currently invokes the server side-overlay compiler, rather
than the local implementation described in the older brief. This confirmation
checks the single immutable delivered module in both modes; no build was run.

Immutable module SHA256:
`b780a43fb987e4063d6ccea9728a03ec18719273f0f85023bdd3d830b10cdada`.
Immutable item JSON SHA256:
`9cbddfdd2a6225e6b73fa48fd3aa68994e06f5c0344e1ea761f9f9644d6cfe1a`.
