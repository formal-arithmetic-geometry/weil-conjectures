## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionDerivedExchangeStalkFormula`
states `AlgebraicGeometry.ClosedImmersionExchange.derived_exchange_stalk_formula`.
Its only theorem has proof `sorry`; all seven helper declarations have real data.
The source is Stacks `literature/stacks-project/perfect.tex`,
`lemma-compare-base-change-closed-immersion` (Tag 0E23), especially the exactness
and displayed stalk calculation before Tor independence is invoked (lines 5351–5375).
The expanded six-step DAG proof is reproduced in the theorem docstring.
No mathematical statement correction or dependency-interface repair is needed.
The returned H2 dependency-ownership fault is repaired by the new existing-definition
node documented below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and morphisms: `{Z X Z' X' : Scheme.{u}}` and `i`, `i'`, `f`, `g`.
  `[IsClosedImmersion i]` is the sole geometric property assumed.
- The cartesian square is `sq : IsPullback g i' i f`. This presents any fibre
  product with its projections, equivalently the chosen `pullback i f`, without
  selecting a different square. Closedness of i' is a consequence, not an input.
- The unbounded module-sheaf categories use the recorded `schemeDerivedCategory`,
  `derivedPullback` and `schemeDerivedDirectImage`. The family of
  `HasDerivedCategory.{w}` instances is the existing size convention required by
  the canonical exchange API; it asserts no geometric or cohomological condition.
- For z', the existing stalk-square abbreviations `R i g z'`, `A g z'`,
  `B i' z'`, `C z'` mean exactly O_X,i(g(z')), O_Z,g(z'), O_X',i'(z'), O_Z',z'.
  Their `leftAlgebra` and `rightAlgebra` are induced by the actual scheme stalk
  maps and transport the equality i(g(z')) = f(i'(z')) from sq.w.
- The existing `SingleComplexBaseChange.tensorMap` is the canonical ring map
  A tensor_R B -> C characterized by its restrictions to A and B. The first
  conjunct asserts `Function.Bijective` of that very map, hence it is a ring
  isomorphism, without an independently chosen ring equivalence.
- The source isomorphism `s` identifies the exact derived stalk of Lf* Ri_*
  with `stalkModel g z' ⋙ sourceModel ... ⋙ Q`. `sourceModel` specializes
  `RingTensorCohomology.sourceComplex`: restrict to R, K-flat resolve over R,
  extend to B. Thus it is K_z tensor-derived-over-R B with its B action.
- `targetModel` specializes the existing `targetComplex`: K-flat resolve over A,
  restrict to R and extend to B, the existing model of
  Res_B(K_z tensor-derived-over-A (A tensor_R B)). The complex natural isomorphism
  `d` identifies this model with `actualTargetModel`: resolve over A, extend along
  `(g.stalkMap z').hom : A -> C`, then restrict along `(i'.stalkMap z').hom : B -> C`.
  Its explicitly quantified pure-tensor equation sends b tensor p to image(b)
  tensor p. This fixes exactly the transport along the canonical tensorMap,
  including its scalar actions and all degrees/differentials.
- The target natural isomorphism `t` identifies the exact derived stalk of
  Ri'_* Lg* with that actual-C model; this is the requested second isomorphism
  in D(B), including restriction from C to B.
- `ringComparison` selects the unique natural transformation characterized by
  `exists_affineDerivedBaseChangeComparison`, not a bare morphism with the same
  endpoints. The final equation compares it, followed by Q(d), with the exact
  derived stalk of `schemeDerivedBaseChangeMap i i' f g sq.w`. The latter is the
  existing precisely normalized mate of the pullback composition and counit.
  This is equality of derived morphisms, not equality of cohomology maps.
- Both `s` and `t` are natural isomorphisms on complexes after precomposition
  with Q. This is the standard presentation of a natural derived isomorphism:
  Q is localization at quasi-isomorphisms, so all complexes and their roofs are
  covered, including arbitrary derived K. The canonical K-flat tensor models
  invert quasi-isomorphisms and thus descend. Their naturality is in M = K_z
  through the degreewise stalk functor. Every derived object has such a representative.
- The last conjunct quantifies over every ambient x' outside `Set.range i'`
  and every derived K, asserting `IsZero` for both requested derived stalks.
- There is no Tor-independence, boundedness, quasi-coherence, flatness, affine,
  nonempty or nonzero assumption.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `IsPullback` is the equivalent square interface.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`:
  `exists_derivedPullbackComposition`, used by the existing normalized mate.
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` reexports
  `RingedSpace.derivedModulePullback_adjunction`; the normalized scheme
  adjunction built into schemeDerivedBaseChangeMap is the canonical specialization.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, including its degreewise action.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard` for the module stalk targets.
- `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`:
  `RingTensorCohomology.exists_affineDerivedBaseChangeComparison`; its public
  import `WeilConjectures.Algebra.Homology.RingTensorCohomology` supplies the
  unique shared `resolution`, `sourceComplex`, `targetComplex` tensor models.
- Added the already landed `def-pc-derived-base-change-map` to stmt_deps for
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap` /
  `schemeDerivedBaseChangeMap`; added
  `def-pc-single-complex-base-change-stalk-condition` for
  `WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` /
  the actual square's R,A,B,C, algebra structures and tensorMap; added
  `def-sfb-derived-zariski-stalk-functor` for
  `WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport` /
  `SingleComplexBaseChange.comparisonDerivedStalk` and its existing exactness
  instances. These are existing notions, not replacements or new definitions.
  Their full source signatures and documentation were read.

All recorded proof modules are imported; the retired empty Sheaf comparison-is-iso
module is replaced by its actual adopted WeilConjectures module. The affine stalk
localization and Spec-map matches are Mathlib declarations available through the
scheme imports; the derived-adjunction match is imported from Mathlib directly.

Edge cases checked before stating: empty Z and empty Z' leave the on-image
quantifier empty but retain off-image vanishing; zero K gives zero source/target;
identity closed immersion and identity/arbitrary base change require no special
choice or omitted case; zero stalk modules and arbitrary positive/negative degrees
are allowed; non-Tor-independent quotients are included and the comparison is
NOT asserted invertible; non-quasi-coherent and unbounded complexes are included.
All universes are explicit and autoImplicit is false. No local notation or instance
is introduced; `ChangeOfRings` and `TensorProduct` are existing public scoped notation.

Searches (before writing):

- msearch.py leanfinder, query `stalk derived exchange closed immersion pullback
  pushforward canonical base change comparison`: eight ordinary stalk/unit
  results, no derived closed-immersion formula.
- msearch.py loogle, query `AlgebraicGeometry.IsClosedImmersion, DerivedCategory`:
  zero hits.
- msearch.py grep, query `derived.*[Ss]talk|[Ss]talk.*[Dd]erived`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- msearch.py leansearch, query `closed immersion derived exchange stalk formula
  without Tor independence`: eight ordinary closed-immersion or restriction-stalk
  results; none gives the theorem.
- rg on both `lean/WeilConjectures` and `lean/Sheaf` for derived/stalk/exchange
  combinations: found the shared exact derived stalk, stalk-square coordinates,
  generic canonical exchange map and existing tensor-comparison models used here;
  no theorem with the present closed-immersion formula and off-image clauses.
- rg for the exact item ID in both source trees: no hits; rg for the chosen
  namespace/declaration in both trees and dag/lean_names_upstream.json: no clash.

Validation: prescribed scompile.py compiled the sandbox and library-path versions
cleanly (16.0 s and 10.0 s on the successful initial run). The final dry-run and
push validation results are recorded by the delivery wrapper.

## Second reading by Q110

Author's explicit second pass, not an independent-agent review: reopened the node,
source proof, imported APIs and final Lean signature. The theorem retains the
actual mate, arbitrary cartesian square, actual stalk ring maps, full derived
morphism equality, naturality and both off-image zero claims. The complex models
are the dependency's existing K-flat constructions, with the transport to C fixed
on pure tensors; no arbitrary comparison or scalar action is substituted. The
only initial compiler fault was omission of the public ChangeOfRings notation
scope; adding it fixed the parse, and all declarations then compiled. Replaced
the retired empty proof import by its adopted source counterpart. No mathematical
node fault or STATEMENT-DISPUTED issue was found. The maintainer supplies the
independent review as required by the dispatch brief.


## New nodes

`def-sfb-derived-zariski-stalk-functor` records the exact existing
`AlgebraicGeometry.SingleComplexBaseChange.comparisonDerivedStalk` and its four
instances `comparisonStalkAdditive`, `comparisonStalkHomology`,
`comparisonStalkLimits`, `comparisonStalkColimits`, all in the owning module
`WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport`.
Its Lean attachment is `existing: true`, branch `slopmaster2`; no new module or
second definition is introduced. The statement specifies schemes Y, points y,
the ordinary Zariski module stalk S_y, additivity and preservation of homology,
finite limits and finite colimits, followed by S_y.mapDerivedCategory with the
standard target ModuleCat localization. Each clause is given by one of the five
recorded declarations; the localization comparison is Mathlib's existing
`Functor.mapDerivedCategoryFactors`. The full source bodies were reread.
The source is Stacks 0E23's stalk computation and exactness of module stalks
(modules.tex, lemma-abelian); exactness permits the generic derived localization.
LeanSearch found mapDerivedCategory, LeanFinder found ordinary tilde stalk maps,
and the Mathlib grep found the exact-functor localization API. Source-tree rg
found precisely the five reused declarations. Definition-node rg found only the
different open-immersion stalk-isomorphism node, and blueprint_refs search returned
zero matches. All actual search outputs are retained in mathlib_searches.
Thus the Lean notion already exists, but no DAG definition node owned it; the new
node supplies the missing ownership required by the return. Empty schemes have
no points to bind, and zero, arbitrary unbounded and non-quasi-coherent complexes
are included without extra hypotheses.

## Repair of return H2

The immutable returned head fcda03813d82 cited the theorem node
`lem-pc-stalk-comparison-source-transport` merely for the plain derived stalk
functor; it did not use `exists_comparisonSourceIso`. Replaced that added
statement dependency with `def-sfb-derived-zariski-stalk-functor`, whose
existing:true attachment owns the required functor and its four instances in
the same upstream module. The imported module and entire Lean source, including
the theorem signature, are unchanged. This is a dependency-record repair, not an
unchanged re-push. Compared the retained node with current main: only lean and
the earlier added stmt_deps differ; reconstructed the item from current main
and reapplied those authorized fields plus this repair. The definition's
blueprint ancestor is null exactly as blueprint_refs ancestor reports; its via
chain prepends the item to the item's existing chain.

Second pass on the repair: confirmed that the new definition node states the
exact existing functor and each input instance, cites only the four definition
nodes it uses, and the item now cites the definition rather than the unrelated
theorem. The main theorem's mathematics and edge cases remain those approved
in the maintainer's return. Independent review remains with the maintainer.
