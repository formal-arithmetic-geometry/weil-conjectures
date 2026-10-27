## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceRelativeFlatModulePushout` states
`AlgebraicGeometry.AlgebraicSpace.RelativeFlatModulePatching.restriction_equivalence`.
Its only theorem has proof `sorry`. Every helper has explicit data, and no object,
functor, module, map or comparison is selected from a bare existence theorem.
The natural-language statement, proof and existing dependency list are preserved;
the list gains three already-landed definition nodes used by the signature.
No new nodes, dependency repairs, statement correction or disputed statement.

Source checked: `literature/stacks-project/spaces-pushouts.tex`, Tag 08KV,
`lemma-space-over-pushout-flat-modules`, the equivalence and part (b), and
`more-algebra.tex`, Tag 08KP. As already recorded in the node, the source's X in
(2)(b) means X-prime, and O_Y in (b) means O_V. The delivery does not introduce
these corrections: they are already in the accepted statement and source record.

All names below, unless qualified otherwise, are in
`AlgebraicGeometry.AlgebraicSpace.RelativeFlatModulePatching`.

### Hypotheses and objects

| Node hypothesis or object | Lean rendering |
| --- | --- |
| Scheme S and spaces over S in the size convention | `{S : Scheme.{u}}`, with explicit `universe u`; `Diagram S` uses the existing `AlgebraicSpace S`, small etale sites and module categories. No independent section/site universe is equated with another one. |
| Four S-schemes T0,T1,T2,P | `Diagram.T₀`, `.T₁`, `.T₂`, `.P : Over S`; these are arbitrary schemes with their actual structure maps. |
| Maps T0 to T1 and T0 to T2 | `D.i` and `D.a` are morphisms in `Over S`. |
| T0 to T1 is a closed immersion | `[IsClosedImmersion D.i.left]`. |
| Its ideal I has I^n=0 for some n at least 1 | `hnil : ∃ n : ℕ, 1 ≤ n ∧ D.i.left.ker ^ n = ⊥`; `ker` is the actual ideal sheaf data of the closed immersion and bottom is the zero ideal sheaf. |
| T0 to T2 is affine | `[IsAffineHom D.a.left]`, the existing affine-open inverse-image test. |
| P is the scheme pushout with its two inclusions | `D.j₂`, `D.j₁` and `hpush : IsPushout D.a.left D.i.left D.j₂.left D.j₁.left`. The imported `scheme_affineThickeningPushout` shows that this same pushout is an algebraic-space pushout; this is not an additional hypothesis. |
| Any algebraic-space morphism h:V to P | `D.V : AlgebraicSpace S`, `D.h : D.V ⟶ schemeSpace D.P`. No property of h occurs in the equivalence hypotheses. |
| Vi = V times_P Ti | `D.V₀`, `D.V₁`, `D.V₂`, their projections `D.r₀/r₁/r₂` and `D.t₀/t₁/t₂`, and `D.cartesian₀/cartesian₁/cartesian₂ : IsPullback ...`. These are pullbacks in sheaves, hence precisely the existing algebraic-space fibre products, allowing any representative rather than fixing a noncanonical equality of objects. |
| Canonical maps from V0 to V2 and V1 | `D.a₂`, `D.a₁`, with both projection equations `a₂_r/a₂_t`, `a₁_r/a₁_t`. Pullback uniqueness determines each map. These fields supply notation for the uniquely determined arrows, not an arbitrary map or an extra geometric hypothesis. |
| Scheme inclusions as algebraic-space maps | `schemeMap` is literally `ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map f)`, on the existing `schemeSpace`. It has no chosen or postponed data. |
| Quasi-coherent modules on the small etale sites | Each module is in the existing `X.Modules`; `M.IsQuasicoherent` is Mathlib's local arbitrary-free-presentation predicate, specialized by the recorded `QCoh` module. |
| Flatness over the base scheme, on etale charts | `ModuleIsFlatOver D.h M` or `ModuleIsFlatOver D.tᵢ Mᵢ`. This existing predicate tests every compatible pair of etale scheme charts using the recorded scheme `IsFlatOver`; for quasi-coherent modules it is the stated stalk condition. Taking the identity chart of the scheme target recovers the node's direct-to-scheme formulation, and target etale localization gives all the other tests. |
| All pullbacks are tensor pullbacks | Every occurrence is the recorded `moduleTensorPullback`, never the scheme functor named `Modules.pullback` or etale precomposition along a non-etale map. |

### Categories, functor and conclusions

| Node clause | Lean rendering |
| --- | --- |
| Source category of quasi-coherent modules flat over P, with all module maps | `FlatQCoh D.h` is the full subcategory of `D.V.Modules` for the conjunction of the existing quasi-coherence and relative-flatness predicates. Its arrows impose no isomorphism condition. |
| Triples (M2,M1,alpha) | `ModuleTriple D := Comma (moduleTensorPullback D.a₂) (moduleTensorPullback D.a₁)`. Its `left`, `right`, `hom` are respectively M2, M1 and the map between their two actual overlap pullbacks. |
| Mi quasi-coherent and flat over Ti | `AdmissibleTriple D` contains exactly `M.left.IsQuasicoherent`, `ModuleIsFlatOver D.t₂ M.left`, and the analogous two conditions for `M.right` and `D.t₁`. |
| alpha is an isomorphism | The last admissibility condition is `IsIso M.hom`. It is equivalent to retaining alpha as a bundled isomorphism, with its uniquely determined inverse. |
| Arrows are pairs of all module maps commuting with alpha | `FlatTriple D` is the full subcategory of that comma category. Its ambient `CommaMorphism` has `left`, `right`, and the equality `L.map left ≫ target.hom = source.hom ≫ R.map right`. No condition makes these component maps invertible. |
| Restriction gives an equivalence | `∃ E : FlatQCoh D.h ≌ FlatTriple D`, together with the specified natural identifications below. This supplies a quasi-inverse and the unit/counit, rather than only a bijection of object classes. |
| Functor sends M to its restrictions, including every module map | `e₂ : E.functor ⋙ leftForget D ≅ ObjectProperty.ι _ ⋙ moduleTensorPullback D.r₂`, and the analogous `e₁` for `r₁`. These are natural isomorphisms of functors, so they identify both objects and actions on every arrow. |
| Canonical pullback-composition comparison on V0 | `restrictionComparison D M` is `(moduleTensorComposition D.a₂ D.r₂).app M`, then equality transport through the common composite, then the inverse comparison for `D.a₁,D.r₁`. This uses the existing tensor-normalized composition, not an arbitrary iso. The first conjunct of the theorem requires `(a₂-star).map (e₂.hom.app M) ≫ can.hom = (E.functor.obj M).obj.hom ≫ (a₁-star).map (e₁.hom.app M)`. This is exactly compatibility with the specified alpha. |
| If h is locally of finite presentation on etale charts | `MapIsLocallyOfFinitePresentation D.h → ...`, using the recorded all-compatible-charts test, only in the second conjunct. |
| M is finitely presented iff both restrictions are | `∀ M : FlatQCoh D.h, M.obj.IsFinitePresentation ↔ ((moduleTensorPullback D.r₂).obj M.obj).IsFinitePresentation ∧ ((moduleTensorPullback D.r₁).obj M.obj).IsFinitePresentation`. This is the required iff, not merely preservation or an unrelated equivalence. |
| Finite presentation means etale locally a cokernel of a finite free map | The existing Mathlib `SheafOfModules.IsFinitePresentation`, whose witness is a locally finite free presentation, is used directly. |
| No additional hypotheses listed at the end of the node | No flatness of h, support hypothesis, properness, separatedness, quasi-compactness, Noetherian condition, nonemptiness or characteristic assumption is present. |

The equivalence is specified up to natural isomorphism with the actual restriction
functor. Both component natural isomorphisms and their overlap equation are required;
therefore this is stronger than an unspecified equivalence between the two categories
and exactly expresses that restriction is an equivalence. It does not assert a strict
equality of differently represented categorical objects. The finite-presentation
criterion is stated directly on the actual restrictions, independently of choices in E.

The category helpers, diagram notation, scheme-map abbreviation and canonical comparison
are constructions belonging to this same node's stated categories and functor, not new
independent mathematical notions. They are all listed in `lean.declarations`, with source
and blueprint docstrings. There is one postponed theorem, matching this DAG node, and its
docstring contains all eight accepted proof steps, including the nonflat chart-algebra
case and the use of Tag 08KP with E=R.

### Recorded dependency declarations used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.Modules`, `EtaleSite`, `structureSheaf`.
- `def-weil-size-convention` has a convention record and no declaration: universes
  are explicit and the existing module/site encodings are retained.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout`:
  `AlgebraicSpace.scheme_affineThickeningPushout` and
  `exists_affineThickeningPushout`; its scheme clause identifies the two pushouts.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with the stated sheaf-pullback universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its slice
  instances, using Mathlib `SheafOfModules.IsQuasicoherent` without replacement.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorAdjunction`, `ModuleDirectImageModel`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`, the affine-section criterion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`.

Three additional, already-landed definition nodes are added to `stmt_deps`:

- `def-trf-scheme-algebraic-space`, module
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`.
- `def-sfb-space-flat-proper-coefficient`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`: `ModuleIsFlatOver`.
  Only its existing relative-flatness predicate is used; no support condition is used.
- `def-sfb-space-module-tensor-composition`, module
  `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `moduleTensorComposition`, fixed by its unique local-tensor characterization.
  No flat-base-change conclusion is assumed.

The modules of recorded proof dependencies are imported privately when they are not
already public statement dependencies: affine-chart calculus, scheme Zariski/etale
comparison, affine tensor/stalk flatness, quasi-coherent pullback, pointwise-flatness
base change, chart tensor realization, affine module base change, flat module
fibre-product patching, and the Mathlib pullback, finite-presentation and tensor modules.
Proof-only nodes without a recorded declaration are left as future proof inputs, not
silently replaced with an additional hypothesis. No dependency module is repaired.

### Edge cases checked before writing

- Empty V or empty base schemes: the categories use no `Nonempty` or inhabited
  hypotheses. In particular the empty-site/zero-module cases remain in scope.
- Identity thickening I=0: n=1 satisfies `hnil`; restriction recovers the usual
  degenerate pushout equivalence, without imposing that T0 is nonempty.
- Nontrivial nilpotence: every finite exponent at least one is admitted, not just
  square zero. No theorem or definition forces a global uniform universe bound
  beyond the existing size convention.
- Zero modules and zero homomorphisms: allowed by full subcategories; target arrows
  need not be isomorphisms. Only each object's overlap comparison is invertible.
- Arbitrary h, including a nonflat finite-presentation chart algebra such as
  R=k[epsilon]/(epsilon^2), D=R[x]/(epsilon*x): no flatness assumption on D over R
  has entered. The finite-presentation argument uses the accepted E=R proof route.
- Arbitrary characteristic and non-Noetherian/non-quasi-compact schemes: no binder
  removes these cases. Local finite presentation of h is required only for the iff.
- Replacing any Vi by an isomorphic pullback: `IsPullback` and both projection
  equations admit every such representative and determine the same overlap maps.

### Searches for an existing statement or duplicate notion

All semantic searches used the prescribed `batch2/msearch.py` wrapper for this item.

- LeanFinder query: `Milnor patching equivalence of relatively flat quasi coherent
  modules over a nilpotent scheme pushout`. Eight results about flat scheme
  morphisms, their affine criterion, and their permanence; none states this result.
- Loogle query: `CategoryTheory.Functor.IsEquivalence, Module.Flat, IsPushout`.
  Zero hits; the service reports unknown identifier `IsPushout` for that query.
- Mathlib grep query: `patching|Milnor|flat.*pushout`. Four hits: an unrelated
  Milnor sphere, two injectivity lemmas for ring pushouts, and a faithfully-flat
  tensor equalizer. None is the algebraic-space module statement.
- LeanSearch query: `Equivalence of categories of relatively flat quasicoherent
  sheaves on a nilpotent pushout of schemes and compatible pairs`. Eight hits:
  equivalences of ordinary sheaf categories, local quasi-coherent presentation
  data, and compatible-preserving site functors. None gives the patching theorem.
- Project/upstream ripgrep: the item id, relative-flat/module/pushout patterns,
  `RelativeFlatModule`, `FlatModulePatching`, `RelativeFlatPatching`,
  `flatModulePatching`, `relativeFlatModule`, `FlatQCoh` and `ModuleTriple` in
  `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib. No exact statement or category
  was found. Hits for relative-flatness scheme stalk lemmas are proof tools, not
  this equivalence.
- Searches for `ModuleIsFlatOver`, `schemeRestriction`, `moduleTensorComposition`,
  `schemeSpace` and finite-presentation predicates found the exact existing
  interfaces named above; they are reused. Searching their declaration ownership
  in `dag/nodes` found the three already-landed definition nodes added to the item.

### Validation

The full module compiled via the prescribed `scompile.py` against the server's
published live library, in module mode, with no errors or warnings. The first run
reported 2.8 seconds for its sandbox check and 2.6 seconds for the library-name check.
The final delivery dry run recompiles the complete final file and checks the node
signature, metadata, sorry-only theorem proof, docstrings and line width.

## Second reading by Q11

No independent worker reading is claimed. This worker was dispatched directly and
was instructed not to start agents. The maintainer's independent review reads the
delivery, as required by the current direct-delivery brief.
