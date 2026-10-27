## Worker report

The module `Sheaf.SixFunctors.CompleteLiftedTopCellTriangle` states
`WeilConjectures.CompleteLiftedTopCell.complete_lifted_top_cell_triangle`, with its
whole proof `sorry`. Its six auxiliary declarations contain actual data or transparent
abbreviations; none postulates a comparison map or duplicates a coefficient, derived
category, completion, tensor, or Tor-amplitude construction.

Source read: `literature/stacks-project/proetale.tex`,
`lemma-local-structure-constructible-complex` (Tag 09C3), especially the final
induction paragraph lifting rho(e_s) to cycles and taking the cone. The DAG item
extracts just this lift and complete cone, with a specified free top residue basis.
Its proof's bounds, regular quotient and free completeness inputs explain the
weaker hypotheses of this extracted statement; it does not require all residue
cohomology sheaves to be locally constant.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]` |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Valuation ring and chosen uniformizer | Existing `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`, used by the coefficient API |
| Scheme T and its small pro-etale site | `T : Scheme.{t}`, `T.ProEt`, `ProEt.topology T`; t and u are independent |
| R_n constant sheaves and B their inverse limit | `integralCoefficientSheaf l E T n` and `completedIntegralCoefficientSheafUnrestricted l E T`; API index n denotes exponent n+1, so index 0 is exactly the residue coefficient |
| Unbounded derived module category over B | `DerivedCategory (scalarReductionSource l E T)`; source is the existing `SheafOfModules` category over B |
| Quotient-tower completeness with actual canonical quotient legs and scalar restriction | `IsDerivedCompleteUnrestricted l E T M`, the unchanged global branch of recorded `IntegralOnSlice.IsComplete`; its good representative, quotient transitions and augmented Roos triangle are the recorded constructions |
| Quasi-compact T | `[CompactSpace T]`, without a separation hypothesis |
| Terminal evaluation sends epis of set sheaves to surjections | `hT`, quantified over all F,G and epic f in `Sheaf (ProEt.topology T) (Type (max u (t+1)))`, evaluated at `op (ProEt.mk (𝟙 T))` |
| M_1=M tensor-derived k_T | `(scalarReductionDerivedExtension l E T 0).obj M` |
| Integers a<=b | `a b : ℤ`, `hab : a ≤ b` |
| Tor amplitude on every object, against every degree-zero module | `hTor : ∀ V : T.ProEt, residueTorTest ... V`; the wrapper applies recorded `HasRingedSiteTorAmplitudeOfUniverses` to recorded `ringedDerivedRestrictionGeneral` on the actual slice over V. This predicate quantifies over every module sheaf and degree q<a or b<q; its tensor is the canonical site derived tensor. The restricted constant ring is `(integralCoefficientCommRingSheaf ... 0).over V`. The slice is the usual presentation of the site localized at V. |
| Finite r>=0 and prescribed theta | `r : ℕ`, `θ : residueFree ... r ≅ H^b(M_1)`; finite products in this abelian category are finite direct sums |
| P=B^r and P[-b] | Existing `CompletedCoefficientFree.freeCell ... r b`: the single complex on that product in degree b, localized by `DerivedCategory.Q` |
| Canonical H^b reduction is epi | `Epi (topReduction ... M b)`; topReduction is the existing normalized derived adjunction unit followed by the inverse of the exact restriction/cohomology comparison |
| Surjective on T-sections | `Function.Surjective ((topReduction ...).val.app (op (ProEt.mk (𝟙 T))))`; the target is H^b(M_1) with B-scalars restricted |
| f and distinguished triangle | Existential f,L,g,delta, with `Triangle.mk f g δ ∈ distTriang _`; final target is the source cell shifted by 1, hence P[-b+1] |
| Complete L | `IsDerivedCompleteUnrestricted l E T L` |
| Standard-generator source reduction | Existential isomorphism e from the derived reduction of the free cell to `residueCell ... r b`, required to satisfy the adjunction-unit square with `freeCellQuotient` |
| Actual quotient on generators | `freeQuotient` is the finite product of recorded `CompletedCoefficientFree.quotientProjection` maps, followed by inverse canonical restriction/product comparison. `freeCellQuotient` places that map in degree b and uses the canonical exact functor/single comparison. The unit square fixes e, via the scalar adjunction; e is not an unconstrained change of basis. |
| H^b(f_1)=theta | `singleFunctorCompHomologyFunctorIso ... b` identifies H^b(k^r[-b]) with k^r; its inverse followed by H^b of `e.inv ≫ reduction.map f` equals `θ.hom` |
| r=0: P=0 and f unique | Last implication asserts the localized free cell is zero and every map from it to M equals f. Since this is the single complex on P, its zero condition is equivalent to P=0. Fin 0 is allowed throughout. |
| a=b and empty T allowed | No strict inequality, inhabitant of T, nonzero ring-sheaf, or nonempty site hypothesis occurs. The prescribed theta still binds on the empty site. |

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; its public coefficient-extension module supplies integers, uniformizer, ideals, quotients and transitions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; `Mathlib.Topology.Defs.Filter`: `CompactSpace`; `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, `ProEt.mk`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`; `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`. They are used by the existing coefficient construction, not reconstructed here.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, `singleFunctor` and the triangulated structure; `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `DerivedCategory.homologyFunctor`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimitTriangle`, used inside the recorded completeness condition.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`, underlying the recorded scalar restriction.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the recorded module for `lem-pur-derived-change-of-rings`, publicly retaining its generic sheaf `DerivedChangeOfRingsCochainModel` and independent-coefficient derived change of rings; no ordinary-module endpoint is substituted for sheaf modules.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`: recorded `HasRingedSiteTorAmplitudeOfUniverses`, with its full original-site module test; the latest fixed-coefficient primary specialization is not applicable to non-constant B or to the actual ringed slice, so its publicly retained general interface is used.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`; its global definition is exactly `IsDerivedCompleteUnrestricted` used here.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: existing completed coefficient construction; no identification of scheme and field universes.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`: `scalarReductionSource`, `scalarReductionTarget`, `scalarReductionRestriction`, `scalarReductionDerivedRestriction`, `scalarReductionDerivedExtension`, and their standard localization/exactness interfaces.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`: `ringedDerivedRestrictionGeneral` for the Tor tests; `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit` supplies canonical sheafification on the slice.
- `Sheaf.SixFunctors.CompletedCoefficientFreeResolution`: `CompletedCoefficientFree.residueModule`, `freeCell`, `quotientProjection` and `reductionMap`, now owned by `def-sf-completed-coefficient-free-cell`. Its theorem `completed_coefficient_free_resolution` is used only in the proof plan (step 6), not to state this theorem.
- `def-sf-scalar-reduction-categories-restriction` owns the already-used source/target categories and scalar restriction; `def-weil-integral-derived-reduction` owns `scalarReductionDerivedExtension`. Their unchanged recorded declarations are in `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- Canonical comparison APIs: `Limits.Pi.map`, `piComparison`, `Functor.mapDerivedCategorySingleFunctor`, `Functor.mapDerivedCategoryHomologyFunctorIso`, `DerivedCategory.singleFunctorCompHomologyFunctorIso`.

All existing recorded proof modules are imported. The two proof-only nodes
`lem-sp-completed-coefficient-regular-quotients` and
`lem-sf-derived-homology-long-exact` have no recorded Lean module in this checkout;
there is no module to import. Their mathematical steps remain in the theorem docstring.
Other proof imports match the node: integral coefficient limit, residue bounds,
K-flat resolution, regular quotient flat sequence, SES triangle, weakly contractible
projectivity, bounded-flat K-flatness, single-tensor comparison, constant completion
equivalence and triangulated complete subcategory.

Searches for existing statements (2026-10-23):

- `msearch.py ... leanfinder "A complete complex of proetale module sheaves admits a lift of a prescribed top residue basis with complete cone"`: eight hits, including BDeRhamPlus/BDeRham and ordinary `IsAdicComplete` lifting lemmas; none concerns this derived sheaf statement.
- `msearch.py ... loogle '"IsAdicComplete", "triangle"'`: zero hits.
- `msearch.py ... grep 'residue.*basis|complete.*triangle' Algebra/Homology`: three hits, generic homotopy-category distinguished triangle morphism completion, not this statement.
- `rg -n 'top.cell|top_cell|prescribed.*basis|lifted_top' lean/Sheaf lean/WeilConjectures`: no matching theorem; unrelated endpoint basis or formal ring statements only.
- `rg`/node records identified existing completed free cell, derived quotient unit, quotient-tower completeness, ringed slice restriction and Tor predicates. These are reused. The returned H2 review requires a definition ownership node for the completed free-cell interface; the repair adds that node with `existing: true`, without adding or changing Lean data.
- The exact item-id search in `lean/WeilConjectures` found no declaration.

Edge checks: r=0 (empty product, unique zero-source map), a=b (ordered interval
still accepted), empty scheme (zero sheaf categories), arbitrary negative b,
independent site/coefficient universes, and no condition on other cohomology
sheaves. No STATEMENT-DISPUTED issue or statement correction was found.

## Second reading by Q84

Final in-thread clause-by-clause rereading against the node and source: the two
surjectivity clauses, exact coefficient quotient, cone completeness, prescribed
basis equality and zero-rank uniqueness are each explicit. The Tor test uses every
actual slice, not just the terminal test. The source comparison is fixed by its
unit square on the finite product of coefficient quotient maps; an arbitrary
isomorphism of free residue sources would fail to preserve the prescribed basis
and has not been used. No characteristic or quasi-separatedness assumption is
present. Independent review remains with the maintainer, as the dispatched brief
specifies; no second agent was started.

Original validation: prescribed `scompile.py` passed both sandbox and library-module mode with no errors or non-sorry warnings (22.1 s and 13.6 s). No global build was run. The first repair-session dry run passed on saved packet `fcff0d8311b`, before the ownership correction below; this did not resolve the independent H2 return.

## New nodes

`def-sf-completed-coefficient-free-cell` owns the existing completed-coefficient
finite free cells and canonical reduction maps in
`Sheaf.SixFunctors.CompletedCoefficientFreeResolution`, with `existing: true`.
Its four declarations are `CompletedCoefficientFree.residueModule`,
`quotientProjection`, `freeCell`, and `reductionMap`. The statement introduces the
same arbitrary scheme, prime and finite coefficient extension, completed ring
and its quotient sheaves; it defines the restricted quotient module, the actual
unit-to-unit quotient map, the finite product single complex in degree d, and the
normalized derived adjunction unit. Source: Stacks Tag 09C3, final induction
paragraph, with the scalar-extension normalization of Tag 06YY and quotient
module construction of Tag 093M. No existing definition node owns these data:
the only DAG ownership search hit was the free-resolution theorem record.
The new node records that existing module and adds no module or definition.

Searches performed for this node, 2026-10-23:

- `msearch.py ... leansearch "A finite free cell over a completed coefficient sheaf placed in one degree, with the coefficient quotient map and canonical derived scalar reduction unit"`: eight hits, including `SheafOfModules.free`, `SheafOfModules.ιFree`, and ordinary presheaf free-unit formulas. These are generic module constructions, not the completed-coefficient single complex and normalized derived reduction interface.
- `msearch.py ... leanfinder "Finite free sheaf modules as single cochain complexes with quotient projection and derived extension restriction adjunction unit"`: eight hits, headed by `SheafOfModules.generatorsOfIsCokernelFree`; other hits concern free generators and their maps. None supplies the specialized interface.
- `msearch.py ... grep "CompletedCoefficientFree|quotientProjection|def freeCell" Algebra`: zero Mathlib hits.
- `rg -l 'CompletedCoefficientFree\.(freeCell|quotientProjection|reductionMap)|completed-coefficient-free-cell' dag/nodes`: only `lem-sf-completed-coefficient-free-resolution.json`, a theorem node. The corresponding namespace search in `lean/Sheaf/SixFunctors` finds the unchanged existing definitions; no corresponding namespace is present in `lean/WeilConjectures`.
- `tools/blueprint_refs.py search "completed coefficient free cell"`: zero blueprint nodes. `ancestor` returns `lem-fix-weil-operations`; the new node preserves that ancestor and prepends this item to its `via`.

## Returned-review repair

Return L/H2 at immutable head `2917c0bc325f` is repaired by replacing
`lem-sf-completed-coefficient-free-resolution` in the saved item's `stmt_deps`
with `def-sf-completed-coefficient-free-cell`. The theorem remains in
`proof_deps` and step 6 of the proof docstring. Its conclusion is unnecessary to
form any of the four owned definitions. The new node cites
`lem-weil-derived-scalar-extension-restriction-adjunction`: `reductionMap` is
literally `(derivedScalarExtensionRestrictionAdjunction ...).choose.unit.app M`,
so this theorem supplies required normalized adjunction data. The item's existing
adjunction dependency also supplies `scalarReductionRestrictionLimits` and
`scalarReductionRestrictionColimits`, required to type its canonical comparisons.
The review's two advisory definition dependencies are included both in the new
node and directly in the item: `def-sf-scalar-reduction-categories-restriction`
and `def-weil-integral-derived-reduction`. No mathematical statement, proof plan,
proof dependency, or Lean file has changed; no statement correction is needed.

Repair self-check, with the source, node and Lean file open:

| Checked part | Exact reading and finding |
| --- | --- |
| New node parameters | The source module binds `universe t u`, `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, and arbitrary `T : Scheme.{t}`. No relation between t and u or geometric hypothesis is added. |
| Coefficient index and residue module | `residueModule n` restricts the unit of `integralCoefficientSheaf ... n`; this is exponent n+1, so n=0 is the residue field. The new node uses exactly that indexing. |
| Quotient projection | `quotientProjection` is constructed with `unitHomEquiv.symm` from the identity on the quotient unit module. Its image of 1 is 1, and B-linearity forces the actual coordinate coefficient projection. This is real data, not a free map parameter. |
| Free-cell degree and rank | `freeCell r d` is `(CochainComplex.singleFunctor _ d).obj (∏ᶜ fun _ : Fin r ↦ unit B)`. Thus d=b gives P[-b], all integers d are allowed, and r=0 is the empty finite product. |
| Derived reduction | `reductionMap n M` is the selected normalized adjunction's unit at M. The cited adjunction conclusion fixes its K-flat comparison with the ordinary unit; the new node asserts no additional theorem and chooses no arbitrary arrow. |
| Main theorem hypotheses | The original correspondence table above checks each parameter and hypothesis. `hT` uses all epic set-sheaf maps in universe `max u (t+1)`; `[CompactSpace T]` is the entire geometric assumption. Completeness is the actual quotient-tower predicate. The slice Tor condition tests every object V and every module N through the recorded predicate. The bounds are a≤b, the finite rank is r≥0, and θ fixes only top residue cohomology. |
| Reduction conclusions | The first two conjuncts assert both `Epi (topReduction ...)` and surjectivity of its actual component at the terminal object. That map is the adjunction unit followed by the exact restriction/homology comparison. |
| Triangle and cone | Existential f, L, g and δ form `Triangle.mk f g δ ∈ distTriang _`, with final target the free source shifted by 1, and L satisfies the identical completeness predicate as M. |
| Prescribed basis and canonical identification | The existential e satisfies the explicit reduction-unit square with `freeCellQuotient`, the product of actual coefficient projections placed in degree b. The next equality uses `singleFunctorCompHomologyFunctorIso` and `e.inv ≫ reduction.map f` to assert precisely H^b(f_1)=θ; no independent source basis change is allowed. |
| Boundary cases | The final implication treats r=0, giving a zero free source and uniqueness of f. The statement allows a=b, negative b, and the empty scheme. None is excluded by the new definition node. |

The ownership mismatch is the only repair to the accepted mathematics. This is
the dispatched worker's self-check, including the new node; no other agent was
started. The maintainer performs the independent reading.


Repair validation: `scompile.py Q84 lem-sf-complete-lifted-top-cell-triangle`
passed the unchanged theorem file in sandbox and library-module modes (22.1 s
and 13.6 s), with no errors or non-sorry warnings. The repaired packet passed
`deliver2.py ... --no-push` as commit `03f8ba04c67`: server preflight, existing
ownership declaration check, and per-file compilation all passed. Only this
validation paragraph was added after that dry run. No global build was run.
