## Worker report

The current base already contains Q83's `Sheaf.CategoryTheory.CompositeTensorTranspose`.
I read that module and all four dependency records and declaration sources. Its global
calculation and canonical helper definitions match the global part of this node. The final
restricted-domain clause was only in its proof docstring: the theorem still required two
ambient `Adjunction`s and two everywhere-defined `ProjectionFormula` structures. Therefore
an `existing: true` rebinding alone would not state the whole node. This delivery preserves
all those declarations and adds the local-diagram statement of that final clause in the
same owning module. No informal statement, dependency list, or proof plan is changed.
There is no repair-note file for this item and no item-specific Q144 return entry.

The module contains two postponed theorems, both for this node's two cases:
`SecSmoothPurity.composite_tensor_transpose` and
`SecSmoothPurity.CompositeTensorLocalData.composite_tensor_transpose_restricted`.
Their proofs are exactly `sorry`, with the node's natural-language proof in their
docstrings. Every helper is real data: structures of specified objects and equations,
functorial images, isomorphism composition, or application of a specified Hom equivalence.
No object or morphism is chosen from a postponed existence theorem.

The hypotheses and clauses of the global statement are rendered as follows.

| Node text | Lean rendering |
| --- | --- |
| Three monoidal categories | `C`, `D`, `E` with `Category` and `MonoidalCategory` instances; independent object and Hom universes `uX vX uY vY uZ vZ` |
| Strong monoidal `S_f`, `S_g` | `S₁ : D ⥤ C`, `S₂ : E ⥤ D`, `[S₁.Monoidal]`, `[S₂.Monoidal]`; Mathlib's invertible lax/oplax structure is equivalent to the dependency's `CoreMonoidal` |
| Left functors and specified right adjoints | `P₁`, `P₂`, `G₁`, `G₂`, `adj₁ : P₁ ⊣ G₁`, `adj₂ : P₂ ⊣ G₂`; the Hom bijections and counits are those of these adjunctions |
| Natural projection isomorphisms with unit and associativity equations | `pf : S₁.ProjectionFormula P₁`, `pg : S₂.ProjectionFormula P₂`; fields `iso`, `natural_left`, `natural_right`, `unit`, `assoc` |
| Composite functors and adjunction | `P₁ ⋙ P₂`, `S₂ ⋙ S₁`, `G₂ ⋙ G₁`, `adj₁.comp adj₂` |
| Specified composite projection | `compositeProjectionIso`, defined as `P₂.mapIso (pf.iso ...)` followed by `pg.iso ...` |
| Specified composite counit | `(adj₁.comp adj₂).counit.app`; `Adjunction.comp_counit_app` identifies it with `P₂.map` of the first counit followed by the second |
| `W_h`, `τ^h` | Unit images `G₁.obj (𝟙_ D)`, `G₂.obj (𝟙_ E)`, `(G₂ ⋙ G₁).obj (𝟙_ E)`; `tensorCounitTranspose` is `pf.theta` followed by the right adjoint of the right unitor |
| Transpose convention | `ProjectionFormula.theta` is literally `adj.homEquiv` of the projection followed by the whiskered counit; naturality in the target gives the subsequent unitor, so this is the exact stated transpose |
| `q = τ^f_V` | `tensorCounitTranspose S₁ P₁ G₁ adj₁ pf (G₂.obj (𝟙_ E))` in `compositeTensorSecond` |
| `K` arbitrary | `(K : E)` |
| `N` and its identification with the reassociated tensor source | `compositeTensorSource`; `compositeTensorSecond` inserts `(Functor.Monoidal.μIso ...).inv ▷ W` followed by the specified associator |
| First map | `compositeTensorFirst`: `S₁.map (τ_g K) ▷ W`, then `τ_f (G₂.obj K)` |
| Second map | `compositeTensorSecond`: reassociation, `S_c K ◁ q`, then the Hom transpose built from the composite projection and composite counit |
| The explicit common inverse transpose | `compositeTensorInverseTranspose`: `P₂.map` of `pf.iso`, then `P₂.map` of the first whiskered counit and right unitor, then `pg.iso`, the second whiskered counit and right unitor |
| Both inverse transposes equal that map | The two conjuncts in `composite_tensor_transpose`, using `((adj₁.comp adj₂).homEquiv N K).symm` |
| No invertibility of `τ`, `q`, or `W_h` | No such assumptions; only the stipulated tensorators and projection maps are isomorphisms |
| No geometric hypotheses | Only category, functor, monoidal, adjunction and projection data occur |

The restricted clause is formalized separately without requiring ambient right adjoints.
`CompositeTensorLocalData` records only the finite diagram used by the proof. This is an
owning-node helper for the restricted calculation, not another definition of an adjunction,
strong monoidal functor, or projection formula. Its data and equations are extracted from
those specified structures on their full domains; arbitrary maps cannot replace the
transposes or counits because those are definitions from the Hom bijections.

| Restricted clause | Local data and statement |
| --- | --- |
| Functors on full domains | `X : ObjectProperty C`, `Y : ObjectProperty D`, `R : ObjectProperty D`; `P : X.FullSubcategory ⥤ D`, `Q : Y.FullSubcategory ⥤ E`, `S : R.FullSubcategory ⥤ C` use Mathlib's full subcategories, with exactly all ambient morphisms between their objects |
| Right-adjoint objects needed in the diagram | `A`, `V`, `T` name `S_g K`, `G_g 𝟙`, `G_g K`; `W`, `U`, `H` name `G_f 𝟙`, `G_f V`, `G_f (G_g K)` |
| Definedness of coefficient tensor and selected tensorator | `hAV`, `delta`; `delta` is the supplied inverse strong tensorator at `A,V`, the only monoidal comparison of `S_f` used in this calculation |
| Definedness of the first left functor's tensor sources | `hN`, `hVW`, `hTW`, `hAU`, `hAVW`; each is explicit membership in `X`, not a tensor-closure assumption |
| Definedness of the second left functor's sources | `hPN`, `hPAU`, `hAPU`, `hPU`, `hV`, `hAVY`, `hAVPW`; these include the intermediate object in the explicit four-arrow inverse transpose |
| Specified adjunction Hom bijections | `homFOne`, `homFV`, `homFT`, `homGOne`, `homGK`; each has the exact adjunction orientation on its full source domain and selected target |
| Naturality equations actually used | `naturalFV`, `naturalFT`, `naturalGK`; these are contravariant naturality of the given inverse Hom equivalences, with actual functorial images of full-subcategory arrows |
| The two counits at units and the first counit at `V` | Definitions `counitFOne`, `counitGOne`, `counitFV` apply the corresponding inverse Hom bijection to the identity, as in Stacks 0037 |
| Selected projection instances | `pfAV`, `pfT`, `pfV`, `pfAQ`, `pfAU`, `pgV`, `pgU` have exactly the relevant projection-formula types |
| Projection naturality and coherence used | `Coherence.natural_left` at `τ_g K`, `natural_right` at `q`, `assoc` at `S_g K,V,W`, and `natural_counit` at `ε_f,V`; they are literal instances of the dependency's equations, not hypotheses asserting the desired equality |
| Defined transposes and composites | Definitions `tauG`, `q`, `first`, `second`, and `inverseTranspose` repeat the exact formulas using those local data |
| Composite projection and counit | In `second`, `Q.map pfAU.hom ≫ pgU.hom` and `Q.map counitFV ≫ counitGOne` |
| Composite Hom bijection | The succession of `homGK` and `homFT`; its inverse in each conclusion is `homGK.symm (homFT.symm ...)` |
| Both inverse transposes equal the displayed composite | Two conjuncts of `composite_tensor_transpose_restricted` |
| No value outside domains asserted | Every argument of `P`, `Q`, `S` is a member of its full subcategory, and every image of an arrow is `Functor.map (ObjectProperty.homMk ...)`; no extension functor, ambient adjunction, tensor-closed domain, or value at an outside object is assumed |

`S_g` itself supplies only the object `S_g K` in the restricted calculation, so there is
no need to extend its values away from this selected input. Likewise only the indicated
values of the right adjoints enter. All equations stipulated in the restricted interface
are the equations actually used by the same two-transpose proof. In particular the
projection unit axiom is part of the global projection structures, but the finite local
calculation uses only associativity, the listed naturality equations, and the ambient
right-unitors. No projection instance at a new coefficient unit is requested.

Dependencies used, with declarations and sources opened:

- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory` and its data class
  in `Mathlib.CategoryTheory.Monoidal.Category` (tensor, associator, unitors, pentagon,
  triangle). The node is a Mathlib leaf and has no Lean record.
- `def-sfb-strong-monoidal-functor`: `CategoryTheory.Functor.CoreMonoidal` and
  equivalent `Functor.Monoidal` in `Mathlib.CategoryTheory.Monoidal.Functor`;
  `Functor.Monoidal.μIso` gives the specified tensor comparison. The node is a
  Mathlib leaf and has no Lean record.
- `def-weil-pbc-composite-adjunction`: `CategoryTheory.Adjunction.comp`,
  `comp_homEquiv`, `comp_counit_app`, and `Adjunction.homEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. The node is a Mathlib leaf.
- `def-sfb-projection-formula`: `CategoryTheory.Functor.ProjectionFormula` and
  `ProjectionFormula.theta` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`. Read the exact
  published framework source under `lean/WeilConjectures` and
  `coord/pefw-upstream-framework.md`, rather than the older source checkout.
- The full-domain encoding uses `ObjectProperty.FullSubcategory` and
  `ObjectProperty.homMk` from `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.

Source check: read main-20261015 `thm-pur-cohomological-smoothness.proof.md`, second
paragraph, and the local Stacks `categories.tex`, `definition-adjoint` and its following
unit/counit formulas. The calculation preserves projection first, then the first counit,
then the second counit. No source-based statement correction is needed.

Edge cases checked: independent object and morphism universes are retained in both
versions; no smallness or equality of universes is imposed. No nonemptiness is added.
If an ambient category has no unit object it is not monoidal and is not a case of the
node. Empty full domains admit no `d` with the displayed objects; the restricted clause
explicitly assumes those objects are defined. Finite full domains and full domains not
closed under tensor are allowed by the individual membership fields. Identity functors
and identity adjunctions make both maps the same unitor/tensorator composite. Zero
objects and zero or noninvertible counits and transposes are allowed: no cancellation
of any such map is used. No symmetry, additivity, smoothness, or purity is assumed.

Searches performed for an exact statement before changing the module:

- `msearch.py ... leanfinder "double transpose tensor counit maps composite adjunction projection formula"`:
  eight hits, including `Adjunction.map_μ_comp_counit_app_tensor`, its reassociated form,
  `ε_comp_map_ε`, `unit_app_tensor_comp_map_δ`, `map_ε_comp_counit_app_unit`, and duality
  evaluation identities. None states the restricted two-projection calculation.
- `msearch.py ... loogle "SecSmoothPurity.composite_tensor_transpose"`:
  no hit (that service indexes Mathlib, not side-project declarations).
- `msearch.py ... grep "comp_counit_app|projection.*transpose|transpose.*projection" CategoryTheory`:
  eleven hits, composite counits and monoidal adjunction identities, no exact theorem.
- `rg "compositeTensorTranspose|tensorCounitTranspose"` in Mathlib, upstream
  `WeilConjectures`, and side `lean/Sheaf`: only the Q83 module in the side tree.
- Searched the item id in upstream `WeilConjectures`: no hit.
- `rg "Restricted.*Adjunction|Partial.*Adjunction|restricted.*homEquiv|composite_tensor_transpose"`
  in upstream and side project: the existing global theorem and an unrelated
  reconstruction adjunction; no local composite-tensor calculation.
- `rg "PartialFunctor|RestrictedProjection|partial.*functor|HomBijection|PartialAdjunction"`
  in Mathlib CategoryTheory and both project trees: partial-adjoint existence machinery,
  unrelated scalar-Hom bijections and completed projection formulas. Reused Mathlib's
  full-subcategory construction instead of inventing a partial-functor definition.

There are no new DAG nodes, no dependency modules, no changed informal clauses,
and no statement dispute. The node's old global helper definitions and theorem signature
are retained; only its Lean record and module receive this missing formal clause.

Validation: the prescribed single-file `scompile.py` wrapper passed with no errors or
warnings under its default 60-second limit (sandbox 35.8 s, module-path check 17.7 s).
The delivery dry run and push are run after this clean compile; their results are
reported by the delivery tool.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
