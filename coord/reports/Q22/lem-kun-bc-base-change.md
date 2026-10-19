## Worker report

`Sheaf.Paper.KunBaseChange` states all of `lem-kun-bc-base-change` in three theorems:
`AlgebraicGeometry.Etale.kun_bc_base_change` (clause 1),
`AlgebraicGeometry.Etale.kun_bc_base_change_cube` (the unconditional diagram of clause 2), and
`AlgebraicGeometry.Etale.kun_bc_base_change_identification` (its final conditional statement).
Each theorem has only `sorry` as its proof and its docstring supplies the corresponding node
proof steps. All declarations are listed in the node's `lean.declarations`.

Every variable and universe is explicit (`set_option autoImplicit false`). Schemes have
universe `u`; coefficients are exactly `AddCommGrpCat.{u + 1}`, with the same small-etale-site
size convention as the recorded derived inverse-image-composition declaration. There is no
abstract coefficient-category parameter and no geometric finiteness, torsion or invertibility
assumption on the exchange map.

The common hypotheses and clause (1) correspond as follows:

| Node text | Lean rendering |
| --- | --- |
| Cartesian square with its chosen identification | `sq : ChosenCartesianSquare g' f' f g`, the recorded dependency itself |
| `f:X→Y`, `f':X'→Y'`, `g:Y'→Y`, `g':X'→X` | The four explicitly typed scheme morphism binders |
| Abelian coefficients, bounded below | `DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})` |
| Canonical exchange, not an arbitrary map | `derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq` |
| Any `u:Y''→Y'` | `u₀ : Y'' ⟶ Y'` with arbitrary `Y'' : Scheme.{u}` |
| `X''=X'×_{Y'}Y''`, `v`, `f''` | `pullback f' u₀`, `pullback.fst f' u₀`, `pullback.snd f' u₀` |
| Further square | `IsPullback.of_hasPullback f' u₀` |
| Outer square and induced Cartesian identification | `.paste_horiz (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)` |
| Every `K∈D⁺(X_et)` | The arbitrary binder `K` in the stated bounded-below category |
| First factor `(cᴰ_{g,u,Rf_*K})⁻¹` | `(upperStarCompDerivedPlus ... u₀ g).hom.app (Rf_*.obj K)` |
| Pullback of the original exchange | `(u₀)^*[...].mapDerivedCategoryPlus.map ((derivedBaseChangeMapPlus ... sq.toCommSq).app K)` |
| Further exchange at `g'⁻¹K` | The component for `IsPullback.of_hasPullback f' u₀` at `(g')^*[...].mapDerivedCategoryPlus.obj K` |
| Final factor `Rf''_*(cᴰ_{g',v,K})` | Direct-image `.map` of `(upperStarCompDerivedPlus ... (pullback.fst f' u₀) g').inv.app K` |
| The displayed equality | `kun_bc_base_change`; `≫` writes composites in traversal order, the reverse of the printed `∘` notation |
| No exchange factor assumed invertible | There is no `IsIso` hypothesis in this theorem |

The geometry and every arrow of clause (2) are explicit constructions, as follows:

| Node text | Lean rendering |
| --- | --- |
| Any `w:Z→Y` | `w : Z ⟶ Y` in the two cube theorems |
| `X̃=X×_Y Z`, `a`, `f̃` | `pullback f w`, `pullback.fst f w`, `pullback.snd f w` |
| `Ỹ'=Y'×_Y Z`, `b`, `g̃` | `pullback g w`, `pullback.fst g w`, `pullback.snd g w` |
| `X̃'=X'×_Y Z`, `c` | `pullback (f' ≫ g) w`, `pullback.fst (f' ≫ g) w`; the structure map to Y is `f' ≫ g = g' ≫ f` |
| Induced `f̃'` | `kunBaseChangeRightMap f' g w`, built by Mathlib `pullback.map` with components `f'`, `𝟙 Z`, `𝟙 Y` |
| Induced `g̃'` | `kunBaseChangeTopMap sq w`, the same construction with components `g'`, `𝟙 Z`, `𝟙 Y` and `sq.w` |
| Comparison square B | `(IsPullback.of_hasPullback f w).toCommSq` |
| Comparison square C | `kunBaseChangeComparisonSquare f' g w`; its commutativity is Mathlib's `pullback.lift_fst` |
| Base-changed square | `kunBaseChangedSquare sq w`; its commutativity is the two `pullback.lift_snd` equalities |
| `gb = w g̃` | `pullback.condition (f := g) (g := w)` in `kunBaseChangeSourceIso` |
| `g'c = a g̃'` | `(pullback.lift_fst _ _ _).symm` in `kunBaseChangeTargetIso` |
| `s=(cᴰ_{w,g̃})⁻¹ ∘ cᴰ_{g,b}` | `kunBaseChangeSourceIso g w`: the inverse of the upstream comparison for `(b,g)`, then the upstream comparison for `(g̃,w)`, with shared composite `b ≫ g` |
| `t=(cᴰ_{a,g̃'})⁻¹ ∘ cᴰ_{g',c}` | `kunBaseChangeTargetIso sq w`: the inverse comparison for `(c,g')`, then the comparison for `(g̃',a)`, with shared composite `c ≫ g'` |
| Left vertical `g̃⁻¹(Ex_B) ∘ s` | `kunBaseChangeLeft f g w K`, explicitly defined by these two factors |
| Right vertical `Rf̃'_*(t) ∘ Ex_C` | `kunBaseChangeRight sq w K`, explicitly defined by these two factors |
| Top horizontal `b⁻¹(Ex_square)` | The `.map` expression in `kun_bc_base_change_cube` |
| Bottom horizontal `Ex_squarẽ` at `a⁻¹K` | The final argument to `CommSq` in that theorem |
| Diagram commutes unconditionally | `CommSq top left right bottom`, meaning `top ≫ right = left ≫ bottom` |
| Both vertical maps invertible | Exactly the two `IsIso` instance hypotheses of `kun_bc_base_change_identification` |
| Identification under those isomorphisms | `top = kunBaseChangeLeft ... ≫ bottom ≫ inv (kunBaseChangeRight ...)` |

The two square abbreviations are transparent names for existing Mathlib projection equalities,
not new axioms or postponed proofs. The four maps of schemes are the actual projections and
induced maps, and both natural comparison isomorphisms are actual composites of the recorded
inverse-image comparisons. No choice of an unspecified morphism or natural isomorphism occurs.
These helpers belong to the arrows already introduced in this node's statement; no new notion
or additional DAG node is needed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`,
  including its inherited `CommSq`, chosen `isoPullback`, `hom_fst`, and `hom_snd`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`. Its full coefficient hypotheses and
  functor signature were read. `DerivedComparison.baseChange_eq_derivedBaseChangeMapPlus`
  identifies this recorded interface with the adjunction-mate definition.
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`:
  `AlgebraicGeometry.Etale.derivedInverseImageComposition`. Its full signature/docstring
  identify the existing `upperStarCompDerivedPlus` inverse with the node's `cᴰ`.
- Mathlib `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`,
  `pullback.lift_fst`, `pullback.lift_snd`, and `IsPullback.of_hasPullback`, from the recorded
  fibre-product module and its imports. The universal property and scheme pullback instances
  were read in the pinned Mathlib sources.
- Proof import `Sheaf.Paper.ExchangeIdentityPasting`:
  `AlgebraicGeometry.Etale.derivedExchange_identity_pasting`, whose full horizontal-pasting
  clause and proof docstring were read. Its module is imported without `public`.

The live sources of the two `Sheaf.AlgebraicGeometry` dependencies were also read with
`scompile.py --source`; they agree with the local recorded interfaces. No dependency repair
or statement correction is necessary. There is no `STATEMENT-DISPUTED` fault in this statement.

Edge cases checked before finalizing the statement: empty schemes and empty fibre products
are allowed by the scheme pullback construction; zero complexes and all cohomological shifts
are allowed by the arbitrary bounded-below `K`; identity `u₀` and identity `w` still use the
canonical composition comparisons rather than assuming pullback is strictly unital. Neither
pasting nor cube commutativity needs smoothness, properness, torsion, a characteristic
restriction, or invertibility of an intervening exchange. The final conditional theorem alone
assumes the two vertical comparisons are isomorphisms, just as the node says.

Searches actually run:

- `msearch.py leansearch "Derived exchange morphisms for étale sheaves commute with successive
  base change and a base change cube"`: service unavailable (Internal Server Error).
- `msearch.py leanfinder "derived exchange base change compatibility further base change
  cartesian square"`: eight generic Guitart-exactness/Kan-extension hits; no derived étale cube.
- `msearch.py loogle "derivedBaseChangeMapPlus, derivedExchange_identity_pasting"`: no hits;
  the service does not know the project declaration.
- `msearch.py loogle "CategoryTheory.mateEquiv_vcomp"`: one generic mate-calculus hit; its
  source signature does not state this derived étale lemma.
- `msearch.py grep "derivedExchange_identity_pasting|baseChange_eq_derivedBaseChangeMapPlus"
  CategoryTheory` and `msearch.py grep "baseChange.*(cube|paste)|derivedBaseChange|kunBaseChange"
  CategoryTheory`: no Mathlib hits.
- `rg` in upstream `WeilConjectures/SixFunctors/BaseChange` found
  `derivedBaseChangeMapPlus_paste_horiz` in `DerivedPasting/Horizontal.lean`; the whole
  declaration/docstring were read. This gives the generic first-clause calculation, but
  not the node's two-clause statement with its canonical cube and conditional identification.
- `rg` in `lean/Sheaf` found `derivedExchange_identity_pasting`, the recorded proof dependency,
  and strict-henselization stalk-comparison uses. `scompile.py --source
  WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons` was read: its public
  comparison arrows are specialized to sheaves placed in degree zero and include a
  single-complex identification, and its arbitrary-complex cube theorem is private.
  It therefore does not provide an existing public statement of the current node.
- `rg` for the item's identifier and all proposed declaration names in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no duplicate.

The source [Stacks Remark 0E47](https://stacks.math.columbia.edu/tag/0E47) was opened and its
successive-base-change formula agrees with the four factors. The cube is the node's two-route
application of that formula, not an assertion that comparison exchange maps are invertible.

## Second reading by Q22

I independently read the current DAG node and the entire delivered module, then opened the
four statement dependencies and their recorded declarations. The sandbox node differs from
the shared node only in `lean`; it has no stage-2 `statement_change`, new node, or dependency
repair. I also read the original blueprint paragraph and Stacks `sites-cohomology.tex`,
Remark 0E47 (`remark-compose-base-change-horizontal`, lines 4093 onward), together with
Remark 07A7 immediately before it. The literature files are absent from this shared clone;
the available read-only copies are under `/home/ubuntu/work-bp/sheaf/literature/`.
The reviewed stage-1 node explicitly supplies the two-route cube consequence. Stacks assumes
commutative diagrams of ringed topoi; its horizontal-pasting assertion imposes no properness,
smoothness, torsion, invertibility, or finiteness assumption. Exact inverse image of abelian
etale sheaves gives the bounded-below specialization in the node.

My object/hypothesis/conclusion checklist, formed from the node before comparison:

| Node item | Lean rendering and independent verdict |
| --- | --- |
| Schemes X', X, Y', Y and morphisms g', f', f, g | Explicit `Scheme.{u}` and morphism binders in all three theorems; exact. |
| Cartesian square with chosen identification alpha | `sq : ChosenCartesianSquare g' f' f g`; I opened its structure: it extends the correct `CommSq` and includes `isoPullback`, `hom_fst`, `hom_snd`; exact. |
| Abelian etale sheaves and bounded-below derived categories | `DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`; the same coefficient convention as the recorded composition dependency; exact. |
| The canonical exchange transformation | `derivedBaseChangeMapPlus ... sq.toCommSq`; I read its signature and definition in upstream `BaseChange/Derived.lean:129`, and the comparison with the mate in `DerivedComparison.lean:169`; exact. |
| Composition isomorphism cD from iterated inverse image to composite inverse image | The recorded `derivedInverseImageComposition` identifies cD with `(upperStarCompDerivedPlus ...).symm`; I read both this theorem and the upstream definition in `UpperLowerStarCoherence.lean:269`; exact. |
| Arbitrary u:Y'' to Y' in (1) | `Y'' : Scheme.{u}` and `u₀ : Y'' ⟶ Y'`, with no instance assumption; exact. |
| X'' and both projections v, f'' | `pullback f' u₀`, `pullback.fst f' u₀`, `pullback.snd f' u₀`; the recorded Mathlib constructions, exact. |
| Further Cartesian square | `IsPullback.of_hasPullback f' u₀`; exact. |
| Outer Cartesian square with induced identification | `.paste_horiz (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)`; it has top map `pullback.fst f' u₀ ≫ g'` and base map `u₀ ≫ g`; exact. |
| Every bounded-below K | Unrestricted `K` binder in the displayed category, in all three theorems; exact. |
| Clause (1), first factor cD inverse at Rf_*K | `(upperStarCompDerivedPlus ... u₀ g).hom.app (Rf_*.obj K)`; direction composite inverse image to iterated inverse image, exact. |
| Clause (1), pullback of original exchange | `(u₀)^*[...].mapDerivedCategoryPlus.map ((derivedBaseChangeMapPlus ... sq.toCommSq).app K)`; exact. |
| Clause (1), further exchange at g' inverse image of K | Exchange for the further pullback square evaluated at `(g')^*[...].mapDerivedCategoryPlus.obj K`; exact. |
| Clause (1), last factor Rf''_* of cD | Direct-image `.map` of `(upperStarCompDerivedPlus ... (pullback.fst f' u₀) g').inv.app K`; exact. |
| Clause (1), equality with outer exchange | `kun_bc_base_change` equates precisely these arrows; `≫` reverses the printed order of `∘`, as required; exact. |
| No invertibility of an exchange in (1) | No `IsIso` hypothesis; exact. |
| Arbitrary w:Z to Y in (2) | `Z : Scheme.{u}`, `w : Z ⟶ Y`, unrestricted in both cube statements; exact. |
| X-tilde, a, f-tilde | `pullback f w`, its `fst`, and its `snd`; exact. |
| Y'-tilde, b, g-tilde | `pullback g w`, its `fst`, and its `snd`; exact. |
| X'-tilde and c | `pullback (f' ≫ g) w` and its `fst`, using the given structure map to Y; exact. |
| Induced f'-tilde | `kunBaseChangeRightMap f' g w`, defined by `pullback.map` with components f', identity on Z, identity on Y; exact. |
| Induced g'-tilde | `kunBaseChangeTopMap sq w`, defined by `pullback.map` with components g', identity on Z, identity on Y and the original commutativity; exact. |
| Cartesian comparison B | `(IsPullback.of_hasPullback f w).toCommSq`; exact. |
| Cartesian comparison C | `kunBaseChangeComparisonSquare f' g w` has top c, left f'-tilde, right f', bottom b; its actual pullback maps have the stated Cartesian universal property; exact. |
| Base-changed square | `kunBaseChangedSquare sq w` has exactly top g'-tilde, left f'-tilde, right f-tilde, bottom g-tilde; the original Cartesian property makes this Cartesian; exact. |
| Identification gb = w g-tilde | `pullback.condition` used as the equality argument to the second composition isomorphism in `kunBaseChangeSourceIso`; exact. |
| Identification g'c = a g'-tilde | `(pullback.lift_fst _ _ _).symm` used in `kunBaseChangeTargetIso`; exact. |
| s = cD(g,b) followed by inverse cD(w,g-tilde) | `kunBaseChangeSourceIso`: first upstream comparison `.symm`, then upstream comparison `.hom` through the shared diagonal; exact. |
| t = cD(g',c) followed by inverse cD(a,g'-tilde) | `kunBaseChangeTargetIso`: the same two-factor construction through `c ≫ g'`; exact. |
| Left vertical arrow g-tilde inverse image of Ex_B after s | `kunBaseChangeLeft f g w K`, defined by precisely these two factors; exact. |
| Right vertical arrow direct image of t after Ex_C | `kunBaseChangeRight sq w K`, defined by precisely these two factors; exact. |
| Top horizontal b inverse image of original exchange | The first argument of `CommSq` in `kun_bc_base_change_cube`; exact. |
| Bottom horizontal exchange of the base-changed square at a inverse image of K | The fourth argument of that `CommSq`; exact. |
| Unconditional diagram commutativity | `CommSq top left right bottom` asserts `top ≫ right = left ≫ bottom`; exact, with no invertibility hypotheses. |
| Conditional identification if both vertical maps are isomorphisms | Exactly `[IsIso (kunBaseChangeLeft ...)]` and `[IsIso (kunBaseChangeRight ...)]` in `kun_bc_base_change_identification`, with conclusion `top = left ≫ bottom ≫ inv right`; exact. |

Dependency and construction inspection: Mathlib `HasPullback.lean:95,111,115,128,270`
gives the chosen object, projections, universal map, and induced map; `Pullbacks.lean:485`
provides `HasPullbacks Scheme` without any geometric assumption. The source and target
comparison isomorphisms are actual composites of the existing inverse-image isomorphisms,
not arbitrary isomorphisms or `Nonempty` choices. The square abbreviations merely package
existing projection identities into `CommSq`. The eight helpers implement arrows explicitly
named in this node, rather than introduce an independent notion. No new/dependency module
requires an H12/H13 audit. The recorded proof dependency `derivedExchange_identity_pasting`
was opened: its clause (2) uses exactly the same composition directions and coefficients.

Edge cases: no index type is introduced, so no empty-index exclusion arises. All schemes may
be empty and all fibre products may be empty. The arbitrary K includes the zero object,
complexes concentrated in degree zero, every shift, and any bounded-below cohomological bound;
there is no n parameter or n > 0 restriction. Identity u or w is included using the canonical
composition isomorphisms, without identifying inverse image strictly with the identity.
There is no field, characteristic, torsion, Noetherian, or finite-type assumption. Universe u
is arbitrary, all finitely many schemes fit one common universe, and the coefficient universe
u+1 matches the dependency's small-etale-site convention. No unbound variable or universe is
present (`autoImplicit false` and explicit `universe u`).

Independent H4 searches (different queries from the first reader):

- `msearch.py ... leanfinder "Commutativity of the Beck Chevalley exchange cube for inverse
  image and right derived direct image on bounded below etale abelian sheaves" returned eight
  hits for sheafification/pushforward compatibility and ordinary module pullback composition;
  none states this derived etale cube. Their printed signatures concern underived functors.
- `msearch.py ... loogle '"CommSq", "rightDerivedFunctor"'` returned zero hits.
- `msearch.py ... leansearch "Commutative square of derived Beck Chevalley exchange
  transformations under further pullback"` returned service unavailable (Internal Server
  Error); this is recorded as unavailable, not as evidence of absence.
- `rg 'base[Cc]hange.*[Cc]ube|exchange.*[Cc]ube|derivedBaseChangeMapPlus_paste_horiz|kunBaseChange'`
  searched the pinned Mathlib, upstream WeilConjectures and project `lean/Sheaf`. I opened
  upstream `DerivedPasting/Horizontal.lean:61`: the existing horizontal-pasting theorem
  supplies clause (1)'s formal calculation, but not this node's full two-clause assertion.
  Other hits are stalk-comparison applications or the already recorded pasting dependency.
- I fetched the current `WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons`
  with `scompile.py --source` and read its full declarations. Its public comparison maps
  require a sheaf G placed in degree zero and insert the single-complex comparison;
  `exchangeCube_stalk_square` concludes a homology-stalk equality. Its arbitrary-complex
  `derivedExchangeCube_pasting` is private. Thus it does not provide a public declaration
  or reusable arrow with exactly the node's type; no existing record replaces this module.

H5/H6/H8/H9: all definitions have real pullback/composition data; the only postponed proofs
are the three named theorems, each `by sorry`. Their docstrings reproduce steps 1-2, steps
3-4, and the final cancellation, respectively, with source and blueprint id. All helper
and module docstrings have the source/id. There are no private copies, file-local notation,
local instances, theorem proofs, or added hypotheses. The maximum Lean line length is 91.
I compared `lean.statement` with the exact source slice from `theorem kun_bc_base_change`
through its type: they are verbatim equal, including newlines. Every public declaration is
listed in `lean.declarations`.

Mismatches and changes: none found. I preserved the Lean module and node record unchanged;
this second reading adds only this report section. `scompile.py Q22 lem-kun-bc-base-change
lean/Sheaf/Paper/KunBaseChange.lean` passed both the sandbox and library-file compilations
without errors or warnings (8.6 s and 10.2 s). No additional Lean files are delivered.
