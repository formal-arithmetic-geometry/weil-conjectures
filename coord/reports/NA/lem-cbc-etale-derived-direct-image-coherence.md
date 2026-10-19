# Stage-2 repair: lem-cbc-etale-derived-direct-image-coherence

## Worker report

This delivery states `AlgebraicGeometry.Etale.exists_normalizedDerivedDirectImageCoherence`
in `Sheaf.Paper.EtaleDerivedDirectImageCoherence`. Its proof is `sorry`; there are no new
definitions, no arbitrary chosen maps, and no postponed data. The node was copied from the
current shared repository and changes only in `lean`. In particular, this delivery does not
repeat the returned stage-1 `mathlib_searches` edit. The sandbox initially contained only
brief files, with no node, Lean module, or report to retain. The returned head's defects are
repaired by the actual stage-2 module and record here.

The source is the locally read `literature/stacks-project/sites-cohomology.tex`, Tag 0D6E,
`lemma-derived-pushforward-composition`, lines 4011–4030. Its general ringed-topos composition
statement is specialized to constant coefficients and bounded-below derived categories. The
normalization, uniqueness, and coherence package is the node's eight-step expanded proof.
The declaration docstring carries all eight steps and identifies the existing derived
associativity theorem that stage 3 can use. The node's statement and proof are unchanged.

Hypotheses and clauses, in the order they occur in the node:

- A commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`. There is no `Finite`,
  torsion, invertibility, nonzero-ring, or residue-characteristic assumption.
- All schemes are `Scheme.{u}`. All maps are unconstrained categorical morphisms. The
  existential family `d` quantifies over every composable pair of arbitrary scheme maps;
  the associativity clause quantifies over `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ W`.
- The coefficient sheaves are precisely `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`,
  the recorded six-functor encoding of constant-ring modules. Their bounded-below derived
  categories are `DerivedCategory.Plus` of this category, the bounded-below full subcategory
  of the recorded `Etale.DerivedCategoryModule Λ T`. The existing
  `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)` is used for every derived direct image.
- `d f g fg w` is an isomorphism from `R(fg)_*` to `Rf_* ⋙ Rg_*`, i.e. to `Rg_*` after
  `Rf_*` in ordinary functional notation. The optional naming in the source's `lowerStarComp`
  is represented by `fg : X ⟶ Z` and `w : fg = f ≫ g`. This allows the associativity and
  unit laws to have a common source, without treating propositionally equal scheme maps as
  definitionally identical. It adds no assumption: `fg = f ≫ g` always has the instance
  `fg := f ≫ g`, and an arbitrary named equal composite is equality transport of that one.
- Localization `Q_X I` is `DerivedCategory.Plus.Qh.obj I`, with
  `I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and
  `∀ n : ℤ, Injective (I.obj.as.X n)`. Thus lower bounds may be arbitrary integers.
  Passing through the homotopy category does not change localization of complexes.
- The first conjunct is the normalization equation
  `alpha_fg ≫ d = Q(c_fg) ≫ alpha_g(f_*I) ≫ Rg_*(alpha_f)`.
  Here `alpha_v` is `(lowerStar ... v).rightDerivedFunctorPlusUnit.app`, and `Q(c_fg)` is
  `Qh.map ((NatTrans.mapHomotopyCategoryPlus (lowerStarComp ...).inv).app I)`.
  `lowerStarComp` is the existing fibre-product comparison in the opposite direction;
  its inverse is exactly the direction prescribed in the node. All three alpha maps are
  isomorphisms on these complexes, including the middle one because `f_*` preserves
  injectives. Accordingly the displayed equation is equivalent to the node's component
  formula after canonical computation. It does not replace normalization by an arbitrary
  isomorphism or by compatibility up to unspecified isomorphisms.
- The second conjunct is uniqueness: any natural transformation `c` with these source and
  target functors whose components agree with `d` at every injective representative equals
  `d.hom`. The first conjunct identifies those components with the required normalized
  maps, so this is exactly uniqueness under the stated normalization. Equality of natural
  transformations also determines natural isomorphisms (their inverses are determined).
- The existential family `e T` supplies `R(id_T)_* ≅ 𝟭`. The third conjunct normalizes it:
  `alpha_id ≫ e_T = Q(lowerStarId.hom)` on every bounded-below injective complex. This is
  precisely the node's identity direct-image comparison, with its computation map shown.
- The fourth conjunct is associativity of `d`: first `d (f ≫ g) h`, then whisker `d f g`
  by `Rh_*`; alternatively first `d f (g ≫ h)`, then whisker `d g h` by `Rf_*`.
  Both start at `R((f ≫ g) ≫ h)_*`. The second path explicitly uses `Category.assoc f g h`
  to name this composite. The end functors are definitionally equal associative composites,
  just as in the published `rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc`.
- The fifth conjunct is `(d f (𝟙 Y)).hom ≫ whiskerLeft Rf_* (e Y).hom = 𝟙 Rf_*`, exactly
  `(d_Y Rf_*) ∘ d_{id_Y,f} = id` in the node's functional notation.
- The sixth conjunct is `(d (𝟙 X) f).hom ≫ whiskerRight (e X).hom Rf_* = 𝟙 Rf_*`, exactly
  `(Rf_* d_X) ∘ d_{f,id_X} = id`. These are equalities of natural transformations.

Dependency declarations used and read:

| Node | Module and declarations |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| `def-weil-pbc-derived-categories` | `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus` |
| `def-weil-pbc-direct-image` | `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`; `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`: `Etale.rightDerivedLowerStarPlus`, `Etale.lowerStarIdDerivedPlus` |
| `def-sp-injective-resolutions` | `Mathlib.CategoryTheory.Preadditive.Injective.Basic` / `.Resolution`: `CategoryTheory.Injective`, `InjectiveResolution`; the statement uses degreewise `Injective` |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections and universal property; the existing `lowerStarComp` is built from the canonical pullback-composition isomorphism |

Also read `GrothendieckTopology.lowerStarComp` and `lowerStarId` in
`WeilConjectures.SixFunctors.UpperLowerStar.Defs`, and the étale specialization in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`. These docstrings explicitly
identify the canonical fibre-product maps. No private alternative construction is introduced.

The proof imports include the published
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`, with
`Etale.preservesInjectiveObjects_lowerStar` and
`Etale.rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc`; the latter proves the inverse
orientation of the fourth conjunct. The definitions and factorization statements of
`Functor.rightDerivedFunctorPlusCompIso'`, `rightDerivedFunctorPlusCompUnit`, and
`rightDerivedFunctorPlusIdIso` were read in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`. Thus the
canonical witness in stage 3 is the inverse primed comparison and the existing derived
identity isomorphism. The exact-inverse-image and enough-injectives proof dependencies are
imported through `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` and
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`; the right-adjoint and injective-derived
computation/Hom tools are the recorded Mathlib declarations (including
`DerivedCategory.Plus.exists_injective_nonempty_iso` and
`DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`). These imports carry the proof plan;
no theorem was proved for stage 2.

Edge cases checked: the empty scheme and zero ring require no excluded nonemptiness/nonzero
hypotheses; zero complexes and arbitrary negative lower bounds are allowed; identity edges
are included in the quantified family and the two unit clauses use correctly oriented
`comp_id` / `id_comp` equalities. Arbitrary nonproper, non-quasi-compact, nonfinite-type maps
and infinite coefficient rings remain included. There is no bounded-above or constructible
condition. The coefficient and site sizes are the dependency's published `u+1` convention,
not an extra identification of distinct site universes.

Searches actually performed in this repair:

- `msearch.py ... leanfinder "Normalized composition isomorphisms of bounded below etale
  derived direct image for arbitrary scheme maps with injective normalization uniqueness
  associativity and unit laws"`: eight hits about scheme normalization, no full match.
- `msearch.py ... loogle "CategoryTheory.Functor.rightDerivedFunctorPlusCompIso"`: no hits,
  because that upstream identifier is outside Loogle's Mathlib index. The upstream source
  was therefore located and read directly, rather than treating this as evidence of absence.
- `msearch.py ... leansearch "composition of right derived pushforward functors associativity
  unit normalization on injective complexes"`: eight hits, including `rightDerived_fac_assoc`,
  `rightDerivedNatTrans_comp_assoc`, and `SheafOfModules.pushforward_assoc`. These are generic
  functoriality or underived module coherence, not the full node.
- `msearch.py ... grep "derivedDirectImageCoherence" WeilConjectures`: no hits.
- `rg` of the upstream and shared `lean/Sheaf` sources for `lowerStarComp`,
  `rightDerivedFunctorPlusCompIso`, `rightDerivedLowerStarPlus`, `DerivedCategoryModule`, and
  the item's id located the partial interfaces above. A full-name check for
  `exists_normalizedDerivedDirectImageCoherence` found no declaration in Mathlib, upstream,
  or `lean/Sheaf`. The partial canonical construction `Etale.lowerStarPlusCompIso` in the
  side framework's `SmoothBaseChange/FailureOverField/ClosedOpen` was read; it does not state
  the normalization/uniqueness/coherence package. The delivery uses the general underlying
  construction through its proof plan and introduces no second definition.

No node correction, missing notion, or disputed statement was needed. The live source of
`WeilConjectures.AlgebraicGeometry.DerivedCategories`, absent locally, was read with the
prescribed `scompile.py --source` command. No missing-local-file workaround was used.

Validation: the final 114-line module compiled through `scompile.py` with exit 0, no errors,
and no non-sorry warnings: sandbox check 44.0 s, server library confirmation 29.4 s. The same
final text is the source of the node's verbatim `lean.statement`. Delivery dry run and push
are performed after this report and recorded by the delivery wrapper.

## Second reading by NA

The dispatcher expressly prohibited starting other agents, so this is a separate in-thread
second reading of the final node and Lean text, not a claim of review by another worker.
The maintainer's independent immutable-head review remains the external second review.

I reopened the node and final file and checked the actual six-conjunct statement. The
coefficient ring has only `CommRing`; all scheme maps have no property instances. The
existential witnesses are natural isomorphisms of the recorded D-plus functors, not arbitrary
objectwise identifications. The first conjunct has exactly the direction `alpha_fg ≫ d` and
uses `lowerStarComp.inv`; all three computation maps are displayed. The uniqueness test
quantifies over every injective representative, with no fixed lower bound, and concludes
actual equality of natural transformations. The identity normalization uses `lowerStarId.hom`.
The two associativity paths start at the same named triple composite, and `Category.assoc`
has the necessary orientation. The final two clauses have the unit on Y whiskered on the
left by Rf, respectively the unit on X whiskered on the right by Rf, and both conclude the
identity of Rf. This matches all node clauses and excludes none of its edge cases.

The earlier scratch draft had reversed composite order and misoriented unit paths, and its
normalization failed to display the correct composite computation map. These were replaced
with the explicit final existential-family formulation before the clean compile. No scratch
declaration, `True` placeholder, diagnostic `#check`, max-heartbeat override, local notation,
local instance, or partial package remains. Only the named theorem's proof is `sorry`.

Returned H1/H2: repaired by the module, lean-only node delta, verbatim complete record and
both report sections. H3–H9: checked against the node/source clause by clause above, using
the dependency declarations and canonical fibre-product comparison. H10: final module has
clean per-file compilation and server confirmation. H11: this section records the precise
reading and the draft mismatches corrected, without fabricating another worker.
