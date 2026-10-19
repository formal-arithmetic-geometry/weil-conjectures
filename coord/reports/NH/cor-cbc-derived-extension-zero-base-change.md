## Worker report

The module `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange` states
`AlgebraicGeometry.Etale.derivedExtensionZeroBaseChange`. The only theorem has proof
`sorry`. Its two helper definitions have real data: the existing canonical underived
exchange and composition isomorphisms, transported through the existing exact-functor
localization and its canonical composition comparisons. No new independent notion,
new node, dependency repair, or statement correction is needed.

Hypothesis and clause correspondence:

- The four schemes and square arrows are explicitly quantified. An open-immersion
  square is expressed by `sq : IsPullback gU j' j g` and the two `IsOpenImmersion`
  instances. This is precisely the property carried by the recorded
  `AlgebraicGeometry.OpenImmersionSquare`, with its irrelevant chosen pullback
  identification forgotten. In detail, a recorded square `s` gives this proof by
  `IsPullback.of_iso_pullback s.toCommSq s.isoPullback s.hom_fst s.hom_snd`;
  conversely `sq.isoPullback` with its projection equations gives the chosen datum.
  Thus no different geometric notion or additional condition on `g` is imposed.
- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This follows the recorded coefficient universe of `DerivedCategoryModule` and
  covers any finite ring by the usual size lift, including the zero ring.
- `K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat Λ))` is exactly
  the recorded D⁺(U_et, Λ); the target category is the same encoding on X'.
  The existing `Functor.mapDerivedCategoryPlus` restricts each exact functor to D⁺.
- `extensionZeroBaseChangeDerivedPlusIso Λ sq` has source functor
  `j_!.mapDerivedCategoryPlus ⋙ g^*.mapDerivedCategoryPlus` and target functor
  `gU^*.mapDerivedCategoryPlus ⋙ j'_!.mapDerivedCategoryPlus`, in the displayed
  node orientation. Its data is the inverse of the precise recorded
  `openImmersionLowerShriekBaseChangeMap`, lifted by
  `Functor.mapDerivedCategoryPlusNatIso`, with both composite-factorization
  identifications `Functor.mapDerivedCategoryPlusCompIso` included.
  Thus it is the specified map, not an arbitrary isomorphism or an existence choice.
- The first conjunct asserts `IsIso` for every component K and the naturality
  equation for every derived morphism `t : K ⟶ L`. Naturality is for all derived
  morphisms, not only chain maps or degree-zero objects.
- The second conjunct treats the identity square `IsPullback.id_horiz j`.
  Its equation compares the exchange with the identity after both endpoint
  `upperStarIdDerivedPlus` identifications. The surviving arrow is precisely the
  identity on j_!K under those identifications.
- The third conjunct handles successive arbitrary base changes. It compares the
  exchange for `sq'.paste_horiz sq` with the pullback of the first exchange and
  the second exchange. `upperStarCompDerivedPlus h g` expands the source;
  `upperStarCompDerivedPlus hU gU` in its inverse direction recombines the target.
- The fourth conjunct handles composable open immersions. It compares the exchange
  for `sqk.paste_vert sqj` with the two successive exchanges, inserting the inverse
  of `extensionZeroCompDerivedPlusIso Λ k j` at the source and the forward
  comparison for k',j' at the target. This helper is exactly the localized inverse
  of the recorded `openImmersionLowerShriekComp`, so it is the canonical comparison
  of lem-cbc-extension-zero-composition. This equation is equivalent to Step 3's
  equation after moving its invertible source comparison across the equality.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `AlgebraicGeometry.OpenImmersionSquare`,
  inheriting `ChosenCartesianSquare` (full structure and projection equations read).
  Its square property is used as described above; its choice plays no role in the map.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, with its upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, Mathlib `DerivedCategory.Plus`.
  The node's main `torsionCohomology` declaration is not needed, since this item
  imposes no torsion-cohomology condition beyond finite coefficients.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`,
  `isIso_openImmersionLowerShriekBaseChangeMap`, and
  `unit_map_openImmersionLowerShriekBaseChangeMap_app` (full signatures and
  docstrings read). The first is the opposite-direction mate; its inverse is used.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus`, `mapDerivedCategoryPlusNatIso`,
  `mapDerivedCategoryPlusCompIso` (read their exactness hypotheses and definitions).
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `upperStarIdDerivedPlus`, `upperStarCompDerivedPlus` (definitions read).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`:
  `openImmersionLowerShriekComp` (the canonical left-adjoint comparison, definition read).

Modules of all recorded proof dependencies are imported (those with no recorded
module cannot yet be imported). The docstring contains the complete five-step
proof plan, including transpose normalization, both pasting directions, descent
through localization and restriction to D⁺. No proof dependency is used as an extra
hypothesis, and no pending proof node is needed to construct the maps.

Edge cases checked before writing: empty schemes or empty opens still admit all
exact functors and adjunctions; no nonemptiness, nonzero-ring, separatedness,
Noetherianity, finite-type or flatness hypothesis occurs. The zero complex and
complexes with any integer lower bound are included. The identity comparisons are
explicit, and pasting allows identity morphisms or identity open immersions.
Both directions of the comparison have been checked against the node's diagram.
All universes and variables are explicitly bound; no local notation or instances
are needed to read the statement outside its module.

Searches (2026-10-15):

- `msearch.py ... leansearch "Derived extension by zero base change on etale sheaves"`:
  service unavailable, Internal Server Error; no mathematical conclusion drawn.
- `msearch.py ... leanfinder "Derived extension by zero for an open immersion commutes
  with arbitrary base change naturally with identity and pasting"`: eight hits,
  mainly Zariski `Scheme.Modules.restrictFunctorComp` and open-immersion section
  identities; none supplies the small-etale D⁺ statement with both coherences.
- `msearch.py ... loogle '"mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso"'`:
  zero hits.
- `msearch.py ... grep 'extensionByZero|openImmersionLowerShriekBaseChange'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in upstream SixFunctors/Etale/Derived and LowerShriek/OpenImmersion finds
  `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` on unbounded derived
  categories, and refinement-specific comparisons. Read the full unbounded file:
  it supplies the precise construction but neither the requested D⁺ statement nor
  its general identity and two pasting laws. Its construction is reused through
  the existing bounded-below exact-functor API, rather than defining new sheaf data.
- `rg` in this project's lean/Sheaf finds `ExchangeIdentityPasting` for derived
  direct image, not extension by zero; read its comparisons to check orientation.
- `rg` for the blueprint id in the upstream WeilConjectures tree finds no hit.
  `rg` for all three proposed names in upstream, lean/Sheaf and
  dag/lean_names_upstream.json finds no collision.

Validation: prescribed scompile.py compiled the entire module cleanly, including
all proof-dependency imports. No warnings or errors. No STATEMENT-DISPUTED flag.
The independent second reading is left to the dispatcher's next worker.

## Second reading by NH

I independently read the node, its blueprint source, Stacks etale-cohomology.tex
at lemma-shriek-base-change (03S6) and lemma-jshriek-open (0F70), and derived.tex
at lemma-right-derived-exact-functor (015F), with the delivered Lean open.
03S6 assumes an arbitrary scheme morphism and an etale immersion; the present
open-immersion specialization needs no finiteness, flatness or separation
hypothesis on the base change. 015F applies to exact functors of abelian
categories. The blueprint adds finite commutative coefficients and the stated
coherences, exactly as the DAG node does.

My object/hypothesis/conclusion checklist and verdicts:

1. Four schemes U', U, X', X and all four arrows: the first conjunct binds
   `U' U X' X : Scheme.{u}`, `gU`, `j'`, `j`, `g` with exactly the diagram's
   domains and codomains. Pass.
2. Cartesian square with open vertical arrows and no condition on g:
   `sq : IsPullback gU j' j g`, `[IsOpenImmersion j]` and
   `[IsOpenImmersion j']`. I opened both `OpenImmersionSquare` and its parent
   `ChosenCartesianSquare`. The recorded chosen isomorphism respects both
   projections, so it is uniquely determined by the square. The IsPullback
   presentation forgets only that redundant choice, not any geometric condition;
   `sq.isoPullback` reconstructs it, and `IsPullback.of_iso_pullback` forgets it.
   No private square definition or extra base-change hypothesis is present. Pass.
3. Finite commutative ring Lambda: the section variable is
   `(Λ : Type (u + 1)) [CommRing Λ]`; the theorem adds `[Finite Λ]`.
   I opened `DerivedCategoryModule` in Derived.Coefficients and the dependency
   DerivedCategories module: this is their prescribed coefficient and site size.
   Finite coefficients can always be represented at that size. Pass.
4. Every K in D+(U_et,Lambda), with output in D+(X'_et,Lambda):
   `DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
   and the two functor endpoints of `extensionZeroBaseChangeDerivedPlusIso`.
   The exact-functor API restricts the existing unbounded derived functor to the
   full subcategory of cohomologically bounded below objects, with no fixed
   lower bound. These are the dependency node's categories. Pass.
5. The particular canonical map, not an arbitrary isomorphism: the helper uses
   the inverse of `openImmersionLowerShriekBaseChangeMap`, exactly the recorded
   declaration of lem-cbc-extension-zero-base-change. I read its definition,
   isomorphism theorem and `unit_map_openImmersionLowerShriekBaseChangeMap_app`:
   its transpose is the unit followed by the square identification specified
   by the node. `mapDerivedCategoryPlusNatIso` localizes that inverse, with
   `mapDerivedCategoryPlusCompIso` and its inverse identifying the endpoints.
   I read those API definitions, not just their names. Pass.
6. Isomorphism for every K and naturality: first conjunct states `IsIso` of
   the helper's component and the naturality equation for every `t : K ⟶ L`
   in D+, including derived morphisms not represented by a single chain map.
   The helper is already an Iso; the IsIso clause records the requested fact.
   Pass.
7. Identity for identity base change: second conjunct uses
   `IsPullback.id_horiz j`; the exchange followed by j_! of the upper identity
   comparison equals the lower identity comparison at j_!K. I read
   `upperStarIdDerivedPlus`, which localizes the ordinary identity comparison.
   Thus both endpoint identifications are canonical and the resulting map is
   the identity. Pass.
8. Successive arbitrary base changes: third conjunct binds a second cartesian
   square `sq'`, and compares `sq'.paste_horiz sq` with pullback of the first
   exchange followed by the second. `upperStarCompDerivedPlus h g` expands
   the source and the inverse comparison for hU,gU recombines the target.
   I checked the composition comparison's source and target in its definition.
   The order is h inverse-image after g inverse-image. Pass.
9. Successive open immersions: fourth conjunct binds k,k',j,j' and the two
   cartesian squares, then uses `sqk.paste_vert sqj`. The source comparison
   is g inverse-image of the inverse of `extensionZeroCompDerivedPlusIso`;
   the two exchanges follow, then the forward comparison for k',j'. I read
   `openImmersionLowerShriekComp`: it is the canonical adjunction comparison
   from extension along the composite to the composite functor, so the helper
   correctly localizes its inverse. Rearranging the invertible source
   comparison gives exactly Step 3's displayed vertical pasting equation. Pass.

Edge cases: empty schemes and opens, the zero ring and zero complex are all
included. There is no Nonempty, Nontrivial, characteristic, Noetherian, finite-type
or separatedness condition. Every integer lower bound is allowed, including
complexes concentrated in degree zero and negative shifts. There is no index
set to restrict. Identity arrows are permitted in both pasting laws. Universe u
and the section coefficient binder are bound explicitly; coefficient categories
match the recorded small-etale derived-category encoding. No extra typeclass
hypothesis is hidden in the theorem's section.

Independent H4 searches: msearch LeanFinder query "Open immersion etale
exceptional inverse image exchange identity composition bounded below derived"
returned eight ordinary scheme/open-immersion identities, none this statement.
Loogle `"openImmersionLowerShriekComp"` returned no hits. LeanSearch query
"Etale sheaves extension by zero derived base change" was unavailable with
Internal Server Error; no absence conclusion is based on it. msearch grep
`shriek|extensionByZero` in AlgebraicGeometry returned no Mathlib hits.
I also searched Mathlib's AlgebraicGeometry and CategoryTheory/Sites trees
for extension by zero and LowerShriek, the upstream Etale/Derived tree for
base-change, composition and coherence, and lean/Sheaf for the helper names
and related exchange statements. The unbounded
`mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` supplies the existing
underived-map localization pattern but has different derived-category endpoints;
refinement D+ comparisons concern compactifications, not arbitrary squares.
No existing general D+ exchange with both pasting clauses was found. Neither
helper's name nor the theorem's name collides with the upstream name inventory
or either source tree.

No new nodes, dependency modules, statement correction, hollow data, or new
postponed helper theorem occurs. The only theorem has `sorry`; the two definitions
contain real canonical isomorphism data. Source/blueprint docstrings cover every
declaration, and the theorem docstring follows all five DAG proof steps, including
normalization, both pastings, localization and bounded-below restriction.
No mathematical mismatch was found; I left the Lean and node unchanged.

Second-reader validation: scompile.py compiled the single delivered module cleanly
against its overlay and library (3.0 s / 3.5 s), with no errors or warnings.
