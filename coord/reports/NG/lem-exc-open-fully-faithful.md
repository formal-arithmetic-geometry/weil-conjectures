## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedOpenImmersionFullyFaithful` states
`AlgebraicGeometry.Etale.derivedOpenImmersionFullyFaithful`, with a single `sorry` proof.
It introduces no definition and changes only the item's `lean` record. The statement is
coefficient-free, hence uses the abelian-sheaf interpretation of `D(T_et)` specified by
`def-weil-pbc-derived-categories`, without imposing a coefficient ring or finiteness,
Noetherian, quasi-compactness, boundedness, or constructibility hypotheses.

Hypothesis and conclusion correspondence:

- Schemes T and V and the open immersion g: `{T V Z : Scheme.{u}}`, `(g : V ⟶ T)`,
  `[IsOpenImmersion g]`.
- The closed complement i: `(i : Z ⟶ T)`, `[IsClosedImmersion i]`, and
  `(h : Set.range i.base = (Set.range g.base)ᶜ)`. This is the usual arbitrary closed
  immersion whose underlying closed set is the complement, allowing the canonical
  reduced complement as well as its scheme structures, which have equivalent small
  étale sites. In particular it does not replace complementarity by mere disjointness.
- The derived categories without a coefficient ring are
  `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})` and the identical
  constructions for V and Z, as the dependency's module documentation specifies.
  The scheme universe is u; abelian group coefficients have the prescribed u+1 size.
- `Rg_*` is `(lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor`, the upstream
  unbounded total derived functor of the recorded direct image. Its required resolutions
  and derived-category instances come from the upstream Grothendieck abelian API, not
  additional hypotheses.
- `Lg^*` is `(upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory`: exact inverse image
  descends termwise to the derived category. This is the exact-functor representative of
  the derived pullback, as prescribed by the first node proof step. It avoids imposing
  monoidal flat-resolution assumptions needed only by the separate K-flat presentation.
- `Lg^* Rg_* ≅ id` is `Nonempty (Rg_* ⋙ Lg^* ≅ 𝟭 ...)`. Functor composition is written
  in Lean's order, so direct image comes first. This is existence of a *natural*
  isomorphism, not merely unrelated objectwise isomorphisms.
- `i_*` in the second displayed identity is the termwise closed-immersion direct image,
  exactly as the fourth proof step stipulates. It is
  `(lowerStar AddCommGrpCat.{u + 1} i).mapDerivedCategory`. A closed immersion is finite,
  so `Etale.preservesFiniteColimits_lowerStar_of_isFinite` supplies exactness; no such
  assumption is added to the theorem.
- `Lg^* i_* = 0` is `∀ K : DerivedCategory (Sheaf Z.smallEtaleTopology
  AddCommGrpCat.{u + 1}), IsZero ((i_* ⋙ Lg^*).obj K)`. Objectwise zero is equivalent to
  this composite being a zero functor: its maps and the natural identifications with a
  zero functor are uniquely determined. It is categorical vanishing, not definitional
  equality to a chosen zero object.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`: the documented coefficient-free category
  is Mathlib `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, and
  `upperStarLowerStarAdjunction` (full signatures and construction documentation read).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`: the documented generic
  `rightDerivedFunctor` and `mapDerivedCategory` encodings, and
  `AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`. No duplicate derived
  functor definition is introduced.
- `WeilConjectures.SixFunctors.Finite.Exact`:
  `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite` supplies the
  exactness instance for termwise closed direct image.

The stated proof dependencies are imported without `public`, including their recorded
Mathlib leaves: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`
(`AlgebraicGeometry.Etale.fullyFaithfulLowerStarOfIsOpenImmersion`),
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
(`CategoryTheory.Functor.mapDerivedCategoryFactors`),
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`
(`CochainComplex.IsKInjective.Qh_map_bijective`),
`Sheaf.CategoryTheory.KInjectiveTotalDerived`
(`CategoryTheory.exists_rightDerived_of_enough_isKInjective`),
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
(`CategoryTheory.Adjunction.preservesKInjectiveComplexes`),
`WeilConjectures.SixFunctors.OpenClosed.Vanishing`
(`AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range`),
`Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
(`AlgebraicGeometry.Etale.upperStar_abelian_exact`), and
`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
(`CochainComplex.etale_kinjective_resolutions_exist`). Their docstrings and signatures were
read. The last recorded theorem is for module sheaves; the abelian-sheaf K-injective
instance is already supplied by the imported Grothendieck abelian framework. No new
interface is required to type this statement.

Edge cases checked mathematically: V empty (both composites vanish in the zero derived
category), V=T with g the identity (the complement is empty, the first composite is the
identity), T empty, zero complexes, arbitrary unbounded complexes, and nonreduced closed
complements. No degree bound or finite coefficient restriction is present. No hypothesis
is automatic for arbitrary i and g: the complement equality excludes overlapping closed
and open ranges and nonexhaustive disjoint pairs. All variables and the universe u are
explicitly bound, and `autoImplicit` is false.

Existing-declaration searches:

- `msearch.py ... leansearch "Derived inverse image direct image along an open immersion
  is identity"`: service unavailable (Internal Server Error); recorded as unavailable,
  no mathematical verdict based on this service.
- `msearch.py ... leanfinder "For an open immersion of schemes the derived inverse image
  of the derived direct image is naturally isomorphic to the identity and inverse image
  kills direct image from the closed complement"`: eight hits concerning scheme open
  immersion maps on sections, none on these derived functors.
- `msearch.py ... loogle "Functor.rightDerivedFunctor, Functor.mapDerivedCategory"`:
  zero hits, unknown identifier `Functor.rightDerivedFunctor` in the search index.
- `msearch.py ... grep "open.*fully.*faithful|fully.*faithful.*open|upperStar.*lowerStar"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... grep "derived.*[Oo]pen|[Oo]pen.*derived" CategoryTheory`: zero hits.
- Direct `rg` in Mathlib AlgebraicGeometry and Algebra/Homology/DerivedCategory with the
  same open/full-faithfulness and upperStar/lowerStar patterns: no match.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf` for
  `lem-exc-open-fully-faithful|derivedOpenImmersionFullyFaithful`: no existing declaration.
  The upstream name index `dag/lean_names_upstream.json` also has no match.
- Broader upstream and side-library searches found the underived open direct-image
  full-faithfulness theorem, the objectwise module-coefficient
  `AlgebraicGeometry.Etale.mapDerivedCategoryUpperStarRightDerivedLowerStarIso` in
  `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage`, and
  `AlgebraicGeometry.Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range`
  in `WeilConjectures.SixFunctors.OpenClosed.Derived`. Their source signatures were read:
  the former is objectwise and uses module coefficients; the latter is only the
  vanishing clause and uses derived direct image. Neither states both clauses of this
  node as a natural isomorphism plus termwise closed-direct-image vanishing for abelian
  sheaves. The Zariski module-derived open-restriction theorems in the side library are
  on a different site and coefficient category.

The blueprint source file was read from the project server (the literature copy is not
present in this machine's shared checkout). Its two displayed assertions agree verbatim
with the DAG statement. The revised four-step DAG proof is followed, rather than the
source paragraph's already corrected extension-by-zero argument.

No statement correction, new nodes, or dependency modules are needed. No
`STATEMENT-DISPUTED` issue remains. The theorem proof is exactly `by sorry`, with the
four recorded proof steps in its docstring.

Validation: the prescribed `scompile.py` wrapper compiled the statement in its private
side overlay. Final clean compilation and the delivery dry run are recorded below.

## Second reading by NG

I read the DAG node statement, its source place (blueprint node `lem-exc-open-fully-faithful`,
order 1809, fetched read-only from the server), its enclosing unit and chapter, the
dependency records, and the complete Lean module. The node introduces:

- schemes `T`, `V`, and `Z` in one universe, an open immersion `g : V ⟶ T`, and a closed
  immersion `i : Z ⟶ T` whose underlying range is the complement of the range of `g`;
- the coefficient-free derived categories of sheaves of abelian groups on the small etale
  sites of `T`, `V`, and `Z`;
- the two conclusions `Lg^* Rg_* ≅ id` and `Lg^* i_* = 0`.

The Lean binders `{T V Z : Scheme.{u}}`, `(g : V ⟶ T) [IsOpenImmersion g]`,
`(i : Z ⟶ T) [IsClosedImmersion i]`, and
`h : Set.range i.base = (Set.range g.base)ᶜ` render exactly those objects and the
complement hypothesis. The first conclusion is rendered as
`Nonempty ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor ⋙
(upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory ≅ 𝟭 ...)`; this is `Rg_*` followed
by the exact derived inverse image, hence `Lg^* Rg_* ≅ id` in Lean's composition order.
The second is rendered as the objectwise categorical vanishing
`∀ K, IsZero (((lowerStar ... i).mapDerivedCategory ⋙
(upperStar ... g).mapDerivedCategory).obj K)`, exactly expressing `Lg^* i_* = 0`.
No coefficient ring, boundedness, finiteness, Noetherian, constructibility, or extra
universes are assumed. The recorded declarations for `DerivedCategory`, `lowerStar`,
`upperStar`, `IsOpenImmersion`, and `IsClosedImmersion` were opened and match these uses;
no duplicate notion or dependency repair is needed.

I checked the empty open, identity open, empty ambient scheme, zero derived object,
unbounded complexes, and nonreduced closed complement cases. They remain covered by the
same unrestricted binders and complement equality. The complement hypothesis permits
arbitrary closed subscheme structures on that closed set, as the source does: its etale
site is unchanged by the reduced-complement identification. There is no degree or index
parameter and no characteristic restriction to test.

Existing-declaration searches were repeated with `rg` over Mathlib, `WeilConjectures`, and
`lean/Sheaf`, using `counit`, `complement`, and `open inclusion` as additional search words.
I also independently ran `msearch.py ... leanfinder` with the query "Counit of the derived
restriction and direct image adjunction for an open inclusion of schemes is invertible;
restriction of a sheaf supported on its complement is zero": eight hits, all on ordinary
Zariski scheme modules or open-immersion sections, not the required derived etale result.
The independent Loogle query `"counit", "Derived"` returned four generic derived-functor
counit declarations, with no etale open-immersion statement. These results are recorded
in the search log. The worker's LeanSearch attempt was unavailable, as recorded above.
I opened the two upstream derived near-matches named in the worker report: the first is
objectwise with module coefficients; the second is only the vanishing clause (for arbitrary
Grothendieck abelian coefficients) and uses right-derived direct image. Neither states this
node in full. No duplicate statement or missing definition was found.

The only mismatch was in the opening docstring sentence: it reversed the verbal order of
the two functors. I changed it to "derived direct image followed by derived pullback";
the Lean signature already had the correct order and remains unchanged. All four node
proof steps and source/blueprint references are present in the docstring; the sole proof
is `sorry`. There are no definitions, hollow data, local notation, or unbound variables.
The module compiles cleanly through the required `scompile.py` wrapper; the final delivery
checks compile the edited module again.
