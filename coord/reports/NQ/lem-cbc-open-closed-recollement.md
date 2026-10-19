## Worker report

The module `Sheaf.AlgebraicGeometry.OpenClosedRecollement` states
`AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed`, with one sorry and no new
notions or proofs. The node statement is unchanged.

Hypothesis and clause correspondence:
- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Schemes are `{X U Z : Scheme.{u}}`; their two maps are `(j : U ⟶ X) (i : Z ⟶ X)`.
  The immersion hypotheses are `[IsOpenImmersion j] [IsClosedImmersion i]`.
- Complementarity is `hij : Set.range i.base = (Set.range j.base)ᶜ`. This allows arbitrary
  presentations of both immersions, not just a chosen reduced closed complement.
- D⁺ is `_root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`,
  the exact coefficient encoding required by the derived-categories dependency record.
- The existential `δ` chooses a connecting morphism simultaneously for every such `K`.
  Its source is the composite of `upperStar ... i` and `lowerStar ... i`, each restricted
  by `mapDerivedCategoryPlus`; its target is the shifted composite of `upperStar ... j`
  and `openImmersionLowerShriek ... j`. Thus the outer terms are precisely i_*i⁻¹K and
  j_!j⁻¹K, obtained termwise from the exact functors, all within D⁺.
- `∀ K, Triangle.mk ... (δ K) ∈ distTriang _` says that each displayed triangle is
  distinguished in D⁺. The first arrow is exactly the counit of
  `derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat Λ) j`.
  The second is exactly the unit of
  `(upperStarLowerStarAdjunction (ModuleCat Λ) i).mapDerivedCategoryPlusAdjunction`.
- The last conjunct quantifies over every `K`, `K'` and `f : K ⟶ K'`. It asserts
  B(f) ≫ δ(K') = δ(K) ≫ A(f)[1], with B=i_*i⁻¹ and A=j_!j⁻¹.
  The first two squares of the triangle morphism follow from naturality of the specified
  counit and unit. The final conjunct supplies exactly the third square, with all three
  components prescribed functorially. It does not merely ask for an arbitrary map of cones.

Dependency declarations read and used:
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the record identifies D with
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and D⁺ with `DerivedCategory.Plus` of
  module-valued étale sheaves. The new statement uses that same latter category literally.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, and
  `openImmersionLowerShriekUpperStarAdjunction`, via the public derived-adjunction import.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, and `upperStarLowerStarAdjunction`,
  via the same public import.
- The two convention dependencies explicitly define no additional notion and record
  `Scheme`, `IsOpenImmersion`, and `IsClosedImmersion` as their relevant Mathlib leaves.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` supplies the named
  bounded-below derived adjunction. `Adjunction.mapDerivedCategoryPlusAdjunction` in
  `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction` induces the closed one.
- `WeilConjectures.SixFunctors.Finite.Exact` supplies
  `preservesFiniteColimits_lowerStar_of_isFinite`; closed immersions are finite by Mathlib.
  This instance makes the *exact*, termwise direct image available without any additional
  exactness assumption. Every stated proof-dependency module is imported; the only proof
  dependency without a module record is the Mathlib closed-immersion-finite leaf, already
  available through these imports. ExactFunctor is transitively publicly imported.

Edge cases checked: empty X, empty U, empty Z, the zero coefficient ring, and zero complexes
are allowed. No nonempty, nonzero, Noetherian, separated, characteristic, or bounded-degree
hypothesis is imposed. K ranges over all bounded-below objects with their own bounds; there
is no common bound restriction. The coefficient universe follows the dependency's recorded
six-functor encoding and excludes no finite ring up to the usual universe lift.

Searches for an existing statement:
- `msearch.py ... leanfinder "Functorial open closed recollement distinguished triangle of
  etale module sheaves"`: eight hits (Scheme.Etale.forget, Scheme.Modules.pseudofunctor,
  etale locus and module restriction results); none states this triangle.
- `msearch.py ... loogle '"recollement"'`: zero hits.
- `msearch.py ... grep 'openClosed|recollement'`: searched Mathlib; no exact match.
- `rg` in upstream WeilConjectures, project lean/Sheaf, and the upstream name index for
  `openClosed`, `recollement`, and the proposed full declaration name. The upstream module
  `WeilConjectures.SixFunctors.OpenClosed.Derived` has `exists_distTriang_openClosed`.
  Its full signature gives a connecting map separately for each unbounded object and
  uses the right-derived direct image. It has no naturality clause. It therefore does not
  state this node, whose essential extra assertion is one natural connecting-map family.
  Existing short exact sequence and complex-triangle declarations are used as proof inputs,
  not duplicated. The chosen new declaration name has no hit.
- Searched the upstream source for the exact node id; no existing declaration for it.

No statement correction, new node, dependency replacement, or STATEMENT-DISPUTED flag is
needed. The module docstring records all four proof steps from the node, including descent
of naturality through inverses of quasi-isomorphisms. Validation uses server-only scompile.py
and the deliver2.py dry run; no local compiler or library build is used.


## Second reading by NQ

Independent second reader: read the node, original blueprint lemma, Stacks
etale-cohomology.tex lemma-ses-associated-to-open (095L), derived.tex
lemma-derived-canonical-delta-functor (0152), and lemma-right-derived-exact-functor
(015F). The source assumes arbitrary schemes and an abelian coefficient category, not
Noetherian schemes or invertible coefficients. The finite commutative coefficient ring
is the blueprint's own restriction. The DAG's more explicit counit/unit and naturality
clauses faithfully specify the blueprint's triangle and adjunction compatibility.

Object, hypothesis, and conclusion checklist (all pass):

- Coefficients: finite commutative ring Lambda is `(Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]`; neither a field nor a nonzero ring is required.
- Objects: arbitrary schemes Z, U, X are `{X U Z : Scheme.{u}}`. The maps are the
  binders `(j : U ⟶ X) (i : Z ⟶ X)`; their types have the right directions.
- Immersions: `[IsOpenImmersion j] [IsClosedImmersion i]` give exactly the two specified
  hypotheses. `hij : Set.range i.base = (Set.range j.base)ᶜ` gives precisely the
  complementary images; it does not require the reduced closed subscheme.
- Category and quantifier: K ranges over `DerivedCategory.Plus (Sheaf
  X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, the bounded below full subcategory
  specified by def-weil-pbc-derived-categories, not bounded complexes with a fixed bound.
- Left term: `openImmersionLowerShriek ... j` applied after `upperStar ... j`, each
  through `mapDerivedCategoryPlus`, is exactly the termwise exact j_! j^{-1} K.
- Middle term: the counit and unit are both evaluated at the same K.
- Right term: `lowerStar ... i` applied after `upperStar ... i`, through the same
  exact-functor construction, is i_* i^{-1} K. This is direct image, not an arbitrary
  right-derived replacement. The finite-direct-image exactness instance applies since
  Mathlib makes a closed immersion finite; no extra hypothesis is in the signature.
- First arrow: `(derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus ... j).counit.app K`
  is the counit of the exact derived extension-by-zero/inverse-image adjunction.
- Second arrow: `(upperStarLowerStarAdjunction ... i).mapDerivedCategoryPlusAdjunction.unit.app K`
  is the exact derived inverse-image/direct-image unit.
- Connecting map and distinguishedness: the single existential `δ : ∀ K, ...` supplies
  maps from the right term to the left term shifted by `(1 : ℤ)`. `∀ K, Triangle.mk
  ... (δ K) ∈ distTriang _` asserts exactly distinguishedness in this D^+.
- Functoriality: the final `∀ K K' (f : K ⟶ K')` equality is
  B(f) ≫ δ(K') = δ(K) ≫ A(f)[1]. This is the third triangle-morphism square for the
  prescribed components A(f), f, B(f); the other two squares are naturality of the
  fixed unit and counit. Existential choice before K, K', f retains simultaneous
  naturality rather than unrelated choices of cones.

Dependency declarations were opened, not inferred from names: DerivedCategories.lean;
UpperLowerStar/Defs.lean (`lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`);
LowerShriek/OpenImmersion/Defs.lean (`openImmersionLowerShriek`, its exactness and
adjunction); Derived/OpenImmersionLowerShriek.lean (bounded below derived adjunction);
CategoryTheory/DerivedCategory/Adjunction.lean (`mapDerivedCategoryPlusAdjunction` and
its unit compatibility with the termwise unit); Finite/Exact.lean (finite direct-image
exactness); and Mathlib's TStructure.lean (`DerivedCategory.Plus`). The conventions
nodes introduce no independent objects. These declarations have the required
module-valued small-etale types; all coefficient and resolution instances are supplied
for ModuleCat by imports, not added as assumptions. There are no new definition nodes
or replacement dependency modules in this delivery.

Edge cases: empty X (hence empty U and Z), empty U, empty Z, zero K, the zero coefficient
ring, and arbitrary characteristic are included. No indexing set or degree n is bound
by this lemma; its shift is explicitly integer 1. Scheme universe u is arbitrary,
and the coefficient/sheaf universes match the recorded six-functor encoding. Finite
rings can be lifted to that universe. No variable or universe is unbound.

Independent searches, using different words from the first reader:

- msearch leanfinder: "natural localization triangle of bounded below derived etale
  sheaves for a closed subscheme and its open complement": eight unrelated etale-locus
  and localization hits, no recollement triangle.
- msearch loogle: `"distTriang"`: twelve generic triangulated-category declarations,
  no etale recollement theorem. An earlier combined-string query was rejected by
  Loogle's parser and is not counted as evidence.
- msearch grep: `localization.*triangle|triangle.*localization|recollement`: two
  monoid-localization comments, no match.
- Direct rg in Mathlib homological algebra, upstream WeilConjectures/SixFunctors/OpenClosed,
  and project lean/Sheaf for openClosed, recollement and localization/triangle words:
  existing short exact sequences and applications, but no identical statement.
  Opened the full `AlgebraicGeometry.Etale.exists_distTriang_openClosed` signature in
  OpenClosed/Derived.lean: it asserts a connecting map separately for each unbounded M,
  uses the right-derived direct image, and has no natural connecting-map family.
  It is therefore not this lemma. No definition is duplicated by the delivered theorem.

No mathematical or syntactic mismatch was found; Lean and node are unchanged. The
module and theorem docstrings give the source and blueprint id and all four proof
steps, including localization naturality. There is one named theorem with whole-proof
`sorry`, no hollow definition and nothing proved. Node lean.statement was compared
verbatim with the file's signature and agrees.

Validation: server-only scompile.py compiled OpenClosedRecollement.lean in 2.6 seconds,
with nice 19, two threads and a 60-second per-file limit; no errors or warnings.
Its required side import ExactFunctorDerivedFunctor.lean compiled in the private overlay
in 1.3 seconds. No local compiler or global build was run.
