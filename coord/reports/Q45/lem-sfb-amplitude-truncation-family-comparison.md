## Worker report

Item: lem-sfb-amplitude-truncation-family-comparison, group Q45, stage 2.

The module `Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison` states
`DerivedCategory.amplitude_truncation_family_comparison`. Its only declaration is
this theorem, with proof `by sorry`. No definitions, axioms, helper theorems,
new nodes, dependency repairs, or statement corrections are introduced.
Only the item's `lean` record changes.

Source read: the complete current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md`,
particularly Étale statements (finite cohomological window for unbounded inputs)
and Transfer (compatibility with sums). The nine-step abstract argument in the
node expands this application, and is reproduced in the theorem docstring.

Hypothesis-by-hypothesis correspondence:

- A and B: `A : Type uA`, `B : Type uB`, their independent
  `Category.{vA}` / `Category.{vB}` structures, `[Abelian A]`, `[Abelian B]`, and
  `[IsGrothendieckAbelian.{w} A]`, `[IsGrothendieckAbelian.{w} B]`. The indexing
  universe is the same w, as in the node's fixed universe. Mathlib permits the
  object and actual Hom universes to remain independent; Grothendieck structure
  supplies local w-smallness and w-small colimits. No equality between these
  universes is imposed.
- Ordinary unbounded derived categories: `DerivedCategory A` and
  `DerivedCategory B`, with explicitly bound `[HasDerivedCategory.{dA} A]` and
  `[HasDerivedCategory.{dB} B]`. These are localization choices, available for
  every Grothendieck category through the imported upstream construction, not
  bounded variants or extra mathematical assumptions.
- Isomorphism-invariant class: `P : ObjectProperty A` and
  `[P.IsClosedUnderIsomorphisms]` use Mathlib's existing predicate and class.
- Contains zero: `hPzero : P 0`, where the scoped Mathlib `ZeroObject` instance
  interprets 0 as the chosen categorical zero object. Isomorphism invariance
  makes this equivalent to containing any zero object.
- Closed under every small coproduct: `hPsum : ∀ (J : Type w) (X : J → A),
  (∀ j, P (X j)) → P (∐ X)`. This includes the empty indexing type and does
  not impose extension or subquotient closure.
- Exact triangulated functor commuting with integer shifts:
  `G : DerivedCategory A ⥤ DerivedCategory B`, `[G.CommShift ℤ]`,
  `[G.IsTriangulated]`. Mathlib infers additivity from these structures.
- Nonnegative amplitude: `c : ℕ`; every cohomological bound uses the integer
  coercion `(c : ℤ)`.
- Lower bound on every object: `hGge` universally quantifies L and a and states
  `L.IsGE a → (G.obj L).IsGE a`, without a P condition.
- Upper amplitude on P-cohomology objects: `hGle` quantifies L and b, assumes
  `L.IsLE b` and `∀ j : ℤ, P ((homologyFunctor A j).obj L)`, and concludes
  `(G.obj L).IsLE (b + (c : ℤ))`.
- Small family: `I : Type w`, `K : Discrete I ⥤ DerivedCategory A`.
  A discrete diagram is exactly an I-indexed family, with its morphisms exactly
  componentwise maps. `hK` imposes P-cohomology for every s and every integer j.
  There is no Nonempty instance, common bound, or boundedness predicate.
- The degree is an arbitrary integer `m : ℤ`.

Clause-by-clause correspondence and the four arrows:

Write t for Mathlib's `DerivedCategory.TStructure.t` in this explanatory report,
U_s = `(t.truncLE m).obj (K.obj ⟨s⟩)`, and
V_s = `(t.truncGE (m - (c : ℤ))).obj U_s`. No local notation or private
abbreviation is introduced in the Lean module.

- The first conjunct quantifies over s and states `V_s.IsGE (m - (c : ℤ))`,
  `V_s.IsLE m`, and `∀ j : ℤ, P ((homologyFunctor A j).obj V_s)`.
  Thus all V_s have P-cohomology and the same closed interval of support.
- The upper arrow is exactly `t.truncLEι m`, with component U_s → K_s.
- The lower arrow is exactly
  `Functor.whiskerLeft (t.truncLE m) (t.truncGEπ (m - (c : ℤ)))`,
  with component U_s → V_s. Neither arrow is replaced by an existential map.
- For an arrow α between endofunctors of D(A),
  `(Functor.whiskeringRight (Discrete I) (DerivedCategory A)
  (DerivedCategory A)).map α` is the natural transformation on the family
  category whose component is `Functor.whiskerLeft K α`.
- The second conjunct takes this transformation for the upper arrow and
  right-whiskers by `colim ⋙ G ⋙ homologyFunctor B m`, then evaluates at K.
  Its component is precisely `H^m(G(⊕ u_s))`.
- The third conjunct does the same for the lower arrow. Its component is
  precisely `H^m(G(⊕ v_s))`.
- The fourth conjunct first right-whiskers the upper arrow by G, forms its
  family transformation via `whiskeringRight (Discrete I) D(A) D(B)`, and
  right-whiskers by `colim ⋙ homologyFunctor B m`. Its component is precisely
  `H^m(⊕ G(u_s))`.
- The fifth conjunct does the same with the lower arrow. Its component is
  precisely `H^m(⊕ G(v_s))`.
- Every comparison is asserted `IsIso` in B, not equality of objects or an
  unspecified isomorphism. Here `colim` is Mathlib's colimit functor on
  discrete diagrams in the ordinary derived category. Its map is `colimMap`,
  determined by `colimit.ι_map`; these are exactly the specified ambient
  coprojections, before or after G as appropriate.
- Naturality is encoded by writing the four maps as components of actual
  natural transformations on the full category of families. Their `.naturality`
  fields give the required square for every componentwise family morphism;
  restricting to families with P-cohomology yields the stated natural
  isomorphisms. Inverses of these componentwise isomorphisms are natural as
  well. No choice of arbitrary comparison is involved.

Dependency declarations read and used:

- def-sp-grothendieck-abelian: Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian`, its `hasColimits`, and the AB4 consequence.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`; and
  Mathlib.Algebra.Homology.DerivedCategory.HomologySequence,
  `DerivedCategory.homologyFunctor` and its localization factorization.
- def-weil-triangulated-category: Mathlib.CategoryTheory.Triangulated.Pretriangulated,
  `CategoryTheory.Pretriangulated`; Mathlib.CategoryTheory.Triangulated.Functor,
  `CategoryTheory.Functor.IsTriangulated` together with `CommShift ℤ`.
- def-sbc-standard-tstructure-derived-category:
  Mathlib.Algebra.Homology.DerivedCategory.TStructure,
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsLE`, `DerivedCategory.IsGE`,
  and their cohomological characterizations `isLE_iff` / `isGE_iff`.
- def-kun-truncations: imports its recorded
  Sheaf.CategoryTheory.TruncationsAndHomotopyColimits. As its module documentation
  specifies, the good derived truncations are the existing standard t-structure
  functors. The telescope predicate recorded as that composite node's primary
  declaration is not the good-truncation operation. The item uses the public
  Mathlib constructions `TStructure.truncLE`, `truncGE`, `truncLEι`, `truncGEπ`;
  it does not redefine any component of the dependency.
- lem-kun-grothendieck-derived-coproducts: proof import
  Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit,
  `DerivedCategory.isColimit_mapCocone_grothendieckSum`.
- lem-sfb-arrow-exact-colimits: proof import
  Sheaf.CategoryTheory.ArrowExactColimits, `CategoryTheory.Limits.arrow_exact_colimits`.
- src-weil-homology-preserves-exact-colimits: proof import
  WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits, its instance
  preserving colimits for `HomologicalComplex.homologyFunctor` under exact colimits.
- lem-sf-derived-homology-long-exact: the publicly reachable
  `DerivedCategory.HomologySequence.exact₁`, `exact₂`, `exact₃`, and `δ` in
  Mathlib.Algebra.Homology.DerivedCategory.HomologySequence.
- lem-sf-derived-truncation-triangle: the public import
  Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT, specifically
  `CategoryTheory.Triangulated.TStructure.triangleLEGE_distinguished`.
- lem-sfb-grothendieck-filtered-finite-limits: Mathlib's
  `IsGrothendieckAbelian.hasLimits`, `.hasColimits`, and
  `HasExactColimitsOfShape.preservesFiniteLimits`, reachable through the imports.

The additional upstream public imports supply available constructions, not
extra assumptions: `HasDerivedCategory.ofIsGrothendieckAbelian` in
WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory, and
`DerivedCategory.hasColimitsOfShape_discrete` in
WeilConjectures.CategoryTheory.DerivedCategory.Coproducts. In particular both
ambient derived coproducts elaborate without separately postulating their
existence. All recorded proof modules are imported or publicly reachable;
no import-cycle omission is needed.

Searches performed via the prescribed msearch.py wrapper:

- leanfinder: "A triangulated functor of finite cohomological amplitude gives
  uniform good truncation comparisons in degree m for families and coproducts".
  Eight results, including `TStructure.truncGE`, `truncLT`, `triangleLTGE`, and
  `Functor.IsHomological.mk'`. None states the four comparisons.
- loogle: `DerivedCategory.homologyFunctor, "trunc"`: zero results.
- grep: `truncLE|truncGE|[Aa]mplitude` in Algebra/Homology/DerivedCategory:
  fourteen results in TStructure, Fractions and Plus, only individual truncations.
- leansearch: "A functor with finite cohomological amplitude induces isomorphisms
  on degree m cohomology of both canonical truncation maps for arbitrary
  coproduct families". Eight results on individual truncation and exactness
  constructions; none states the family assertion.
- rg on lean/WeilConjectures and lean/Sheaf for amplitude/truncation combinations
  and the item id: found
  WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude.
  Its exported theorem `DerivedCategory.isIso_sigmaComparison_of_bounded` has
  extra assumptions on a triangulated subcategory and bounded coproduct
  preservation, and concludes invertibility of sigmaComparison. Its proof
  contains local facts analogous to the four comparisons, but no exported
  declaration states this node. Its two individual cohomology/Sigma lemmas
  likewise do not have the node's statement. The complete module was read.
- rg of the proposed declaration/module name in dag/lean_names_upstream.json,
  lean/WeilConjectures, and lean/Sheaf: no match.

Edge cases checked before writing: empty I (a discrete empty diagram has zero
coproduct, G is additive, all four zero-to-zero maps are invertible); zero input
objects; the zero abelian category; c = 0 (V_s is supported only in degree m);
negative m; unbounded families with no uniform bound. All are admitted by the
binders and the finite-window argument. The upper truncation triangle's last
term is ≥ m+1; the lower triangle's first term after G is ≤ m-1. Thus both
adjacent terms in each relevant long exact sequence vanish, including at the
endpoints c = 0 and m arbitrary. No false-statement flag or node fault was found.

Validation: prescribed scompile.py cleanly compiled both the sandbox check and
the actual library module (14.0 s and 11.1 s); no errors or warnings. An initial
elaboration pass found missing namespace scopes for Mathlib's categorical zero
object and functor whiskering. Opening the existing namespaces fixed those
syntax/interface issues; no mathematical hypothesis changed.

## Second reading by Q45

A separate self-review pass compared the written signature with the full node,
its source, and its dependency interfaces. The dispatcher explicitly forbids
starting other agents; independent review is performed by the maintainer.
This section records the worker's second pass, not an independent reviewer.

The review checked each hypothesis above, in particular the universally
quantified lower bound without P, the upper bound only with P-cohomology,
closure under every w-small coproduct, and arbitrary dA/dB localization sizes.
It expanded all four whiskering expressions: the first two apply colim before G,
the last two apply G before colim; the lower arrow is evaluated on truncLE m K,
and the endpoint is m-c. The transformations retain their naturality in arbitrary
family maps. The window clause includes both bounds and P in every degree.
Empty I and c = 0 remain included. No mismatch or correction was needed after
the namespace-scope elaboration repair. There is exactly one postponed theorem,
with all nine natural-language proof steps, and no definition containing sorry.
