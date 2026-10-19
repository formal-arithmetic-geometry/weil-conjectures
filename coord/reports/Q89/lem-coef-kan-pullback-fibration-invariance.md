## Worker report

The new module `Sheaf.AlgebraicTopology.KanPullbackFibrationInvariance` states
`SSet.Enhanced.isWeakHomotopyEquivalence_pullback_map`, with its sole proof `sorry`.
No definition, auxiliary theorem, or new node is introduced. The node is copied
from the current shared DAG and changed only in `lean`; in particular its already
reviewed stage-1 statement and four-step proof are preserved.

Source read: [Kerodon Proposition the project server, Tag 0109](https://kerodon.net/tag/0109),
including its displayed diagram, statement, and proof. It states precisely the
arbitrary-simplicial-set result, with weak vertical maps and the two left legs Kan
fibrations. The module docstring records this source. The theorem docstring gives
the node's four proof steps in order, using the existing right-properness node.
No statement correction or STATEMENT-DISPUTED issue was found.

Hypothesis and clause correspondence:

- The six small simplicial sets are `{X₀ X X₁ Y₀ Y Y₁ : SSet.{u}}`, for an explicit
  arbitrary universe `u`. They are unrestricted objects of the simplicial-set
  category, not objects of its Kan-complex subcategory.
- The first cospan is `(f : X₀ ⟶ X) (g : X₁ ⟶ X)`; the second is
  `(f' : Y₀ ⟶ Y) (g' : Y₁ ⟶ Y)`.
- The objectwise comparison maps are `(α : X₀ ⟶ Y₀) (β : X ⟶ Y) (γ : X₁ ⟶ Y₁)`.
- The square equations are `hf : f ≫ β = α ≫ f'` and
  `hg : g ≫ β = γ ≫ g'`. Lean composes in diagrammatic order, so these are exactly
  the two displayed equations of the node.
- The three weak homotopy equivalences are the separate hypotheses
  `hα : IsWeakHomotopyEquivalence α`, `hβ : IsWeakHomotopyEquivalence β`, and
  `hγ : IsWeakHomotopyEquivalence γ`. This is the recorded realization-based
  predicate, including bijectivity on path components and on all positive based
  homotopy groups, with all source basepoints quantified.
- The Kan-fibration hypotheses are `[Fibration f] [Fibration f']`, under
  `open scoped SSet.modelCategoryQuillen`. Mathlib's scoped fibration structure
  is exactly `modelCategoryQuillen.J.rlp`, where `J` ranges over every horn in
  each dimension `n + 1`, with all vertices `Fin (n + 2)`. Thus dimensions start
  at one, both outer horns occur, and no dimension-zero nonemptiness condition
  has been added.
- The conclusion is
  `IsWeakHomotopyEquivalence (pullback.map f g f' g' α γ β hf hg)`.
  The existing `pullback.map` is defined as the universal pullback lift of
  `pullback.fst f g ≫ α` and `pullback.snd f g ≫ γ`. This gives exactly the
  coordinate formula `(x₀, x₁) ↦ (α(x₀), γ(x₁))` under the canonical degreewise
  description of limits of presheaves. No arbitrary comparison map is supplied.
- No `KanComplex`, `IsFibrant`, nonempty, or connected hypothesis occurs, and
  neither `g` nor `g'` is assumed to be a fibration.

Dependencies and declaration sources read in full:

- Statement dependency `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the docstrings and signatures of
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `componentsMap`, and
  `homotopyGroupMap` were read. The predicate uses the actual `SSet.toTop` map,
  path components and boundary-relative based cube homotopy classes.
- Mathlib module `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`,
  declarations `SSet.modelCategoryQuillen.J`, its scoped
  `CategoryWithFibrations SSet` instance, `fibrations_eq`, and `fibration_iff`:
  these give exactly the node's Kan-fibration notion without defining it again.
- Mathlib module `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback.map`, lines 260–275: its full signature,
  docstring, and body were read. It is the actual strict pullback comparison.
- Proof dependency `lem-coef-kan-quillen-right-proper`, module
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen`: its full docstring and signature
  were read. It supplies the model structure, functorial factorizations,
  boundary-lifting characterization including degree zero, and right properness
  for arbitrary bases. It is imported without `public` as a proof dependency.

Edge cases checked before writing: empty simplicial sets and empty pullbacks are
allowed; the component condition on weak equivalences prevents a false empty to
nonempty equivalence. A point base gives the product special case. Identity maps
and identity fibration legs fit the same comparison map. The horn range includes
dimension-one outer horns and does not impose a dimension-zero lift. Arbitrary
non-Kan bases and non-Kan objects are retained by the absence of fibrancy binders.
No extra universe equalities or size restrictions beyond small `SSet.{u}` occur.

Searches actually run with `msearch.py Q89 lem-coef-kan-pullback-fibration-invariance`:

- `leanfinder`, query `Objectwise weak homotopy equivalences of cospans of
  simplicial sets induce a weak equivalence on pullbacks when both left legs
  are Kan fibrations`: eight hits, principally the two trivial-fibration
  pullback weak-equivalence instances, fibration base-change instances, fibrant
  object comparison, and Brown factorization. None states this comparison.
- `loogle`, query `"pullback.map", "WeakEquivalence"`: zero hits.
- `grep`, query `pullback.*weakEquivalence|weakEquivalence.*pullback`: six hits
  in `PathObject.lean`, `JoyalTrick.lean`, and `Instances.lean`. Read the pertinent
  signatures and bodies: `Instances.lean` 225–246 requires a leg itself to be a
  trivial fibration, `PathObject.lean` 273–286 concerns gluing chosen path objects,
  and `JoyalTrick.lean` 69–96 is a lifting-property lemma. None is the statement
  or a one-line specialization of it.
- `leansearch`, query `Weak homotopy equivalence of strict pullbacks of
  objectwise weakly equivalent Kan fibration cospans`: eight hits. The additional
  `pullback.map_isIso` requires actual isomorphisms, not weak equivalences;
  fibration base change, trivial-fibration projection instances, and over-category
  retract stability do not give this arbitrary cospan comparison.

Direct `rg` searches were also run over Mathlib, upstream `WeilConjectures`,
project `lean/Sheaf`, and `dag/lean_names_upstream.json`, using the item id,
`pullback.*[Ii]nvarian|[Ii]nvarian.*pullback`,
`pullback.map.*[Ww]eak|[Ww]eak.*pullback.map`, and the proposed declaration name.
No exact existing theorem or name collision was found. Nearby project statements
include path-pullback comparison and right properness, which are different
statements. All searches are performed rather than inferred from earlier reports.

Validation: `scompile.py Q89 lem-coef-kan-pullback-fibration-invariance
lean/Sheaf/AlgebraicTopology/KanPullbackFibrationInvariance.lean` completed both
sandbox and library compilation cleanly. All variables and the universe are
explicitly bound; `autoImplicit` is disabled. The only postponed proof is the
item's theorem. The JSON `lean.statement` is copied verbatim from its signature.

## Second reading by Q89

I independently read the item node, its sandbox module, the statement dependency's
node and relevant declarations, and the complete proof-dependency theorem. I also
opened [Kerodon Proposition the project server (0109)](https://kerodon.net/tag/0109), including
its diagram and proof. This is a Kerodon source, not a Stacks tag. It explicitly
concerns simplicial sets and imposes no ambient Kan-complex, connectedness, or
nonemptiness assumption. Its two fibration hypotheses and three vertical weak
equivalences are exactly the node's. There is no `statement_change`, repair note,
new definition node, or dependency module in this delivery. Comparing sandbox and
shared node records found `lean` to be the sole changed field.

My object/hypothesis/conclusion checklist, with the Lean open:

1. Six arbitrary small simplicial sets: `{X₀ X X₁ Y₀ Y Y₁ : SSet.{u}}`.
   Verdict: exact. Mathlib `SSet` is `SimplicialObject (Type u)`, not the full
   subcategory of Kan complexes. The universe is explicitly declared and arbitrary.
2. Two cospans: `(f : X₀ ⟶ X) (g : X₁ ⟶ X)` and
   `(f' : Y₀ ⟶ Y) (g' : Y₁ ⟶ Y)`. Verdict: exact, with the same leg orientation.
3. Three comparison maps: `(α : X₀ ⟶ Y₀) (β : X ⟶ Y) (γ : X₁ ⟶ Y₁)`.
   Verdict: exact; all are actual simplicial maps.
4. Both squares commute: `hf : f ≫ β = α ≫ f'` and
   `hg : g ≫ β = γ ≫ g'`. Verdict: exact after translating diagrammatic
   composition into the node's function-composition order.
5. All three comparisons are weak homotopy equivalences: `hα`, `hβ`, `hγ`
   separately use `SSet.Enhanced.IsWeakHomotopyEquivalence` from the recorded
   `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Verdict: exact. I read
   `componentsMap`, `homotopyGroupMap`, and this predicate: realization induces
   a bijection on path components, and bijections on boundary-relative cubical
   based homotopy classes in every positive degree and at every source basepoint.
   Postcomposition preserves the group operation, so this is the stated
   homotopy-group isomorphism condition. Mathlib's `SSet.toTop` is geometric
   realization, defined as the left Kan extension of the standard topological
   simplices; it is not a replacement by a Kan complex.
6. The two left legs are Kan fibrations: `[Fibration f] [Fibration f']` under
   `open scoped SSet.modelCategoryQuillen`. Verdict: exact. I read Mathlib's
   `Fibration`, the scoped instance, `fibrations_eq`, and `J`: the latter ranges
   over `Λ[n + 1, i].ι` for every `n : ℕ` and `i : Fin (n + 2)`. Thus all
   positive-dimensional horns and both outer horns are included, with no
   dimension-zero lifting or inhabitance condition. Neither right leg is
   required to be a fibration.
7. The induced strict-pullback map is weak: the conclusion is
   `IsWeakHomotopyEquivalence (pullback.map f g f' g' α γ β hf hg)`.
   Verdict: exact. I read `pullback.map` in Mathlib's `HasPullback.lean`:
   it is the universal lift of `pullback.fst f g ≫ α` and
   `pullback.snd f g ≫ γ`. Since these are presheaf pullbacks, their canonical
   degreewise identifications give precisely `(x₀, x₁) ↦ (α(x₀), γ(x₁))`.
   No arbitrary map, homotopy-pullback replacement, or extra conclusion occurs.
8. No six-object Kan hypothesis: there is no `KanComplex` or `IsFibrant`
   binder. Verdict: exact. All objects and maps are bound before their properties;
   the class binders express properties of the two already fixed maps.

Edge cases: empty objects and empty strict pullbacks remain allowed. The
path-component bijection excludes an empty-to-nonempty weak equivalence, so the
positive-degree clause does not make that case vacuous. A terminal base gives
products, and identity comparisons give the identity pullback map. Degree zero
is represented by components, whereas horn lifting starts at dimension one.
Arbitrary non-Kan bases and total objects remain covered. All six objects may
lie in any common ambient universe `u`; no extra universe equation is imposed.
The empty-index, ring-characteristic, scheme, and zero-object cases do not add
parameters to this simplicial-set statement.

The theorem docstring follows all four node proof steps. I checked the graph
factorization and the two-out-of-three argument over an arbitrary fixed base;
the identification of the base changes of `s` and `t` with strict pullbacks;
the intermediate `E = Y₀ ×[Y] X`; and the final coordinate identifications with
`(Y₀ ×[Y] Y₁) ×[Y₁] X₁`. The result is the actual coordinate map in item 7.
The recorded proof dependency `SSet.KanQuillen.right_proper_kan_quillen` fixes
the realization weak equivalences and Mathlib's horn fibrations, supplies both
factorizations and boundary lifting, and states right properness without a
fibrant-base restriction. It is correctly imported without `public`.

Independent searches (performed with `msearch.py Q89` for this item):

- LeanFinder, `Reedy lemma weak equivalence between pullbacks of cospans with
  fibration left arrows`: eight hits. The two weak-equivalence projection
  instances in `ModelCategory/Instances.lean` require the pulled-back arrow
  itself to be a trivial fibration; the fibration instances only preserve the
  fibration property. `JoyalTrick` is a lifting theorem, and `PathObject.trans_P`
  concerns chosen path objects. I read the relevant source signatures; no match.
- Loogle, `"pullback.map", "Fibration"`: zero hits.
- Grep, `Reedy.*lemma|pullback.map.*[Ww]eak|[Ww]eak.*pullback.map|[Rr]ight[Pp]roper`:
  three weak categorical pullback hits, unrelated to weak homotopy equivalences.
- LeanSearch, the six-object pullback-square formulation with both left legs Kan:
  eight hits. `pullback.map_isIso` assumes three genuine isomorphisms;
  `weakEquivalences_over_iff` detects the underlying weak equivalence of a slice
  map without proving base-change invariance. The other categorical-square hits
  have no weak-homotopy-equivalence assertion. I opened the pertinent sources.
- Direct `rg` searches over Mathlib's algebraic topology sources, upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`,
  using Kan/pullback, weak/fibration, Reedy, right-proper, and the full proposed
  name, found no exact theorem or name collision. I opened the nearby project
  `kan_pullback_path_comparison`, `kan_homotopy_pullback_invariance`, and
  `simplicial_pullback_equivalence`: these concern a constant-path comparison,
  explicit homotopy pullbacks, and invertible vertices of enriched categories,
  respectively. None is this statement.

No mismatch was found, so I preserved the Lean module and node record. There
are no definitions or auxiliary postponed theorems; the item's sole theorem
has proof `by sorry`. Source/blueprint docstrings, namespaces, public statement
imports, proof-only import, and 100-character line widths satisfy the contract.
A direct comparison confirms that `lean.statement` equals the file's signature
verbatim. Every variable and universe is explicitly bound under
`set_option autoImplicit false`.

Second-reader validation: the prescribed `scompile.py Q89
lem-coef-kan-pullback-fibration-invariance
lean/Sheaf/AlgebraicTopology/KanPullbackFibrationInvariance.lean` completed both
sandbox and library compilation with no errors or warnings (1.1 s and 1.2 s).
Only this independent second-reading section was added to the delivery.
