## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleTorsorComparisonAffine` states
`AlgebraicGeometry.ProEtale.torsor_comparison_affine`. Its only theorem has proof `sorry`.
Two construction helpers abbreviate the existing original-site inverse image and equip it
with Mathlib's canonical monoidal structure from finite-product preservation. The latter
uses the already recorded comparison theorem; no proof obligation or chosen data is hidden.
No new nodes, dependency repairs, or statement corrections are needed.

Source read: current blueprint main-20261015,
`sec-proetale-coefficients/sk-lem-pe-torsor-comparison/sk-lem-pe-torsor-comparison-affine.md`
and its proof; Stacks `proetale.tex`, label `lemma-compare-cohomology-nonabelian`, Tag 099X.
The theorem docstring follows the node's expanded nine-step proof, including its specified
noncommutative left-action convention. The printed blueprint proof is less expanded;
the node already contains the finite-affine-refinement and overlap repairs.

Clause-by-clause correspondence:

- Affine scheme X: `(X : Scheme.{u}) [IsAffine X]`. No separatedness, Noetherianity,
  connectedness or coefficient-ring assumption is added.
- Sheaf of possibly noncommutative groups G_0 on X_et:
  `G₀ : Grp (Sheaf X.smallEtaleTopology (Type (u + 1)))`. This is Mathlib's bundled
  internal group object in the cartesian category of set sheaves. Its multiplication,
  unit and inverse are natural sheaf maps satisfying the group equations. Since the
  cartesian tensor and terminal object of set sheaves are sectionwise product and
  singleton, this is precisely a sheaf of groups, with no commutativity condition.
- G = nu_X^* G_0: the underlying sheaf is
  `(torsorComparisonPullback X).obj G₀.X`. Its group structure is Mathlib's
  `Functor.grpObjObj` (the same structure used by `Functor.mapGrp`), obtained through
  `torsorComparisonPullback_monoidal`. Its product map is the inverse canonical product
  comparison followed by the inverse-image multiplication; its unit and inverse are
  pulled back in the same canonical way. No unrelated group or arbitrary lift is bound.
- T a sheaf of sets on X_proet: the binder `T : Sheaf (Scheme.ProEt.topology X)
  (Type (u + 1))` uses the recorded weakly-etale site and its fpqc covering topology.
- Left action: `a : (torsorComparisonPullback X).obj G₀.X ⊗ T ⟶ T` is a sheaf map,
  so restriction compatibility is built in. `h_one` is the unit equation, and `h_mul`
  is the left associativity equation `(gh)t = g(ht)`, with the explicit associator
  accounting for product parentheses.
- The displayed pair-map isomorphism is exactly
  `h_iso : IsIso (lift a (snd ((torsorComparisonPullback X).obj G₀.X) T))`.
  Cartesian `lift` pairs the action and second projection, giving `(g,t) ↦ (gt,t)`.
- The epimorphism T → * is exactly `h_epi : Epi (toUnit T)`; `toUnit` targets the
  cartesian monoidal unit, the terminal set sheaf.
- One affine etale surjection U_i → X: the existential object `V : X.Etale` supplies
  the etale structure morphism, and `IsAffine V.left ∧ Surjective V.hom` gives
  exactly the other two conditions. The source's subscript i denotes the chosen
  stage, not an additional arbitrary family.
- G_0-torsor T_0: the existential sheaf `T₀` and map `a₀ : G₀.X ⊗ T₀ ⟶ T₀`
  have the same explicit unit and left associativity equations, pair-map
  `IsIso (lift a₀ (snd G₀.X T₀))`, and `Epi (toUnit T₀)`.
- T_0(U_i) nonempty: `Nonempty (T₀.obj.obj (op V))`.
- Isomorphism of G-torsors nu_X^* T_0 ≅ T: the existential
  `e : (torsorComparisonPullback X).obj T₀ ≅ T` is followed by its explicit
  equivariance equation. The left side first uses `Functor.LaxMonoidal.μ` to
  identify the product of inverse images with the inverse image of the product,
  then applies the actual inverse image of `a₀`, then `e.hom`. The right side
  applies identity × e, then a. Thus this is an isomorphism for the canonical
  pulled-back action, not merely an isomorphism of underlying sheaves.
- T is classical: the conjunct `IsClassical T` uses the dependency's exact
  continuity-map predicate on all affine presentations.
- T is trivialized by that etale covering: the final conjunct is
  `Nonempty (T.obj.obj (op ((Scheme.toProEt X).obj V)))`. Under `h_iso`, a section
  s induces the natural equivariant isomorphism g ↦ gs on the slice over V;
  its inverse is the first coordinate of the inverse pair-map at (t,s).
  Consequently nonempty sections on this cover express exactly triviality,
  not a weaker local-existence assertion. This argument also explains why no
  separate torsor predicate or arbitrary trivialization map is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  `ProEt.precoverage`, the exact Mathlib match for `sk-def-pe-site`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale` (the latter defined in `Morphisms.Etale`), and the covering criterion.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf` and sheaf morphisms.
- `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`: the currently recorded
  module is publicly imported, including its retained original-site comparison from
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`
  and `Scheme.preservesFiniteLimits_proEtaleSiteComparison`. The small-model record
  transports this same comparison; the original-site declarations remain usable and
  match the original-site `IsClassical` predicate without another transport.
- `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`: `ProEtale.IsClassical`,
  whose complete definition quantifies over `AffinePresentation` and uses
  `continuityMap`; these definitions and their docstrings were read.
- Mathlib `CategoryTheory.Grp`, `Functor.grpObjObj`,
  `Functor.Monoidal.ofChosenFiniteProducts`, cartesian `lift`, `snd`, and `toUnit`
  supply the internal structures and canonical maps. All universes and variables
  are bound explicitly; `autoImplicit` is false.

Every recorded project proof-dependency module is imported: `IndEtaleStability`,
`IndPrincipalZariski`, `ProEtaleComparisonSections`, `SetSheafCoverDescent`,
`ProEtaleSmallModelComparison`, and upstream `ProEtale.Comparison.Affine`.
There are no additional theorem declarations requiring new DAG nodes.

Edge cases checked before and after writing:

- The empty affine scheme remains allowed. V may be empty, its morphism is
  surjective, and a sheaf has a singleton of sections on the empty object.
  No point or nonempty scheme is assumed.
- The trivial group remains allowed. The pair-map torsor axiom together with
  the terminal epimorphism says T is the terminal sheaf, and the conclusion holds.
- No section of T on X is assumed; sections are required only on the existential
  cover V. An empty section set on X does not make the hypotheses inconsistent.
- General nonabelian groups are retained. The associativity equation and
  equivariance equation use the left action; the proof's gluing uses right
  multiplication in coordinates, which commutes with that action.
- The site objects have universe u+1 and morphisms universe u; values and the
  classicality predicate use the existing larger universe u+1. No equality of
  site universes, finiteness of the group, or restriction to finite coefficients
  is imposed.
- A single affine etale surjection is exactly the selected stage promised by
  the source. It yields a singleton etale covering; no stronger global section
  or finite-etale hypothesis is imposed.

Searches (all on 2026-10-17; launcher msearch logs also retained in searches.jsonl):

- `msearch.py ... leanfinder`: “Every torsor under the pullback of an etale sheaf
  of groups on the proetale site of an affine scheme descends to an etale torsor”.
  Eight hits for etale-site definitions/forgetful functors; no comparison theorem.
- `msearch.py ... leansearch`: “Torsors under pullback etale group sheaves on
  affine schemes descend from the proetale site”. Eight hits for sites and
  general morphism descent; no matching torsor comparison.
- `msearch.py ... loogle`: `GrpObj, MulAction, torsor` returned no hits (unknown
  unqualified `GrpObj`); the corrected query `CategoryTheory.Grp,
  CategoryTheory.Functor.mapGrp` returned the existing internal-group functor
  and related declarations, which are used instead of rebuilding group objects.
- `msearch.py ... grep`: `torsor|Torsor` in `CategoryTheory` returned no matches.
  Direct rg in Mathlib CategoryTheory also found no sheaf-torsor comparison.
- `rg -n 'torsor|Torsor'` in upstream `WeilConjectures` found the existing
  `CategoryTheory.Sheaf.Torsor` for abelian sheaves. Its full structure and
  docstring were read; it cannot represent the general group here.
- The prescribed upstream grep for `det-pe-torsor-comparison-affine` returned no match.
- `rg` in `lean/Sheaf` found `Sheaf.NonabelianTorsor` in
  `Sheaf.CategoryTheory.Sites.ConstructibleTorsor`, which was read in full.
  It is specialized to the etale site and provides no comparison or proetale
  torsor interface. We introduce no competing torsor definition; the statement
  spells out the source's own action, isomorphism and epimorphism conditions.
- Name searches for `torsorComparison`, `torsor_comparison_affine`, and
  `proEtaleTorsorComparison` in Mathlib, upstream, `lean/Sheaf` and the upstream
  name index found no declaration collision. The DAG definition-title search
  found only abelian, etale, finite, or represented torsor specializations.

Validation: `scompile.py Q29 det-pe-torsor-comparison-affine <module>` passed
both sandbox and module-path compilation with no errors or warnings. The only
postponed proof is the named theorem with the complete proof docstring.
No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q29

I read the node statement, its source proof, the complete Lean module, and the
recorded declarations of every statement dependency. The source is the affine
case of Stacks Tag 099X (`lemma-compare-cohomology-nonabelian`) and the blueprint
node `sk-lem-pe-torsor-comparison-affine.md`. The node introduces the following
objects and clauses, matched against Lean as follows.

- The affine scheme (X) is `(X : Scheme.{u}) [IsAffine X]`; no
  separatedness, Noetherianity, connectedness, or coefficient hypothesis is
  added.
- The possibly noncommutative sheaf of groups (G_0) is
  `G₀ : Grp (Sheaf X.smallEtaleTopology (Type (u + 1)))`. This is Mathlib's
  internal group object in the cartesian category of set sheaves, so it is the
  same sheaf-of-groups notion used by the node.
- The definition (G=\nu_X^*G_0) is rendered by
  `torsorComparisonPullback X`, an abbreviation for the recorded canonical
  `Functor.sheafPullbackConstruction.sheafPullback` along `Scheme.toProEt X`.
  `torsorComparisonPullback_monoidal` supplies the canonical product
  comparisons from `preservesFiniteLimits_proEtaleSiteComparison`; it introduces
  no arbitrary map or replacement group.
- The pro-étale sheaf of sets (T) is
  `T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))`.
- The left action is the sheaf morphism
  `a : (torsorComparisonPullback X).obj G₀.X ⊗ T ⟶ T`. `h_one` is the unit law
  and `h_mul` is the associative left-action law, with the displayed
  associator. These are exactly the source's action hypotheses.
- `h_iso : IsIso (lift a (snd ...))` is the isomorphism
  ((g,t)\mapsto(gt,t)), and `h_epi : Epi (toUnit T)` is the epimorphism
  (T\to *), since `toUnit T` is the terminal set-sheaf map.
- The first conclusion object is `V : X.Etale`; `IsAffine V.left` and
  `Surjective V.hom` give precisely an affine étale surjection (V\to X).
- The next existential gives
  `T₀ : Sheaf X.smallEtaleTopology (Type (u + 1))` and
  `a₀ : G₀.X ⊗ T₀ ⟶ T₀`, followed by the unit law, associative action law,
  pair-map isomorphism, and terminal epimorphism. Together these are exactly a
  (G_0)-torsor, with no commutativity or extra condition.
- `Nonempty (T₀.obj.obj (op V))` is (T_0(V)\ne\emptyset), and the final
  `Nonempty (T.obj.obj (op ((Scheme.toProEt X).obj V)))` is the asserted section
  of (T) on the same étale cover.
- The existential `e : (torsorComparisonPullback X).obj T₀ ≅ T` is accompanied by
  the displayed equality using `Functor.LaxMonoidal.μ`, `map a₀`, and the
  whiskered `e.hom`. This is the equivariance equation, so it is an isomorphism
  of the two torsors rather than merely an isomorphism of underlying sheaves.
- `IsClassical T` is exactly the recorded continuity-map predicate from
  `det-pe-classical-definition-continuity-map`; it is the node's “in
  particular” clause.

No mismatch was found and no Lean or node field was changed. In particular, the
Lean statement has the same quantifier order and does not add a family of covers,
nonemptiness of (X), finiteness of (G_0), a characteristic assumption, or a
universe equality. The helper declarations are listed in the node's `lean`
record and have source and blueprint docstrings; they are canonical aliases and
do not duplicate a torsor notion.

The edge cases were checked explicitly: the empty affine scheme and empty cover,
the trivial group, (n=0) (there is no hidden finite-index parameter), empty or
zero section sets on (X), and arbitrary noncommutative groups. The chosen cover
may itself be empty where the hypotheses permit it, and no global section of (T)
is required. Site objects and section values use the existing (u+1) convention;
no independent smaller universe is introduced.

For the one-definition check I searched Mathlib and `WeilConjectures/` with the
prescribed LeanFinder, LeanSearch, Loogle, and `rg` queries for torsors,
`torsor_comparison_affine`, `torsorComparisonPullback`, and comparison maps. The
only related declarations were the generic `CategoryTheory.Sheaf.Torsor` and the
specialized `Sheaf.NonabelianTorsor`; neither states this pro-étale/étale affine
comparison. The canonical comparison inverse image and finite-limit theorem are
the recorded dependency declarations and are used directly. Compilation with
`scompile.py` succeeded for both sandbox and library paths with no errors or
warnings beyond the intended theorem `sorry`.
