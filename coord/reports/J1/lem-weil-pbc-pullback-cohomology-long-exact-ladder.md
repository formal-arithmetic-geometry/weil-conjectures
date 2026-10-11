## Worker report

The module `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder` states
`AlgebraicGeometry.Etale.pullbackCohomology_longExact_ladder`. Its only proof is `sorry`.
No notions are redefined and no node statement is changed.

Hypotheses and clauses, individually:

- Schemes X and Y: `{X Y : Scheme.{u}}`; arbitrary scheme morphism u:Y→X:
  `(f : Y ⟶ X)`. No properness, etaleness, finiteness, coefficient torsion, or
  geometric-point hypothesis is imposed.
- The abelian sheaves G₁,G,G₂ and maps α,β are `S.X₁,S.X₂,S.X₃,S.f,S.g` for
  `S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1})`.
  `hS : S.ShortExact` gives precisely injectivity, exactness, and surjectivity.
- Clause 1 is `∃ hY : (S.map ((f)^*[AddCommGrpCat.{u+1}])).ShortExact`.
  The object and arrow maps of this short complex are those of the recorded
  inverse-image functor `AlgebraicGeometry.Etale.upperStar`.
- Clause 2's connecting homomorphisms are the dependent families `δX` and `δY` of
  additive homomorphisms in all degrees `q : ℕ`. The first two conjuncts pin down
  their values as `x.comp hS.extClass rfl` and `x.comp hY.extClass rfl`.
  These are the canonical boundaries, not arbitrary maps giving an exact sequence.
  In `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass`, the full signature
  `ShortExact.extClass_hom : hS.extClass.hom = hS.singleδ` identifies their
  underlying derived morphism with exactly the mapping-cone morphism named by
  the node. `Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`
  in `Ext.ExactSequences` identifies postcomposition with the boundary of that
  distinguished triangle, including the shift convention. Thus, under the
  existing identification of Ext sheaf cohomology with derived global sections,
  these are H^q of σ∘RΓ(w), with w=singleδ, as prescribed in the statement.
- The initial `0→H⁰(G₁)` and its Y counterpart are the two explicit
  `Function.Injective` conjuncts at degree zero.
- Exactness at G, G₂, and the next G₁ is given by the three `Function.Exact`
  conjuncts quantified over every q on X, and the three on Y. Together with
  the degree-zero injection these express the entire displayed long exact
  sequences, including every degree, with no terminal surjectivity added.
- Clause 3 is the final three universally quantified equalities, using the
  recorded `cohomologyMap` and `Sheaf.H.map`. The first square is for α, the
  second for β, and the last sends H^q(X,G₂) to H^(q+1)(Y,f⁻¹G₁).
  Equalities on every element give equality of the additive homomorphisms.

Representation and dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`; the small etale
  topology is `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `upperStarLowerStarAdjunction` (the recorded
  inverse image; the module imports this transitively).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `AlgebraicGeometry.Etale.cohomologyMap`, and `cohomologyMap_map` for the recorded
  functorial sheaf map. Its full signatures and docstrings were read.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `CategoryTheory.Sheaf.H`, `Sheaf.H.map`, both used in the signature.
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`:
  `ShortComplex.ShortExact.singleδ`, `singleTriangle_distinguished`, the
  dependency's Mathlib match; the ExtClass import supplies them.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass`:
  `ShortComplex.ShortExact.extClass`, `extClass_hom`, fixing the boundary.
- The recorded derived-cohomology source
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` was read:
  `Etale.rightDerivedGlobalSections` is R(Sheaf.Γ), and `Etale.cohomology` is
  its composition with `DerivedCategory.homologyFunctor`. The existing node's
  note explicitly permits the `Sheaf.H` encoding for abelian sheaves and leaves
  the identification with this derived functor to stage 3. The pullback node's
  note similarly specifies `cohomologyMap`, leaving the resolution-recipe
  comparison to stage 3. This delivery follows those existing encodings rather
  than writing another cohomology or pullback definition.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory` (underlying the canonical extension class).
- `Sheaf.AlgebraicGeometry.DerivedCategories`: recorded derived categories and
  `torsionCohomology` were read; no torsion or bounded-derived object is needed
  in the signature, which starts with sheaves in degree zero.
- The recorded shift and triangulated instances in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
  were read. They justify the RΓ interpretation of the boundary; no duplicate
  triangulated structure is introduced or unused import added.

Dependency record (updated at second reading):
`lem-weil-pbc-cohomology-pullback-functorial` now records
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`, declaration
`AlgebraicGeometry.Etale.cohomologyPullbackFunctorial`. The second reader opened
that module: it states sheaf naturality, composition, and identity in the existing
Ext encoding. The sheaf-induced maps needed to state this item are already
`Sheaf.H.map`, with naturality `cohomologyMap_map`. The comparison-complex and D+
clauses of the dependency are not additional hypotheses or conclusions of this
item, and the delivery does not replace that dependency by its naturality clause.

Edge cases checked before writing: degree q=0 retains both initial injections
and both δ⁰ squares; zero sheaves and split short exact sequences give zero
extension classes and the expected zero boundaries; identity morphisms give an
identity ladder after the usual inverse-image identification; the empty scheme
is allowed, with zero cohomology; arbitrary (possibly non-etale) morphisms are
allowed; there is no torsion restriction. The coefficient universe u+1 is the
recorded universe of abelian sheaves on the small etale site of Scheme.{u}.
No counterexample or STATEMENT-DISPUTED issue was found.

Searches performed:

1. `msearch.py ... leanfinder "pullback maps on etale sheaf cohomology form a
   morphism of long exact sequences of a short exact sequence"`: eight hits,
   concerning Mayer–Vietoris and snake inputs; no complete ladder statement.
2. `msearch.py ... loogle "CategoryTheory.ShortComplex.ShortExact.extClass,
   CategoryTheory.Ext.postcomp"`: zero hits; the service reports the latter
   identifier unknown (the pinned source puts Ext under CategoryTheory.Abelian).
3. `msearch.py ... grep "longSequence|comp_extClass|singleδ" CategoryTheory/Sites`:
   no hits in pinned Mathlib's Sites directory.
4. `rg` on Mathlib's `DerivedCategory/Ext` found `extClass_hom`, the three Ext
   exactness lemmas, and the canonical triangle-boundary identification.
5. `rg` of the source project for long exact sequences and `comp_extClass`
   found `Etale.cohomologyMap_comp_extClass` in `SixFunctors/Etale/Gabber.lean`.
   This proves the final square only, not the bundled statement including both
   complete exact sequences. Its full signature was read.
6. `rg` of `lean/Sheaf` for the same notions found citers, including
   `Curve/DenseOpenAssertions` and `PullbackIsoPrimeTorsionDevissage`, but no
   declaration of this ladder. The required upstream grep for the item id
   returned no hits. The chosen declaration name is new in the searched sources.

The local literature checkout lacks the Stacks sources. The source places were
read at [01FT](https://stacks.math.columbia.edu/tag/01FT),
[04I0](https://stacks.math.columbia.edu/tag/04I0), and
[0A5C](https://stacks.math.columbia.edu/tag/0A5C).

Validation: server single-file compilation completed cleanly in 2.2 seconds.
The dry run result is recorded after running `deliver2.py --no-push`.

`deliver2.py J1 lem-weil-pbc-pullback-cohomology-long-exact-ladder --no-push`
printed OK: the module compiles and preflight passes except for the second
reading, which the independent second reader writes. Nothing was pushed.

## Second reading by J1

Independent reading against the unchanged node, all ten statement-dependency
records, and their source declarations. No statement correction, new definition
node, or dependency module is needed. The Lean signature is unchanged.

The source checkout has no Stacks text. I downloaded the Stacks upstream
`sites-cohomology.tex`, `homology.tex`, and `etale-cohomology.tex` to this item's
scratchpad and read the sections identified by the node's labels, including the
surrounding hypotheses. These agree with [01FT](https://stacks.math.columbia.edu/tag/01FT),
[010S](https://stacks.math.columbia.edu/tag/010S),
[04I0](https://stacks.math.columbia.edu/tag/04I0), and
[0A5C](https://stacks.math.columbia.edu/tag/0A5C).
01FT assumes a site and an abelian sheaf; 010S assumes abelian categories and
universal delta-functors; 04I0 starts with an arbitrary scheme morphism. The
field, dimension, finiteness, separation, and torsion assumptions of 0A5C belong
to the curve application, not the general cohomology ladder cited in its proof.

Object/hypothesis/conclusion list and matching Lean (H3):

1. Objects X,Y are arbitrary schemes: `{X Y : Scheme.{u}}`. The morphism
   u:Y→X is `(f : Y ⟶ X)`. I read `Scheme` and `Scheme.Hom`; their locally
   ringed-space objects and arrows are the recorded definitions. PASS: no
   Noetherian, finite type, separation, properness, or etaleness hypothesis.
2. Objects G₁,G,G₂ and maps α,β are `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g`
   for `S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   The short complex includes β∘α=0 and `hS : S.ShortExact` adds exactness,
   mono α and epi β. PASS: precisely a short exact sequence of abelian sheaves.
   `Sheaf` and `smallEtaleTopology` are the dependency's existing site encoding.
3. Clause 1, the same sequence pulled back to Y is short exact:
   `∃ hY : (S.map ((f)^*[AddCommGrpCat.{u + 1}])).ShortExact`.
   I opened `Etale.upperStar` and `upperStarLowerStarAdjunction`: the functor is
   sheafified presheaf inverse image, left adjoint to direct image. PASS: the
   functor maps the same objects and arrows, not arbitrary sheaves on Y.
4. Clause 2, all connecting additive maps, with degrees q≥0:
   `δX : ∀ q : ℕ, Sheaf.H S.X₃ q →+ Sheaf.H S.X₁ (q + 1)` and the displayed
   `δY` family for the pulled-back objects. PASS: quantifiers follow hY and
   cover all nonnegative degrees, as the node requires.
5. Clause 2, the prescribed canonical boundary, not merely some exact maps:
   the first two conjuncts say `δX q x = x.comp hS.extClass rfl` and
   `δY q x = x.comp hY.extClass rfl`. I read `singleδ`, `singleTriangle`,
   `singleTriangle_distinguished`, `extClass`, `extClass_hom`, and
   `Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`.
   PASS in the recorded Ext cohomology encoding: `extClass_hom` identifies
   exactly the node's cone-constructed `singleδ`, and the latter lemma identifies
   composition with the triangle's connecting map, including its shift sign.
   The records of `def-weil-pbc-etale-cohomology` and
   `def-weil-pbc-cohomology-pullback` explicitly permit `Sheaf.H` and
   `cohomologyMap`, leaving the resolution comparisons to stage 3. I also read
   `Etale.rightDerivedGlobalSections`, `Etale.cohomology`, and the recorded
   right-derived-plus shift/triangulated instances. This delivery introduces no
   new cohomology or alternative choice of boundary.
6. Clause 2, initial zero and exactness at H⁰(G₁), for X and Y:
   the two `Function.Injective (... 0)` conjuncts. PASS: both injections are
   present, without an unjustified surjectivity at the other end.
7. Clause 2, exactness of the whole X sequence:
   for every q the three `Function.Exact` conjuncts cover H^q(G), H^q(G₂),
   and H^(q+1)(G₁). PASS: together with item 6 they cover every term.
8. Clause 2, exactness of the whole Y sequence:
   the next three `Function.Exact` conjuncts use the inverse-image maps of
   S.f and S.g and δY. PASS: all degrees and all terms again included.
9. Clause 3, α square: the first final equality on every
   `x : Sheaf.H S.X₁ q` uses `cohomologyMap f S.X₂ q`, `Sheaf.H.map S.f q`,
   and the pullback of S.f. PASS: the correct vertical maps and sheaf arrow.
10. Clause 3, β square: the next equality on every
    `x : Sheaf.H S.X₂ q` uses `cohomologyMap f S.X₃ q` and S.g. PASS.
11. Clause 3, boundary square: the last equality is
    `cohomologyMap f S.X₁ (q + 1) (δX q x) =
      δY q (cohomologyMap f S.X₃ q x)` for every q and every x in H^q(G₂).
    PASS: the left vertical map has degree q+1; equality on all elements is
    equality of the additive maps. I opened upstream
    `cohomologyMap_comp_extClass`, which states exactly this square, but not
    clauses 1 and 2 or the complete ladder and hence does not replace the item.

Edge cases: q=0 retains both initial injections and all three squares, with
δ⁰ landing in degree 1. Zero sheaves and split sequences are allowed; their
extension classes vanish. Empty schemes are allowed, with no nonemptiness
binder. There is no index set or characteristic parameter to restrict. Both
schemes can lie in any universe u (different original sizes can be placed in a
common universe); AddCommGrpCat.{u+1} is the recorded coefficient universe for
the small etale site, not a new finiteness or field assumption. There are no
unbound variables or universes and no additional instance binders.

Independent H4 searches, using different phrasing from the first reader:

- LeanFinder: "inverse image induces naturality of the coboundary maps in étale
  cohomology for an exact triple"; eight hits, for cotangent or group-cohomology
  boundaries, none for this scheme/sheaf ladder.
- Loogle: `CategoryTheory.ShortComplex.ShortExact.extClass`; twelve hits,
  including extClass_hom, extClass_naturality and general Ext exactness tools.
  I opened the relevant pinned source declarations; none bundles this ladder.
- LeanSearch: "A morphism of schemes induces a commutative diagram between the
  long exact cohomology sequences of an exact triple of abelian sheaves";
  service returned Internal Server Error. Recorded as unavailable, no verdict
  inferred; successful LeanFinder, Loogle and source grep provide the searches.
- `msearch.py ... grep 'homologySequenceδ_singleTriangle|covariant_sequence_exact'
  Algebra/Homology/DerivedCategory/Ext` found ten generic Ext tools, including
  the exact boundary-identification lemma read above.
- Direct rg for `cohomologyMap_comp_extClass`, cohomology ladders,
  `δ_naturality`, and connecting maps in upstream etale modules, project
  `lean/Sheaf/AlgebraicGeometry`, and pinned SheafCohomology found the Gabber
  boundary square, generic base-change ladders, and citers. No complete duplicate.
  The base-change ladders concern higher direct images and a cartesian square,
  not these global-cohomology groups for an arbitrary morphism.
- The item's id and declaration name do not occur in upstream WeilConjectures
  or `dag/lean_names_upstream.json`. All definitions used are existing notions.

Mismatch found and changed: the worker report's claim that
`lem-weil-pbc-cohomology-pullback-functorial` lacks a record was stale. I replaced
that paragraph after opening its now-recorded module. Its sheaf naturality,
composition and identity statement provides the part relevant here; it does
not itself state the comparison-complex and derived clauses of that node.
Those clauses are not needed to type this sheaf-only ladder: `Sheaf.H.map` and
`cohomologyMap` already supply its notions, so no weaker dependency replacement
or private definition is introduced. No mismatch in this item's signature was
found. No new nodes or dependency modules were delivered, so H12/H13 add no
extra review items. No statement_change exists, so citer correction verdicts
are not applicable.

H5/H6/H8/H9: no definitions or auxiliary statements were added; the sole theorem
ends in `by sorry`. Its source/docstring blueprint id and all eleven proof steps
are present. Both imports supply identifiers used by the signature. No private
or file-local notation/instances; the upper-star notation is the dependency's
exported scoped notation. All lines are at most 100 characters. The namespace
has no Sheaf prefix. The node's lean.statement equals the module signature
verbatim after the delivery tool's whitespace normalization.

Validation: independent `scompile.py` server single-file compile exited 0 in
2.2 seconds, with no warnings or errors. Dry run and delivery results follow
from the requested `deliver2.py` checks.
