## Worker report

The module `Sheaf.CategoryTheory.CartesianSectionCoveringRestriction` states
`CategoryTheory.Pseudofunctor.bijective_sieveSectionRestriction_mapIso`, with `sorry`.
Its helper `CategoryTheory.Pseudofunctor.sieveSectionRestriction` is the actual canonical
restriction functor, with real object and morphism data and no postponed laws. It only
reindexes Mathlib's existing descent data. No separate mathematical result is proved.
There are no new nodes, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/stacks.tex`, Tag 02ZN, `lemma-stackify`,
naive proof's final checks (4) and (8), and the less naive proof's definition of
morphisms on common refinements (lines 1480–1730 in the read checkout). The item's
four proof steps are expanded in the theorem docstring: conjugate the local
components into a matching family, glue in each isomorphism sheaf, check section
compatibility by local uniqueness, and prove surjectivity and injectivity. No
object-descent assumption is used or added.

Hypothesis and conclusion correspondence:

- The fixed larger universe is `universe w`; the site is `{C : Type w}
  [SmallCategory C] (J : GrothendieckTopology C)`. Thus both its objects and arrows
  lie in that universe, without any nonemptiness or existence-of-pullbacks condition.
- A fibred groupoid with coherent choices of pullback is represented by
  `(Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})` and
  `(hQ : ∀ V : C, IsGroupoid (Q.obj (.mk (op V))))`. This is the same non-strict
  pseudofunctor encoding used in the existing
  `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription` module. Choosing
  cartesian lifts supplies this presentation of any fibred groupoid; it does not
  require strictly compositional pullbacks. The fibre object and arrow sizes are w.
- The prestack hypothesis is `[Q.IsPrestack J]`. Its full source signature in
  `Mathlib.CategoryTheory.Sites.Descent.IsPrestack` says that, for every V and
  a,b in the fibre, `Q.presheafHom a b` is a sheaf on `J.over V`. Its value at
  h is `h^*a ⟶ h^*b`; all these morphisms are invertible by `hQ`, so this is
  precisely the node's isomorphism-sheaf hypothesis. `J.over V` is the induced
  topology specified in the node, with coverings detected by underlying sieves.
- The base and sieves are `{T : C} (S K : Sieve T)`. The inclusion is
  `(hKS : K ≤ S)`. Neither `S ∈ J T` nor `K ∈ J T` is assumed.
- The local coverage hypothesis is exactly
  `(hcover : ∀ (V : C) (f : V ⟶ T), S f → K.pullback f ∈ J V)`.
  Mathlib composition is left-to-right, so `K.pullback f` consists of h with
  `h ≫ f ∈ K`, the node's f^*K.
- Cartesian sections x and y are
  `(x y : Q.DescentData (fun f : S.arrows.category ↦ f.obj.hom))`.
  `S.arrows.category` is Mathlib's full subcategory of `Over T` on arrows in S.
  This is the existing Mathlib transport presentation of exactly these sections,
  not an arbitrary family without coherences: `obj f` is x_f; `hom` compares
  h₁^*x_f₁ and h₂^*x_f₂ for any equality h₁f₁ = h₂f₂; `hom_self`, `hom_comp`
  and `pullHom_hom` impose identity, cocycle and pullback coherence.
- More explicitly, given the node's section comparisons c, the descent comparison
  at q = h₁f₁ = h₂f₂ is c_(f₁,h₁) followed by the inverse of c_(f₂,h₂).
  Here q is again in S by the sieve property. Conversely, for h:W→dom(f), take
  the descent comparison with first index f and leg h, second index fh and
  identity leg, followed by the pseudofunctor identity-pullback comparison, to
  obtain h^*x_f ≅ x_fh. The descent self/cocycle/pullback laws give the section
  identity/composition laws; the section coherence laws give the descent laws.
  These constructions undo each other using those laws and the unit comparison.
  In particular no extra descent effectivity or covering of T is hidden here.
- Descent-data arrows are fibre maps `φ.hom f` commuting with all the comparisons
  (`Hom.comm`); these correspond to the node's compatible families. Under hQ
  they are all invertible: take fibrewise inverses in the commutative squares.
  Thus isomorphisms in this presentation are exactly the displayed isomorphisms
  of the section groupoid, without quotienting by isomorphism classes.
- `sieveSectionRestriction Q hKS` sends f in K to precisely the same arrow f
  viewed in S. Its object, comparison and arrow fields are the original fields
  at these indices, including for non-strict Q. In particular it is actual
  restriction, not pullback along an identity with additional chosen data.
- The conclusion `Function.Bijective ((sieveSectionRestriction Q hKS).mapIso :
  (x ≅ y) → (...obj x ≅ ...obj y))` is exactly bijectivity of the canonical map
  on isomorphisms asserted in the node. In the section groupoids this is
  equivalently full faithfulness, so no additional conjunct is required.

Recorded dependencies read and used:

- `def-weil-size-convention`: its convention-only Lean record requires explicit
  universe binders and no module or declaration. All sizes are explicitly w.
- `def-weil-pbc-topos`: public import
  `Sheaf.CategoryTheory.Sites.GrothendieckTopos`; read the whole definition and
  docstring of `CategoryTheory.IsGrothendieckTopos`. The module explicitly reuses
  Mathlib's `Sieve`, `GrothendieckTopology`, `Presheaf.IsSheaf` and `Sheaf` for
  the site's definitions. This lemma uses these site notions, not a further
  hypothesis that some unspecified category is a topos. Its proof dependency
  is this same node and is already publicly imported.
- The existing Mathlib APIs read in full were `Pseudofunctor.DescentData`, its
  `Hom`, category instance, `iso`, `isoMk`, and `pullFunctor` in
  `Mathlib.CategoryTheory.Sites.Descent.DescentData`, plus `presheafHom` and
  `IsPrestack` in `Mathlib.CategoryTheory.Sites.Descent.IsPrestack`. The
  declaration `Presieve.category` in `Sites.Sieves` explicitly defines the full
  subcategory of the slice on the specified arrows. `IsGroupoid` is Mathlib's
  property of a category, imported from `Mathlib.CategoryTheory.Groupoid`.

Edge cases checked before writing:

- S empty: K must be empty and the section groupoids have their empty-family
  section and unique arrow. The theorem still quantifies over those sections.
- K empty, S nonempty: hcover requires the empty sieve to cover every domain
  appearing in S; the prestack sheaf condition then gives exactly the required
  uniqueness of fibre arrows. This case is retained without assuming nonempty
  covers or points.
- K = S: restriction is the direct identity reindexing, and mapIso is bijective.
- S noncovering: no cover-of-T binder appears anywhere in the definitions or
  theorem; only hcover over the individual arrows occurs.
- Empty base category, fibres without objects, and disconnected fibres: there
  is no extra nonemptiness, connectedness or chosen base object hypothesis.
- No pullbacks in C, and genuinely non-strict pseudofunctor comparisons: Mathlib's
  transport-style data quantify over common-source diagrams and include the
  comparison isomorphisms, so these cases are retained.

Searches actually run for this item:

- `msearch.py ... leanfinder` with query "For a prestack restriction of cartesian
  sections from a sieve to a locally covering subsieve is fully faithful" returned
  eight hits including `fullyFaithfulToDescentData` and `IsPrestackFor.fullyFaithful`.
- `msearch.py ... loogle` with query `"IsPrestack", "fullyFaithful"` returned
  `IsPrestackFor.fullyFaithful` and its nonempty field.
- `msearch.py ... leansearch` with query "Restriction of descent data along an
  inclusion of sieves locally covering the larger sieve is fully faithful for
  a prestack" returned eight hits, chiefly the same descent-to-family results.
- `msearch.py ... grep 'fullyFaithful|restrict.*[Ss]ieve'
  CategoryTheory/Sites/Descent` returned eleven hits, including
  `DescentData.fullyFaithfulPullFunctor`. I read its full signature and docstring
  in `Precoverage.lean` lines 316–327: it assumes the smaller family covers T.
  It therefore does not state the node, which only assumes local coverage over S.
- `msearch.py ... grep 'cartesianSection|sieveSectionRestriction|cartesian_section|section.*[Ss]ieve'
  CategoryTheory` returned nine unrelated sieve-of-section/intersection results.
- `rg` searches for `cartesian.section|CartesianSection|IsPrestack|FibredInGroupoids|IsFiberedInGroupoids`
  across Mathlib CategoryTheory and the project's CategoryTheory directories
  found the descent APIs and existing stackification statements, no such lemma.
- `rg` searches for `cartesian.?section|sieveSectionRestriction|section.*sieve|sieve.*section`
  in `lean/WeilConjectures/CategoryTheory` found unrelated abelian-sheaf statements;
  the stackification module in `lean/Sheaf` uses cartesian sections in its proof
  description but does not define or state this restriction theorem.
- Searches of `dag/lean_names_upstream.json`, `lean/Sheaf` and
  `lean/WeilConjectures` for the two proposed declaration names had no hits.
  The item-id search in `lean/WeilConjectures` also had no hits.
- DAG searches for cartesian sections and prestacks located the item and its
  consumer `lem-sfb-prestack-sieve-descent-completion`; neither supplies an
  existing usable declaration of this restriction map or lemma.

The general descent-data notion is reused, and only its canonical restriction
map is supplied as an owning-node helper, as authorized in the brief. No
STATEMENT-DISPUTED issue was found. Every binder and universe is explicit;
`set_option autoImplicit false` enforces this. The prescribed `scompile.py`
compiled the module on the server in both sandbox and library contexts with
no errors or warnings (only the expected postponed theorem).

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
