## Worker report

The module Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection states
AlgebraicGeometry.Scheme.geometricPointMorphism_stalk_bijection, with `sorry` as its only
proof. It introduces no definitions or additional nodes and makes no statement correction.

Source checked: https://stacks.math.columbia.edu/tag/04FN, Remark 59.29.8. The local
literature/stacks-project/etale-cohomology.tex is absent on this machine, so the Stacks page
was opened directly. It gives the pointed-neighbourhood functor, representative rule, and
isomorphism of stalk functors. The abelian clause follows by the additive colimit argument
in the node. All five proof steps are recorded in the theorem docstring.

Hypotheses and clauses:
- `S : Scheme.{u}` is the scheme. `k k' : Type u`, the two `Field` and `IsAlgClosed`
  instances, and `s : Spec (.of k) ⟶ S`, `s' : Spec (.of k') ⟶ S` render both geometric
  points, without replacing algebraically closed by separably closed in the hypotheses.
- `a : Spec (.of k) ⟶ Spec (.of k')` is an arbitrary scheme morphism. `ha : a ≫ s' = s`
  is the triangle in the node; there is no assumption that `a` is an isomorphism.
- The local `b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha` is exactly this morphism
  over S. `α := Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)` acts on a lift
  `t` by precomposition with b, hence its underlying scheme map is `a ≫ t.left`.
  Its codomain is the fibre at s, so this also records that the new lift is a pointed
  neighbourhood of s. This uses existing Over and coyoneda constructions, not a new notion.
- `CategoryOfElements.map α` fixes the underlying étale object and underlying morphism
  and changes the lift by precomposition. Its `IsEquivalence` is the parenthetical clause.
- `∀ F : Sheaf S.smallEtaleTopology (Type (max u v))` covers set-valued étale sheaves.
  Stalks are `(pointSmallEtale s').sheafFiber.obj F` and the analogous expression at s.
  The local predicate P says, for every étale U, every lift t, and every section σ,
  that f carries `toPresheafFiber U t F.obj σ` to
  `toPresheafFiber U (α.app U t) F.obj σ`. These are precisely the two classes in the node.
  `(∃! f, P f)` says exactly one map has this rule, and `∀ f, P f → Function.Bijective f`
  asserts that map is bijective. Uniqueness is not restricted to bijective candidates.
- The final universal quantifier uses `Sheaf S.smallEtaleTopology AddCommGrpCat`.
  Its P is equality of the additive coprojection followed by f with the coprojection
  at the transported lift, equivalently the same representative rule for every section.
  `(∃! f, P f)` gives the unique additive map and `∀ f, P f → IsIso f` the abelian-group
  isomorphism. It agrees with the set-level map on all representatives and hence on the
  underlying stalk sets by the filtered-colimit description.

Dependency declarations read and used:
- def-pc-scheme: AlgebraicGeometry.Scheme and Scheme.Hom,
  Mathlib.AlgebraicGeometry.Scheme (locally affine locally ringed spaces and their maps).
- def-weil-geometric-point: Scheme.SpecToEquivOfField,
  Mathlib.AlgebraicGeometry.ResidueField, and IsAlgClosed,
  Mathlib.FieldTheory.IsAlgClosed.Basic. The record explicitly calls for the inline
  specialization `[Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)`; the equivalence of
  such morphisms with residue-field embeddings is not needed to elaborate the statement.
- def-weil-pbc-etale-site: Scheme.smallEtaleTopology, Mathlib.AlgebraicGeometry.Sites.Etale,
  and Scheme.Etale / Etale.forget, Mathlib.AlgebraicGeometry.Morphisms.Etale.
- def-weil-pbc-etale-sheaves: its mixed lean record explicitly includes CategoryTheory.Sheaf
  as the existing sheaf category. We use that declaration from Mathlib.CategoryTheory.Sites.Sheaf;
  its locally constant/constructible predicates in Sheaf.AlgebraicGeometry.EtaleSheaves are
  not part of this node's statement and therefore are not imported.
- def-weil-pbc-geometric-stalks: GrothendieckTopology.Point.sheafFiber,
  Mathlib.CategoryTheory.Sites.Point.Basic, together with Scheme.pointSmallEtale,
  Mathlib.AlgebraicGeometry.Sites.EtalePoint. `toPresheafFiber` from Point.Basic is the
  recorded colimit coprojection; sheafFiber is the restriction of presheafFiber to sheaves.
- def-weil-pbc-abelian-etale-sheaves: CategoryTheory.Sheaf,
  Mathlib.CategoryTheory.Sites.Sheaf, specialized to AddCommGrpCat.
- The category in the final parenthetical is the category of elements of the recorded
  stalk fibre, using CategoryOfElements.map from Mathlib.CategoryTheory.Elements.
  No separate neighbourhood definition is introduced.

Edge cases checked: an empty scheme cannot have either geometric point, so no extra
nonemptiness hypothesis is appropriate. Empty étale objects have no lifts and contribute
no representatives. The empty set sheaf and the zero abelian sheaf have the corresponding
empty and zero stalks; uniqueness and bijectivity/isomorphism remain meaningful. Identity
morphisms and algebraically closed field inclusions of positive transcendence degree are
both included: requiring IsIso a would wrongly discard the latter. No characteristic,
Noetherian, or finiteness assumptions occur. All universes and binders are explicit.
Scheme and fields have the standard shared universe u (any sizes can be placed in a common
universe); the independent value-size v enters `max u v`, allowing arbitrarily large
coefficient sets and groups without demanding colimits smaller than the indexing site.

Searches performed (msearch entries are in searches.jsonl):
- LeanSearch: "morphism of geometric points induces bijection of etale stalks" returned
  Internal Server Error; recorded unavailable, with no mathematical verdict.
- LeanFinder: "morphism of geometric points induces isomorphism of etale stalk functors"
  returned eight Zariski-stalk comparison statements, not this étale assertion.
- Loogle: "AlgebraicGeometry.Scheme.pointSmallEtale" returned seven declarations including
  the fibre and conservativity results, but no morphism-induced stalk bijection.
- Mathlib grep: "pointSmallEtale|sheafFiber" in AlgebraicGeometry/Sites found EtalePoint's
  existing fibre constructions, not this statement.
- rg in WeilConjectures for pointSmallEtale and comparisons found
  WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint.pointSmallEtaleCongr.
  Its full source was read: it takes `e : Spec Ω' ≅ Spec Ω`, so covers only isomorphisms,
  unlike the present arbitrary morphism. The source declaration cannot be reused as the item.
- rg for this item id in WeilConjectures found no attachment.
- rg in lean/Sheaf found EtaleSheaves, GeometricStalkColimits and related stalk usages,
  but no arbitrary-morphism comparison. rg in dag/lean_names_upstream.json and lean/Sheaf
  for the proposed declaration found no name collision.

No STATEMENT-DISPUTED or node fault was found. Server compilation is clean; the final
preflight dry run is performed after writing this report. The independent second reading
is reserved for the second worker, as required by the dispatcher workflow.

## Second reading by C1

I independently opened the item node, the delivered Lean, all six statement-dependency
nodes and their recorded declarations. The local Stacks checkout lacks the .tex file;
I downloaded the official stacks/stacks-project master etale-cohomology.tex into the
sandbox scratchpad and read remark-map-stalks (04FN), plus the start of section-stalks
and definition-geometric-point. I also opened https://stacks.math.columbia.edu/tag/04FN.
The source assumes only a scheme and two geometric points (algebraically closed fields),
with the indicated commuting triangle. There is no standing Noetherian, finiteness,
characteristic, or isomorphism hypothesis. The source's representative rule and equivalence
are exactly those of this node; its abelian clause is the same colimit construction in Ab.

Object/hypothesis/conclusion inventory, with its Lean rendering and verdict:

1. Scheme S: `{S : Scheme.{u}}`. Mathlib's Scheme extends LocallyRingedSpace with local
   affine charts (Scheme.lean:42); its Hom is the scheme morphism. Exact.
2. Algebraically closed fields k and k': `{k k' : Type u}`, `[Field k] [IsAlgClosed k]`
   and `[Field k'] [IsAlgClosed k']`. IsAlgClosed is the usual polynomial splitting
   predicate (IsAlgClosed/Basic.lean:62). Exact; these assumptions imply the separably
   closed instances needed by pointSmallEtale, rather than assuming them additionally.
3. Geometric points: `(s : Spec (.of k) ⟶ S)` and `(s' : Spec (.of k') ⟶ S)`.
   Read def-weil-geometric-point's inline specialization and SpecToEquivOfField
   (ResidueField.lean:346), which identifies these with point/residue-field embedding
   pairs. Exact, with no restriction to closed or rational points.
4. Morphism a and triangle: `(a : Spec (.of k) ⟶ Spec (.of k'))`
   and `(ha : a ≫ s' = s)`. Exact order and direction. No IsIso a is assumed.
5. Transport of pointed neighbourhoods: `b := Over.homMk a ha` is the morphism over S;
   `α := Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)` precomposes a lift
   t with b. Read Etale.forget (Morphisms/Etale.lean:167) and pointSmallEtale's fibre
   (Sites/EtalePoint.lean:64): lifts are Over morphisms. Thus `(α.app U t).left` is
   `a ≫ t.left`, and its Over condition gives the required lift of s. Exact; the
   well-definedness clause is encoded in the term's type, not omitted as a hypothesis.
6. Parenthetical equivalence: `(CategoryOfElements.map α).IsEquivalence`.
   Elements.lean:162 fixes U and sends t to α.app U t, fixing underlying morphisms.
   Its source and target are precisely the pointed-neighbourhood categories. Exact.
7. Every sheaf of sets: `∀ F : Sheaf S.smallEtaleTopology (Type (max u v))`.
   Read smallEtaleTopology (Sites/Etale.lean:51), Scheme.Etale (Morphisms/Etale.lean:158)
   and Sheaf (Sites/Sheaf.lean:302). This is the full category of sheaves of sets on
   the given site. def-weil-pbc-etale-sheaves has a mixed record explicitly including
   this existing Sheaf notion; its locally constant predicates are irrelevant here.
   No private sheaf definition or additional dependency module is needed. Exact.
8. Source and target stalks: `(pointSmallEtale s').sheafFiber.obj F` and
   `(pointSmallEtale s).sheafFiber.obj F`. Read Point/Basic.lean:96,101,277: presheafFiber
   is the colimit over the opposite category of fibre elements; toPresheafFiber is
   its colimit coprojection; sheafFiber restricts it to sheaves. These are precisely
   the recorded def-weil-pbc-geometric-stalks declarations. Exact.
9. Unique map with the representative rule: P quantifies over every U, lift t and
   section σ, and says `f (toPresheafFiber U t F.obj σ) =
   toPresheafFiber U (α.app U t) F.obj σ`. `∃! f, P f` quantifies over all functions
   between those stalks, not just bijections. `∀ f, P f → Function.Bijective f`
   supplies the separate bijectivity conclusion for that unique map. Exact.
10. Abelian sheaf clause: `∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u v}`
    uses the recorded def-weil-pbc-abelian-etale-sheaves specialization of Sheaf.
    The map f is an AddCommGrpCat morphism; P is the equality of additive coprojections
    composed with f and the transported coprojection. Evaluated on σ it is the same
    representative rule. `∃! f, P f` and `∀ f, P f → IsIso f` express the unique
    additive map and its isomorphism. The underlying filtered-colimit map has the
    identical rule on all representatives, so this is the node's abelian assertion.
    No independent choice of a different map is allowed. Exact.

Edge cases: the empty scheme admits no geometric point, so these binders cover it
vacuously without an added nonemptiness assumption. Empty etale objects have no lifts
and impose no representative conditions. The initial set sheaf has empty stalks;
the zero abelian sheaf has zero stalks; the assertions give the unique empty/zero map.
Identity a and non-isomorphic field extensions are included. There is no index set or n
in this statement, and no restriction on characteristic. The geometric fields and S use
the ambient Scheme universe u, as the recorded pointSmallEtale and SpecToEquivOfField do;
objects of differing original sizes may be lifted to a common ambient universe. The
coefficient universe is max u v for independent v, allowing arbitrarily large sets and
abelian groups while supplying u-sized colimits. No independent smaller test universe,
unbound variable, or implicit extra instance is present.

Independent searches (queries actually run through msearch, recorded in searches.jsonl):
- LeanFinder: "precomposition algebraically closed field spectra equivalence etale
  neighborhoods stalk comparison" returned eight etale definitions/ring-map results,
  including Scheme.Etale and StandardEtalePair.homEquiv, none a stalk comparison.
- Loogle: `"pointSmallEtale"` returned seven fibre/conservativity declarations, no
  arbitrary-morphism comparison.
- LeanSearch: "etale neighborhoods geometric point field extension stalk functor
  equivalence" returned Internal Server Error; unavailable, no no-match verdict.
- rg over Mathlib AlgebraicGeometry/Sites and WeilConjectures, with
  `geometricPointMorphism|stalk_bijection|pointSmallEtaleCongr|coyoneda.map` and
  map/stalk variants, and over lean/Sheaf with geometric-morphism and stalk-congruence
  variants. Also searched dag/lean_names_upstream.json and the source for the item id
  and proposed declaration name. No name collision or exact existing statement found.
  Opened WeilConjectures/Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:435-465:
  pointSmallEtaleFiberCongr and pointSmallEtaleCongr require
  `e : Spec (.of Ω') ≅ Spec (.of Ω)`, whereas this node allows any morphism a.
  Reusing it would exclude field embeddings that are not isomorphisms. Other hits use
  stalks for pullback/base-change or Zariski comparisons, not this representative map.

No mathematical signature mismatch, node correction, missing notion, new node, or
dependency module was found. I kept the Lean signature and node lean.statement unchanged
and checked their verbatim equality. The only repair is to the proof docstring: name
lem-weil-pbc-residue-field-point-naturality, the etale residue-field-extension lemma,
def-weil-pbc-geometric-stalks and the cofiltered-neighbourhood lemma explicitly at their
steps. All five node proof steps remain, including the unique lift factorization and
colimit inverse. The module has no definitions, its only theorem proof is `sorry`,
and its source/blueprint docstrings, namespace, imports and line lengths comply.

Validation: compiled the final module with scompile.py against the server build;
only the permitted declaration-uses-sorry warning is allowed. The signature has explicit
universes u v and all binders. Delivery preflight is run after this review.
