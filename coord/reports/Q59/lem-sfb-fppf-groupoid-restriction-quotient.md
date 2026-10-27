## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.fppf_groupoid_restriction_quotient`
in `Sheaf.AlgebraicGeometry.FppfGroupoidRestrictionQuotient`. Its only postponed proof
is that theorem, with the five-step proof in its docstring. The three definitions
in the same module construct the middle projection, the induced map on composable
pairs, and the induced map of presheaf coequalizers. All have actual data and no
postponed proofs. They belong to the restricted-groupoid construction of this node,
not to independent new notions. The node's statement, proof, and proof_deps are
unchanged. Its stmt_deps gains the new definition node
`def-sfb-restricted-groupoid-relation`, which records the existing iterated
pullback and endpoint maps with `existing: true`. There are no dependency-module
repairs and no copied definitions. The unused theorem dependency from the
returned delivery has been removed.

The inherited BLOCKED ending concerned the already accepted stage-1 split. The
current assignment is stage 2: the live item has reviewed.result = pass for its
split, but no lean or reviewed_lean record. The stage-handoff paragraph in
coord/brief-stage2.md explicitly says to continue stage 2 in this situation.
This repair addresses the immutable-head H2 return on 48ef2a5c1878,
which requires a definition owner for the existing pullbacks.
No stage-1 field is reopened by this delivery.

Hypotheses and clauses, with their Lean renderings:

* A base scheme in the chosen bound is `{S : Scheme.{u}}`, with explicit `universe u`.
  All schemes over it are `{R U U' : Over S}`. The morphisms in `Over S` express
  precisely that all structural maps commute with the maps to S.
* The given groupoid is `(s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)` and
  `(c : pullback s.left t.left ⟶ R.left)`, with
  `hG : IsGroupoidScheme s.left t.left e.left i.left c`. This uses the recorded
  absolute groupoid predicate, without making a duplicate relative predicate.
  Its composition_source law implies that c commutes with the structure map to S:
  postcompose that law with U.hom and use s.w. Hence taking c on the underlying
  scheme pullback loses no requirement of a groupoid over S and adds none.
* The restriction map is `(q : U' ⟶ U)` with the three independent instance
  hypotheses `[Surjective q.left] [Flat q.left] [LocallyOfFinitePresentation q.left]`.
  These are exactly the stated singleton fppf covering condition. There is no
  etaleness, quasi-compactness, separatedness, or affine hypothesis on any map.
* The restricted arrow object is the existing `restrictedEtaleRelation s t q`,
  definitionally `pullback (pullback.snd q s ≫ t) q`. Its source is
  `restrictedEtaleRelationSource s t q`, its target is
  `restrictedEtaleRelationTarget s t q`, and its middle projection is the new
  `restrictedGroupoidMiddle s t q`. The underlying pullbacks represent exactly
  triples (x,r,y) with qx = sr and tr = qy. The old helper names contain Etale,
  but their definitions have no etale assumptions and are valid for these maps.
* The first conjunct supplies restricted identity, inverse and composition
  `e'`, `i'`, `c'` and asserts `IsGroupoidScheme` for them. Their middle-coordinate
  equations are respectively `e' ≫ middle = q ≫ e`,
  `i' ≫ middle = middle ≫ i`, and
  `c' ≫ middle.left = restrictedGroupoidComposableMap s t q ≫ c`.
  These fix the canonical operations, rather than unspecified choices: the
  groupoid laws fix the outer coordinates, and the iterated pullback's universal
  property makes a morphism unique from its outer and middle coordinates.
  In particular composing (x,h,y) followed by (y,r,z) has middle c(r,h).
* The second conjunct is explicitly an implication from
  `Mono (prod.lift restrictedSource restrictedTarget)` to `Mono (prod.lift s t)`.
  Products in Over S are fibre products over S. Thus these are exactly the two
  displayed monomorphisms R' -> U' x_S U' and R -> U x_S U. Categorical monicity
  is injectivity on all test-S-scheme sections. Both subsequent `∀ T : Over S,
  Equivalence ...` clauses spell out existence of an arrow with specified
  source and target. Together with monicity, this says the groupoids are
  equivalence relations, including uniqueness of the witnessing arrow.
* The two presheaves in `restrictedGroupoidQuotientMap` are coequalizers of the
  respective two `uliftYoneda.{u + 1}.map` transformations. Colimits in presheaf
  categories are pointwise, so these are the pointwise set quotients by arrow
  endpoints. For a groupoid, arrow existence is already an equivalence relation
  by identity, inverse and composition; hence this coequalizer is exactly its
  presheaf of isomorphism classes, also with nontrivial isotropy. No monicity is
  required for that identification. ULift only places these sets in the containing
  universe and changes neither their elements nor their equivalence classes.
* The canonical map is actual `coequalizer.desc` data, induced by
  `uliftYoneda.map q` followed by the original coequalizer projection. The
  pullback endpoint equations and `coequalizer.condition` give its defining
  compatibility. Therefore it sends [x] to [qx], with no arbitrary map parameter,
  no choice from a mere existence statement, and no inverse posited as data.
* The final conjunct is
  `IsIso ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (restrictedGroupoidQuotientMap s t q))`. This is exactly the canonical
  map U'/R' -> U/R after fppf sheafification. Its type has no monicity hypothesis:
  the preceding implication is a separate conjunct, not a binder for this one.
* The big site has object universe u+1 and hom universe u. Values are in
  `Type (u + 1)`, so Mathlib's sheafification instance applies to this very site;
  no site-universe equality, essentially-small hypothesis, or additional
  sheafification-existence hypothesis is imposed. This implements the recorded
  size convention in a containing universe and retains every scheme in the bound.

Dependency declarations read and used:

* def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
* def-weil-size-convention: the recorded metatheoretic convention, implemented
  by the explicit universe above; it intentionally records no Lean declaration.
* def-a1-groupoid-scheme: `AlgebraicGeometry.IsGroupoidScheme` in
  `Sheaf.AlgebraicGeometry.GroupoidScheme`, including its full list of laws.
* def-weil-surjective-morphism: `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
* def-weil-flat-morphism: `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; its recorded stalkwise equivalence
  is `Flat.iff_flat_stalkMap`.
* def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
* def-pc-fppf-site: `Scheme.fppfPrecoverage` and `Scheme.fppfTopology` in
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`, and `GrothendieckTopology.over` in
  `Mathlib.CategoryTheory.Sites.Over` for the big site over S.
* def-pc-fibre-product: `CategoryTheory.Limits.pullback`, its projections, and
  `pullback.map` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
* def-weil-pbc-sheafification: `CategoryTheory.presheafToSheaf` in
  `Mathlib.CategoryTheory.Sites.Sheafification`, with its standard existence
  instance exported by `Mathlib.CategoryTheory.Sites.LeftExact`.
* Added definition owner def-sfb-restricted-groupoid-relation:
  `restrictedEtaleRelation`, `restrictedEtaleRelationSource`, and
  `restrictedEtaleRelationTarget` in
  `Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`. Only its definitions
  are reused; its theorem is not applied and cannot replace this result because
  that theorem assumes etaleness and relation monicity.

The proof dependencies already stated in Mathlib are available through the
imports of Fpqc and LocallyBijective: fppf base change, fppf-to-fpqc comparison,
subcanonicity for representable fpqc descent, and the set-valued local-bijection
criterion. None was copied or reproved. The named theorem has exactly `by sorry`.

Source reading: literature/stacks-project/groupoids.tex, labels
lemma-restrict-groupoid (02VB) and lemma-quotient-groupoid-restrict (02VH);
literature/stacks-project/descent.tex, lemma-descending-property-monomorphism
(02YK). The main docstring follows the accepted five-step split. The restriction
operations use the explicit formulas of step 1, the two successive endpoint covers
give reflection of monicity, and the orbit map is sectionwise injective and locally
surjective, so the set-valued local-bijection criterion applies.

Edge cases checked before and after writing:

* q = identity: restriction is the original groupoid up to the canonical pullback
  isomorphism and the displayed coequalizer map becomes the identity under it.
* U empty: U' and R must be empty as well. Sections over empty test schemes are
  still handled by the actual Hom types; no Nonempty assumption is present.
* The fold cover U disjoint-union U -> U: q need not be monic and no such
  assumption enters either conclusion.
* A one-object groupoid from a nontrivial group scheme: the quotient statement
  remains valid, while monicity is asserted only conditionally. Nonunique arrows
  are retained in the coequalizer construction.
* A covering without a global section: all constructions use pullbacks and
  coequalizers, with no assumption or choice of a global endpoint lift.
* An fppf cover which is not quasi-compact, and arbitrary non-affine or
  non-separated schemes: none is excluded by the signature or helper definitions.

Searches actually run for this item:

* msearch.py leanfinder, `Restriction of a groupoid scheme along an fppf cover
  induces an isomorphism of quotient sheaves`: eight hits on restriction,
  scheme gluing and cover-dense subsite comparison; no matching groupoid theorem.
* msearch.py loogle, `"Sheaf", "Groupoid"`: two hits on manifold structure
  groupoid sheaves, neither the scheme-groupoid statement.
* msearch.py grep, `groupoid.*quotient|quotient.*groupoid|groupoid.*restrict`,
  AlgebraicGeometry: zero hits.
* msearch.py leansearch, `An fppf covering restriction of a scheme groupoid
  induces an isomorphism of its quotient sheaf`: eight generic sheafification,
  cover-dense and scheme-restriction hits, no exact statement.
* rg over lean/WeilConjectures and lean/Sheaf for groupoid restriction,
  orbitPresheaf, groupoidQuotient, quotientSheaf and IsGroupoidScheme: found
  GroupoidScheme and the already existing etale-relation interfaces. The
  existing iterated pullback definitions were read in full and reused.
  rg for this node id in lean/WeilConjectures found no declaration.
* rg across dag/nodes for groupoid quotient and orbit-presheaf notions, and
  tools/blueprint_refs.py search `groupoid quotient restriction`: no blueprint
  match. Existing related nodes do not state this general groupoid result.

Validation: scompile.py compiled the delivered module in sandbox mode and in its
actual library module name, both with exit code 0 and no diagnostics. All source
lines are at most 91 characters. No auto-bound variable, sorry-valued definition,
or extra hypothesis is present. The repository and launcher files were read only;
all writes are confined to the assigned sandbox or the authorized wrappers.
No STATEMENT-DISPUTED finding or statement correction is needed.

## Second reading by Q59

I made a separate second pass with the node, Lean signature and Stacks source open.
This is a second reading by the dispatched worker, not a claim that another agent
read it: this assignment explicitly prohibits starting other agents. Independent
review remains the maintainer's delivery review.

I checked all three fppf hypotheses separately, the base-S compatibility of the
absolute groupoid predicate, the orientation c(r,h), and the source/target order
of the iterated pullback and `pullback.map`. The first outer coordinate is
pullback.fst followed by the inner pullback.fst; the middle is pullback.fst then
inner pullback.snd; the last coordinate is the outer pullback.snd. These coincide
with the node's (x,r,y) description. Restricted operations are fixed by their
middle equations and their groupoid endpoint laws, so the existential groupoid
data in the conclusion does not substitute arbitrary structures.

I checked the conditional monicity and its two equivalence-relation clauses
against the first part of the node. I then checked that the final IsIso conjunct
lies outside that implication, that both coequalizers retain all arrows rather
than assume a relation is thin, and that coequalizer.desc fixes the canonical map
on representatives. Finally I checked the site and coefficient universes: they
are u+1/u and u+1, respectively, with no hidden universe identification. No
mismatch was found in this pass and no statement change was made.


## Repair of immutable-head H2 return

The return on 48ef2a5c1878 found that the extra statement dependency was a
theorem although only its three plain definitions were used. I added
`def-sfb-restricted-groupoid-relation` with `existing: true` on the published
module and listed exactly those three definitions. The item now cites this
definition node instead of `lem-trf-etale-relation-restriction-quotient`.
The item module is retained byte for byte from the saved packet; its signature,
mathematical statement and proof plan are unchanged. The item node was checked
against current main: all fields except lean and stmt_deps agree, and its only
stmt_deps addition over main is the new definition node. The initial saved-packet
dry run passed at 1b405bf0f67; the H2 ownership repair is made before delivery.

## New nodes

`def-sfb-restricted-groupoid-relation` records the underlying iterated pullback
relation and its source and target in Stacks 02VB. Its objects are arbitrary
S-schemes, its maps are arbitrary S-morphisms, and no groupoid law or cover is
assumed. The three existing definitions in
`Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient` say exactly this,
despite their historic Etale names; the full signatures were checked both
locally and with `scompile.py --source`. The node reuses them with existing:true,
so there is no new Lean module or duplicate definition. The source's extra
groupoid-structure conclusion belongs to the item, not to this underlying
relation definition. No existing DAG definition owns the three declarations.
The related theorem nodes have additional conclusions and hypotheses.

The complete existing signatures (with explicit universe u and namespace
AlgebraicGeometry.AlgebraicSpace) are:

```lean
noncomputable def restrictedEtaleRelation {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : Over S
```

```lean
noncomputable def restrictedEtaleRelationSource {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : restrictedEtaleRelation s t g ⟶ U'
```

```lean
noncomputable def restrictedEtaleRelationTarget {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : restrictedEtaleRelation s t g ⟶ U'
```

For each clause of the new node: `{S : Scheme.{u}}` supplies the base and
chosen bound; `{R U U' : Over S}` supplies the three S-schemes; `(s t : R ⟶ U)`
and `(g : U' ⟶ U)` supply the maps, with g the node's q. The defining body
`pullback (pullback.snd g s ≫ t) g` is the stated two successive fibre products.
The source body is
`pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s` and the target body
is `pullback.snd (pullback.snd g s ≫ t) g`. These select x and y in (x,r,y).
The two pullback conditions are exactly qx=sr and tr=qy. No instance binders
impose any of the excluded properties. Its dependencies are the existing
scheme, size-convention and fibre-product definition nodes.

Repair searches (raw msearch results are preserved in the new node):

* LeanSearch: "The restriction of a scheme relation along a morphism is the
  iterated pullback with its two endpoint projections". Eight restriction and
  pullback-restriction hits, none defining this two-endpoint construction.
* LeanFinder: "Restrict a scheme groupoid relation by pulling back both endpoints
  along a morphism". Eight gluing/open-restriction hits, none matching.
* Mathlib grep in AlgebraicGeometry:
  `restrictedEtaleRelation|restrictedGroupoid|restrict.*[Gg]roupoid`: zero hits.
* Project/source rg for `restrictedEtaleRelation|restrictedGroupoid`: no
  WeilConjectures match; the three exact definitions in the published Sheaf
  module and other modules consuming them.
* DAG rg for `restrictedEtaleRelation|restricted-groupoid-relation|02VB`: related
  theorem nodes, no definition owner. `tools/blueprint_refs.py search
  'restricted groupoid relation'` returned zero matches. Its ancestor command
  returned None; blueprint.from preserves that and prepends this item to via.

I separately reread the new node against the three existing definition bodies
and Stacks 02VB. Identity q, empty U, nonmonic fold maps, and nontrivial isotropy
all retain the same unrestricted pullback construction. No source assumption
is lost: a groupoid is required for the groupoid laws in the item, while the
underlying relation and endpoints use only the maps s,t,q. This supplements
`## Second reading by Q59` above and confirms the requested H2 change.

Final repair validation: scompile.py compiled the unchanged module under both
its sandbox and actual library names (exit 0). The first repaired dry run asked
for `import_flags` on the new node and for the signature to start at `def` rather
than the `noncomputable` modifier; both record-format findings were repaired.
The new node records an empty import_flags list. The declaration remains
noncomputable in its unchanged published source.
