## Worker report

The delivery states `lem-trf-space-fibre-products-etale-covers` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, with three theorems,
each having exactly `sorry` as proof. It also supplies one missing real definition,
`AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`, in its own definition node/module.
The item's statement, proof, proof dependencies, and all other existing fields are unchanged;
its `stmt_deps` only gains that definition node. No statement correction or dependency repair
is required. No mathematical dispute was found.

Hypotheses and clauses of the item, read against the Lean files:

- `S` is a scheme: `{S : Scheme.{u}}` in every declaration. All schemes, presheaf values,
  and the fields whose spectra lie in the big site use the same `u`, following the recorded
  algebraic-space definition. Family indices have arbitrary independent universe `w`.
- `F,G,H` are algebraic spaces over `S`: `(F G H : AlgebraicSpace S)` in
  `fibreProduct_isAlgebraicSpace`. This is the recorded full subcategory of fppf sheaves
  with representable diagonal and a representable surjective étale scheme atlas.
- Morphisms `F → H` and `G → H`: `(f : F ⟶ H) (g : G ⟶ H)`. Their `.hom` fields are
  the corresponding sheaf morphisms; `.hom.hom` is the underlying natural transformation.
- The *sheaf* fibre product is an algebraic space: the first conjunct is
  `IsAlgebraicSpace (Limits.pullback f.hom g.hom)`. It uses the canonical pullback in the
  category of fppf sheaves, with the actual structure predicate from the dependency.
- It is the categorical fibre product among algebraic spaces over `S`: the second conjunct
  quantifies over every `Q : AlgebraicSpace S`, arrows `a : Q ⟶ F`, `b : Q ⟶ G`, and
  compatibility `a ≫ f = b ≫ g`, and asserts a unique sheaf arrow into that *same* sheaf
  pullback whose two projection composites are `a.hom` and `b.hom`. This is precisely the
  universal property in the full subcategory: the first conjunct puts the target sheaf in
  that subcategory, whose Hom types are the same sheaf Hom types. There is no restriction
  to scheme test objects in this categorical universal property.
- An arbitrary jointly surjective étale family: `etaleCover_pullback` quantifies over
  `{I : Type w}`, `(Hᵢ : I → AlgebraicSpace S)`, `(h : ∀ i, Hᵢ i ⟶ H)`;
  `he : ∀ i, IsEtale (h i).hom.hom` is representable étaleness, using the recorded
  scheme-test definition. `hs : IsJointlySurjective (fun i ↦ (h i).hom.hom)` is exactly
  joint surjectivity on field-valued point classes, as expanded below.
- `G → H` is arbitrary: `(G H : AlgebraicSpace S) (g : G ⟶ H)` has no property hypothesis.
- The pulled-back family consists of `G ×_H Hᵢ → G`: the maps in both conclusions are
  `(Limits.pullback.fst g.hom (h i).hom).hom`, i.e. the first projections of the sheaf
  pullbacks in this order. Their source sheaves are algebraic spaces by the first theorem,
  applied to `G,Hᵢ i,H,g,h i`. Thus the second theorem uses exactly those algebraic spaces,
  without introducing arbitrary replacement objects or maps.
- Each pulled-back member is representable étale: the first conjunct of
  `etaleCover_pullback` is `∀ i, IsEtale (...)`. The second conjunct is joint surjectivity
  of these exact first projections, with the same index type.
- Scheme special case: `etale_fibreProduct_isScheme` takes algebraic spaces `G,H,H'`,
  arrows `g,h`, representable étaleness `he`, an arbitrary scheme `T : Over S`, and an
  isomorphism `e : G.obj.obj ≅ yoneda.obj T` expressing that `G` is a scheme. Its conclusion
  `∃ U : Over S, Nonempty ((Limits.pullback g.hom h.hom).obj ≅ yoneda.obj U)` says that
  this very fibre product is represented by a scheme. No choice of representing scheme is
  introduced as data. This clause depends only on étaleness of the individual member,
  as the node's scheme-test explanation says; joint surjectivity is irrelevant to it.
- Meaning of point sets and joint surjectivity: `IsJointlySurjective` expands the
  union-of-images condition without forming a quotient. It quantifies over every field
  `K : Type u`, every base map `s : Spec (.of K) ⟶ S`, and every representative
  `x : F.obj (op (Over.mk s))`. It asks for an index, extension field `L`, ring homomorphism
  `e : K →+* L` (automatically an embedding between fields), and a source representative
  `y` over `Spec L` with the displayed equality to the restriction of `x` along `Spec e`.
  If the point class of `x` is the image of a representative over another field `K'`, the
  common extension `L` in the node's equivalence relation makes its restriction into
  just such a `y`. Conversely such a `y` represents a source point mapping to `[x]`,
  with `L` itself witnessing common-extension equality. Therefore this is the exact
  quotient-point image condition, not surjectivity on `K`-valued sections at a fixed field,
  not sheaf epimorphy substituted for point-surjectivity, and not individual surjectivity
  of each member. A presheaf section is the corresponding map from a representable by
  Yoneda, as explicitly explained immediately before Stacks Tag 03BU.

Dependency declarations inspected and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; read their full structure signatures and docstrings.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsAlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `AlgebraicSpace.IsEtale`; read the whole module.
  No copy of the category, diagonal condition, atlas condition, or étale predicate is made.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`,
  and the universal-property signatures. Scheme permanence proofs use scheme pullbacks;
  the stated object is the sheaf pullback using the same categorical construction.
- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`), read the full signature
  and docstring. The new definition quantifies over actual fields and actual field maps.
- Proof dependency `def-weil-pbc-sites-and-cohomology`: the recorded
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, `CategoryTheory.Precoverage.IsSiteForCoverings`,
  with its documented Mathlib sheaf conventions; imported without `public`.
- Scheme permanence proof dependencies: `Mathlib.AlgebraicGeometry.PullbackCarrier`,
  `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.instSurjectiveCompScheme` (included through `PullbackCarrier`);
  and `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale.etale_isStableUnderBaseChange`, `Etale.etale_comp`, and
  `Etale.of_comp`. The recorded files, signatures and explanatory docstrings were read.
  These proof-only imports keep the existing seven-step DAG proof plan available.

Source checks: read Stacks `spaces.tex` Tags 04T9 and 02X2, `spaces-topologies.tex`
Tag 041F(3), and `spaces-properties.tex` Tag 03BU with its preceding common-extension
relation, and Tag 03H4. The first theorem's docstring gives steps 1–5 of the node's
proof, including the scheme equality loci and atlas `U ×_H V`. The cover theorem's
proof docstring gives steps 6–7, including the common-extension point lift and empty-index
case. The scheme theorem's docstring records the scheme-test specialization of step 6.

Edge cases checked before drafting: no `Nonempty I` or finiteness assumption is present.
For `I` empty, `hs` forbids any field-valued target representative; any source point would
map to such a target point, so the pulled-back family covers the empty source point set.
Empty schemes/base schemes are permitted. Identity maps and isomorphic representing
schemes are permitted. Fields of every characteristic are covered; no separability,
algebraic-closedness or cardinality condition is imposed. The definition allows arbitrary
extension fields in the same universe as the big site, not a separately smaller universe.
A field embedding is not required to be an isomorphism: replacing it by an isomorphism
would incorrectly demand lifting over the original residue field. No flatness,
quasi-compactness or separatedness hypothesis is added.

Searches for an existing statement/notion:

- `msearch.py` LeanFinder, query “Fibre products of algebraic spaces exist and jointly
  surjective etale covering families are stable under base change”: 8 hits on schemes,
  including `Scheme.instIsStableUnderBaseChangeJointlySurjectivePrecoverage` and
  `IsEtale.instIsStableUnderBaseChangeScheme`; none state this algebraic-space theorem.
- Loogle query `AlgebraicSpace, IsEtale, pullback`: 0 hits, unknown identifier
  `AlgebraicSpace`. Mathlib grep `AlgebraicSpace|jointlySurjective|IsJointlySurjective`
  under `AlgebraicGeometry`: 25 scheme-level hits, no algebraic-space definition/theorem.
- LeanSearch and LeanFinder query “joint surjectivity of algebraic space families using
  field valued points after field extension”: 8 hits each. LeanSearch returns the scheme
  `JointlySurjective` precoverage class and related scheme results; LeanFinder returns
  scheme pointsPi, gluing and covering results. Neither supplies the presheaf point-image
  condition needed here. Loogle `AlgebraicSpace, Field, Surjective`: 0 hits.
- Mathlib grep `field.*point|Point.*[Ff]ield|jointly[Ss]urjective|IsJointlySurjective`
  under `AlgebraicGeometry`: 25 hits, covering scheme point/cover constructions and
  geometricFiber, no point-image predicate for algebraic spaces.
- `rg` in upstream `WeilConjectures` for `AlgebraicSpace|algebraic.space` and for the item
  id: no matches. Search for `jointlySurjective|IsJointlySurjective` finds scheme étale
  sheaf conservativity references, not algebraic spaces. The upstream name index has no
  `AlgebraicSpace` or `IsJointlySurjective` match.
- `rg` in `lean/Sheaf` finds the recorded `AlgebraicSpace.lean` and scheme-level cover
  usages, no existing algebraic-space fibre-product theorem or point-surjectivity predicate.
- DAG text search for point/common-extension/joint-surjectivity language finds the item
  and scheme-specific results, no node carrying this predicate. `blueprint_refs.py search
  'jointly surjective'` returns 9 scheme/pro-étale/constant-sheaf nodes, none this notion.
  Search for the new id has no match. `blueprint_refs.py ancestor` confirms the ancestor
  is `lem-trf-local-term-locality`.

Validation: both delivered modules were compiled separately through `scompile.py` in
sibling dependency order, using the private side-project overlay. Both compile without
errors or warnings. All variables/universes are explicit, every theorem proof is `sorry`,
and the definition contains actual quantified data with no proof hole or arbitrary choice.

## New nodes

`def-trf-algebraic-space-jointly-surjective-family` defines joint surjectivity on point
classes through the exact field-extension lift formula explained above. Its source is
Stacks Properties of Spaces Tag 03BU and its preceding presheaf discussion, together with
the étale-covering convention of Topologies on Algebraic Spaces Tag 041F. It has its own
module `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` and actual definition
`AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`. The searches recorded above and
in its `mathlib_searches` show why the scheme precoverage predicate cannot supply this
notion for presheaves/algebraic spaces. The item's statement dependency list gains this
id. The original point-quotient meaning is preserved; no statement change is made.

## Second reading by Q98

Independent maintainer second reading of immutable delivery
`ce275a1ea175b102e369367d6df04e22a368d34f`, performed on 2026-10-18.
This section records the present independent review, not an earlier reading by a Q98 worker.
The packet, snapshot item, all five statement-dependency records, both delivered Lean
files, imported dependency declarations, report, and cited Stacks passages were opened.

Clause-by-clause verdicts:

- Base and objects: `{S : Scheme.{u}}` and `F G H : AlgebraicSpace S` use the recorded
  scheme category and full subcategory of fppf sheaves. The latter's actual predicate
  asserts a representable diagonal and a representable surjective etale scheme atlas.
  The morphisms `f` and `g` have exactly the stated sources and target. Correct.
- Sheaf fibre product: `IsAlgebraicSpace (Limits.pullback f.hom g.hom)` concerns the
  canonical sheaf pullback, not a scheme pullback or an arbitrary chosen sheaf. Correct.
- Categorical universal property: every algebraic space `Q`, every compatible `a,b`,
  and a unique sheaf map `l` with both projection identities are quantified. Since the
  category is full and the first conjunct proves membership, this is precisely the
  universal property in algebraic spaces. Correct.
- Cover hypotheses: `I : Type w` is arbitrary, `he` uses the dependency's representable
  `IsEtale`, and `hs` uses the new field-extension lifting predicate. There is no
  condition on the base-change map `g`. Correct.
- Cover conclusion: both etaleness and joint surjectivity apply to the exact first
  projections from `Limits.pullback g.hom (h i).hom`, with the same indices. The first
  theorem supplies algebraic-space membership of these source sheaves. Correct.
- Scheme clause: `e : G.obj.obj ≅ yoneda.obj T` expresses that `G` is a scheme over `S`;
  the conclusion asserts representability of that very sheaf pullback. Quantifying
  over all representing schemes and isomorphisms adds no mathematical assumption.
  The individual etale hypothesis suffices, independently of the cover clause. Correct.
- Point meaning: for each field `K`, base map `s`, and section `x`, the new definition
  gives `i,L,e,y` with `(f i)(y) = x|_L`. A unital ring homomorphism between fields is
  injective. If a point is in an image, restriction of its source representative to
  the common extension gives this witness; conversely the witness gives equality of
  point classes. The formula has the correct restriction direction and base map.
  It does not require lifting over `K` itself. Correct.

The new definition node is a legitimate missing-notion addition under section 1(A): its
three cited dependencies are exactly its statement references; source, empty proof fields,
searches, creation data, chapter/unit, ancestry and Lean binding meet the field rules.
There is no statement correction or dependency repair, so no correction citer audit is due.
Both delivered `lean.statement` fields match their file signatures verbatim.

Source verification used the read-only Q98 literature: `spaces.tex` lines 804-821
(Tag 025Y), 914-953 (04T9), and 957-971 (02X2); `spaces-topologies.tex` lines 205-226
(Tag 041F(3)); `spaces-properties.tex` lines 226-260 (point equivalence and 03BU) and
281-309 (03H4). The diagonal equality loci, atlas `U ×_H V`, full-subcategory universal
property, scheme-test etaleness, and common-extension lift agree with those sources.
The module and declaration docstrings include sources and blueprint ids; the three theorem
docstrings collectively reproduce all seven DAG proof steps.

Declarations checked directly: Q98 `AlgebraicSpace.lean`, in particular
`IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`, and `AlgebraicSpace`;
Mathlib `Scheme`, `Scheme.Hom`, `Field`, `Limits.pullback`, `pullback.fst`, `pullback.snd`,
`pullback.lift`, and scheme pullback existence. The proof imports provide scheme
surjectivity base change/composition, etale base change/composition/cancellation, and
`Precoverage.IsSiteForCoverings`; no alternative notion is substituted.

Independent searches with `AlgebraicSpace`, `algebraic.space`, `jointlySurjective`,
`IsJointlySurjective`, point-class and common-field language in Mathlib, upstream
`WeilConjectures`, the side library, DAG and upstream name index found no duplicate
algebraic-space closure theorem or point-image predicate. Scheme cover predicates and
scheme etale-sheaf conservativity do not define this presheaf predicate. The worker's
LeanSearch, LeanFinder/Loogle and text-search records were also read.

Edge cases: empty `I`, empty source or base scheme, identity maps, arbitrary representing
isomorphisms, arbitrary field characteristics and nontrivial field extensions are covered.
All site objects, field spectra and presheaf values use the dependency's universe `u`;
`w` is independent only for the family index. No new universe equality, finiteness,
separability, quasi-compactness, separatedness or nonemptiness assumption is present.
There is no hollow definition, arbitrary construction, local proof beyond `sorry`, or
pro-etale substitute. The three theorem bodies are exactly `by sorry`; the definition
has no `sorry`. No delivered Lean line exceeds 100 characters; binders and universes
are explicit. No direct dependency is on the route-pivot dropped list, no dropped
machinery appears, and no route-pivot repair note for this item exists in the inspected
`origin/newtargets-dag` tree.

Compiler reproduction: ran the prescribed `scompile.py Q98
lem-trf-space-fibre-products-etale-covers` on both immutable snapshot Lean files, with
`AlgebraicSpaceJointSurjectivity.lean` first. Exit code 0, no errors or warnings. The
installed wrapper identifies itself as the 2026-10-17 server-side private-overlay
implementation; it compiled the sibling overlay, each sandbox file and each library
file separately under the 60-second limit. The final library checks took 2.2 s and
3.0 s respectively. This corroborates the worker's clean per-file compilation claim;
it is not a claim that the installed wrapper performed a Codex-host local compile.
No direct ssh command, global build, repository edit, or Git mutation was performed.

Finding and correction: H11, the delivered second-reading section only said that no
reading occurred. This replacement supplies the actual independent reading above and
preserves the Worker report and New nodes sections. No mathematical, Lean or node-record
change is needed.
