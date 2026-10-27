## Worker report

The module `Sheaf.Paper.WStrictCommonComponentHypercovers` states
`AlgebraicGeometry.ProEtale.wstrict_common_component_hypercovers`, with a single
`sorry` and the complete nine-step proof plan in its docstring. Three fully written
helper definitions package parts of this statement. Three new definition nodes own already existing definitions; no definitions are copied.
There are no dependency-module repairs, statement corrections or disputed assertions.

The previous attempt reported a stage-1 live-wins prohibition. This assignment is
stage 2: `coord/brief-stage1.md` section 1 explicitly says that stage 2 may state an
unchanged statement independently and must not repeat an already-reviewed stage-1
BLOCKED disposition. The Q06 passing split has no Lean record, and is the proof
plan used here. No stage-1 split or review field has been changed.

Hypotheses, in the order of the node:

- `X X' : Scheme.{u}`, `[IsAffine X]`, `[IsAffine X']` are the two affine schemes;
  `h : X' ⟶ X` is an arbitrary scheme morphism. Neither surjectivity, flatness,
  locality nor preservation of closed points is imposed on h.
- `[IsWStrictlyLocalRing Γ(X, ⊤)]` and the identical binder for X' impose precisely
  w-strict locality of the two coordinate rings. Global sections are the coordinate
  rings of these affine schemes.
- `e : ConnectedComponents X' ≃ₜ ConnectedComponents X` together with
  `he : ∀ x, e (ConnectedComponents.mk x) = ConnectedComponents.mk (h x)` says
  exactly that the induced component map is a homeomorphism. Every component has a
  point, so he determines e uniquely: it is not an independently chosen action.
- `affineComponentSpace X` is the existing bundled quotient component space P,
  with the existing quotient topology. `Homeomorph.refl _` identifies the first
  base with P and `e.symm` identifies the second.
- Universe `u` is explicit. Profinite objects and schemes use universe u, the full
  `Scheme.ProEt` site has object universe u+1 and morphism universe u, and set sheaves
  in weak contractibility have values in `Type (u+1)`. There is no extra equality
  of these site universes, no bound on component cardinality beyond that convention,
  and no coefficient ring to restrict. Every variable is explicitly bound and
  autoImplicit and relaxedAutoImplicit are both false.

Conclusions, clause by clause:

- `S : SimplicialObject (Over (affineComponentSpace X))` supplies the augmented
  simplicial profinite space. Working in the slice gives every augmentation and
  its compatibility with every operator, including faces and degeneracies.
- `IsCommonProfiniteHypercover S` quantifies proper-face cones `M` and arrows μ.
  It fixes `(M 0).pt = Over.mk (𝟙 P)`, requires `IsLimit (M n)` in every degree,
  and gives the equation of the matching map with every proper-face projection.
  It requires surjectivity of `(μ n).left`, extremal disconnectedness of each
  profinite term, and surjectivity of each augmentation `(S _⦋n⦌).hom`.
- `U : SimplicialObject X.ProEt` and `V : SimplicialObject X'.ProEt` are objects
  of the full small pro-etale sites, not an affine-only category. Their structure
  arrows give their augmentations and their functor laws give all identities.
- The two instances of `IsCommonComponentHypercoverLift` specify their lifted
  topology, rings, and canonical component projections p and q. They are auxiliary
  predicates packaging this node's conclusion, not a second definition of the
  relative-component functor. The existing relative lift is characterized by
  its pullback locally ringed space (Bhatt--Scholze 2.2.8 and the recorded relative
  site's universal property). A homeomorphism over T together with stalkwise
  isomorphism of the structure arrow identifies the sheaf with the inverse image
  of the structure sheaf on T: the canonical sheaf map is stalkwise invertible.
  Hence these are exactly the finite-clopen-limit relative lifts, canonically,
  rather than arbitrary weakly contractible covers or a mere Nonempty choice.
- The first conjunct of the lift predicate supplies its proper-face limiting
  cones, degree-zero matching object `Scheme.ProEt.mk (𝟙 T)`, matching projection
  equations, and membership of `Presieve.singleton (μ n)` in `ProEt.precoverage`.
  Thus each matching arrow is a pro-etale covering in the actual full site.
- Its next conjunct gives `IsAffine`, `IsWContractibleRing Γ(U_n.left, ⊤)`, and
  `(ProEt.topology T).IsWeaklyContractible.{u+1} U_n` for every term. The latter is
  the recorded site definition of surjectivity on sections for locally surjective
  sheaf maps, equivalently epimorphisms of set sheaves.
- Its naturality equation for p quantifies every arrow of SimplexCategoryᵒᵖ.
  Together with the base-coordinate naturality already in the slice, it says the
  underlying operator is exactly `(x,s) ↦ (x,a(s))`.
- For every term it gives a homeomorphism to
  `{z : T × S_n | ConnectedComponents.mk z.1 = a (t_n z.2)}` with the product
  subspace topology. The two equations specify the structure arrow and the
  projection p. `IsIso (U_n.hom.stalkMap x)` identifies the local rings with the
  local rings at the first coordinate, via the actual structure morphism.
- The next two homeomorphisms identify `ConnectedComponents U_n.left` and
  `closedPoints U_n.left` with S_n. Their pointwise equations identify them with
  the same canonical projection p. This covers both component and closed-point
  clauses in the node.
- For each term the displayed `colimit (Algebra.stoneanPartitionDiagram ...)`
  is exactly D_n. Its Q-stage is the product over the nonempty fibres of a finite
  discrete quotient Q of `WContractification.Restriction (f '' Q.proj⁻¹{b})`.
  `Restriction` is literally the colimit of `Localization.Away e_W` over the
  opposite poset of clopen neighbourhoods of that inverse-image closed set in
  Spec Γ(T,⊤); clopens of the spectrum and of its component quotient correspond.
  Thus it gives precisely C_Z, the idempotent localization, and the specified
  refinement arrows, without introducing a second version of either colimit.
- `commonHypercoverBaseMap T a E` is the real continuous map taking the
  augmentation to the connected-component coordinates of Spec Γ(T,⊤), using
  the canonical affine isomorphism `T.isoSpec`.
- `k : U_n.left ≅ Spec (.of D_n)` is the ring-model isomorphism. Its composite
  with `Spec.map (algebraMap Γ(T,⊤) D_n)` and `T.isoSpec.inv` is exactly the
  structure arrow. The comparison `e : D_n ≃ₐ[Γ(T,⊤)] PullbackProfinite ...`
  is normalized on every finite-stage function by the same explicit equation
  as `Algebra.stonean_cover_second_stage`. Each restriction is a quotient of
  the coordinate ring, so this determines e on each product stage, hence on its
  colimit. The final p-equation says k is also over S_n, using the existing
  canonical `PullbackProfinite.projT` and the spectrum map of `e.symm`.
  These equations retain the canonical model, not just an arbitrary ring isomorphism.
- `g n : V_n.left ⟶ U_n.left` is over h by
  `g n ≫ U_n.hom = V_n.hom ≫ h`. The equation `p n (g n x) = q n x` makes its
  component map the identity under the specified component identifications.
  Together these specify the exact underlying map `(x',s) ↦ (h(x'),s)`;
  the stalk-isomorphism lifting theorem makes this map unique and canonical.
- The final equation for every arrow `f : m ⟶ n` of SimplexCategoryᵒᵖ gives
  compatibility of g with every face and degeneracy. The preceding equation
  over h gives compatibility with augmentation.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`;
  and the canonical affine `T.isoSpec`.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`,
  `WContractification.Restriction`, its real diagram of clopen idempotent
  localizations, `WContractification.PullbackProfinite` and `PullbackProfinite.projT`.
  Its import `WeilConjectures.RingTheory.ProEtale.WLocal` gives the recorded
  `IsWLocalRing` and `IsWStrictlyLocalRing`; the former uses `WLocalSpace` from
  `WeilConjectures.Topology.SpectralSpace.WLocal.Basic`.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`, used by the existing bundled
  `affineComponentSpace`; no second topology or profinite encoding is introduced.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its full morphisms,
  `ProEt.precoverage`, `ProEt.topology`.
- `Sheaf.Paper.ComponentRelativeProfiniteSite`: `affineComponentSpace` and
  `component_relative_profinite_site`, read in full with its universal-property,
  finite-stage and presentation-limit clauses. These specify which lift is meant.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `SimplicialObject`, its
  simplicial operators, δ and σ. The slice expresses augmentation.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`:
  `GrothendieckTopology.IsWeaklyContractible`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, occurring in
  the existing `Restriction` diagram; `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  `Localization.AtPrime`, occurring in the existing w-strict-locality definition.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, `Cocone`,
  `IsColimit`, with actual diagram data in `stoneanPartitionDiagram`.
- `Sheaf.RingTheory.StoneanCoverSecondStage`: `Algebra.stoneanPartitionDiagram`,
  `stoneanPartitionStage`, `stoneanPartitionMap`, `stonean_cover_second_stage`.
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`: `properFaceDiagram` and
  `ProperFaceCategory` with the exact proper-face matching equations.

The proper-face and Stonean partition diagrams are now cited through their new
definition-node owners, rather than the theorem nodes containing their Lean code.
The affine component bundle also has its own definition-node owner. The relative
component theorem remains a genuine statement dependency: the informal statement
explicitly names the inverse-limit relative lift, and the predicate specifies that
lift by its canonical pullback-space and stalk description. It remains a proof
dependency as well. No theorem-node helper is copied.

Proof-only imports retain every currently recorded usable proof-dependency module:
`FormalCoproduct` through the finite-basis hypercover module;
`Sheaf.Topology.StoneanCover`, `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`,
`Sheaf.Topology.FilteredSpectrumTopologicalLimit`,
`Sheaf.AlgebraicGeometry.AffineComponentSiteProjection`,
`Sheaf.AlgebraicGeometry.StalkIsomorphismLifting`,
`Sheaf.AlgebraicGeometry.ProEtale.Projective`, and the finite affine coproduct-spectrum
maps in `Mathlib.AlgebraicGeometry.Limits`. The relative-site and Stonean-ring modules
are public because their definitions occur in the signature. The four proof-only
nodes clopen-restriction-canonical-localization, partition-restriction-ind-zariski,
profinite-partition-incidence-limit, and relative-component-lift-pullback-space have
no recorded Lean module in this checkout, so none is invented or imported.

Edge cases checked before writing:

- P empty: X and X' are empty; S can be empty in every degree. The partition poset
  still contains the empty partition, whose product ring is zero. No Nonempty or
  Nontrivial binder occurs. The pro-etale matching conditions include this case.
- P a point: the conditions become Stonean covers of a point, and the relative
  lift has the original stalks. No finite or discrete restriction is imposed on P.
- h the identity: e is the identity and one may take identical lifts and identity g.
- Arbitrary h with component homeomorphism: no closed-point-preservation or
  isomorphism-on-stalks assumption on h is needed or imposed; only the lifted
  structure maps are required to be stalkwise isomorphisms.
- Degree zero: empty proper-face diagrams and the explicitly fixed terminal
  objects give precisely the base matching object and the augmentation cover.
- All face and degeneracy maps, not merely adjacent degrees, are quantified.
- The ring comparison is over both factors and normalized on every partition;
  a bare point bijection or bare algebra equivalence would not suffice here.

Sources opened: the complete relevant statements and proofs of Bhatt--Scholze
2.2.8, Example 2.4.6 and 2.4.8; HRS paragraph before (4.1) and Proposition 4.3;
Stacks `hypercovering.tex`, `lemma-hypercovering-object` (0DAV); the existing
`StoneanCoverSecondStage` module and its partition/refinement definitions.

Searches:

- `msearch.py ... leanfinder "Compatible weakly contractible pro-etale hypercovers
  from a common profinite component space"`: eight generic zero/one-hypercover
  results, no all-degree compatible common-component theorem.
- `msearch.py ... loogle '"Profinite", "Hypercover"'`: zero results.
- `msearch.py ... grep '(hypercover|Hypercover).*(component|Stonean)|
  ([Cc]omponent|Stonean).*(hypercover|Hypercover)'`: thirteen generic hits, including
  zero/one hypercovers and affine Zariski hypercovers; no exact statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item tag and
  common-component hypercover phrases: no existing declaration. Additional concept
  searches found the relative component functor, the actual Stonean partition ring
  model and the proper-face diagram, all reused rather than duplicated.

Validation: the required `scompile.py Q58 lem-sfb-wstrict-common-component-hypercovers`
compiled the delivered module against the published server library, both sandbox
and library modes, with no errors or unexpected warnings (3.4 s and 3.7 s).


## New nodes

`def-sfb-proper-face-diagram` owns the existing `properFaceProperty`,
`ProperFaceCategory`, `properFace`, and `properFaceDiagram` in
`Sheaf.CategoryTheory.ProperFaceMatchingObject`, with `existing: true`.
Stacks 0186, `lemma-formula-limit`, supplies the lower-simplex indexing description;
this definition restricts it to injective proper faces. Objects, commuting triangles,
the opposite variance and the distinguished codimension-one faces match the source.
The degree-zero index is empty. It asserts no matching comparison theorem.
`def-sfb-proper-face-matching-arrow` is different: it defines a predicate via boundary
products/multicospans, and owns none of these indexing definitions.

`def-sfb-stonean-partition-diagram` owns the existing `stoneanRestrictionMap`,
`stoneanPartitionStage`, `stoneanPartitionMap`, and `stoneanPartitionDiagram` in
`Sheaf.RingTheory.StoneanCoverSecondStage`, with `existing: true`.
Stacks 097C/097D, `lemma-construct` and `lemma-construct-profinite`, give the
clopen-neighbourhood localization colimit and finite-quotient construction.
The node states the restriction ring construction explicitly, then products,
refinement maps and their functor. `WContractification.Restriction` and its diagram
are the existing implementation in the public imported upstream WContractible
module; they are reused, not redefined. The definition works before any Stonean or
surjectivity assumptions. When S is compact its open equivalence classes give the
finite nonempty clopen parts. Empty S has its empty partition and zero product ring.

`def-sfb-affine-component-space` owns the existing `affineComponentSpace` in
`Sheaf.Paper.ComponentRelativeProfiniteSite`, with `existing: true`.
Stacks 0906, `lemma-spectral-pi0`, supplies exactly the profinite structure used by
this bundle. The carrier is literally `ConnectedComponents T` with its existing
quotient topology. This addresses the return's advisory ownership finding too.
No new functor or choice of relative lift is introduced.

For each notion, the new node records the actual LeanSearch, Loogle and Mathlib
grep queries and outputs from `searches.jsonl`. LeanSearch returned eight general
related declarations per query; Loogle returned zero for each exact name;
Mathlib grep returned zero for the two diagrams and one unrelated CompHaus
component-functor comment for the affine bundle. `rg` in upstream WeilConjectures
returned no matching declarations, while Sheaf contains exactly the reused helpers.
DAG definition-node searches found no owner; blueprint searches for `proper face`,
`partition` and `component space` found only the related finite-split-hypercover
and cover-construction statements, with no exact definition. The ancestor command
returns None, so the inherited null ancestor and full via chain are retained.

## Second reading by Q58

Self-check performed in this dispatcher session, with the node, saved Lean module,
three new definition records, and existing source definitions open; no other agent
was started. The independent maintainer review remains the delivery review.
The returned head's two theorem-node additions to stmt_deps have been replaced by
the definition-node owners, and affineComponentSpace now has a definition owner.
Current-main comparison shows only lean and these three additions to stmt_deps
change on the item; the two returned theorem nodes are not added. The existing
relative-component theorem is retained because the informal statement itself
uses its canonical relative lift, not just its helper bundle.

Re-read the hypotheses: both schemes affine and w-strictly local, arbitrary h,
component homeomorphism e with its pointwise identification he. Re-read every
conclusion: all-degree surjective Stonean hypercover, limiting proper-face cones
including degree zero, actual full ProEt covering arrows, affine w-contractible
and site-weakly-contractible terms, topology/stalk/component/closed-point clauses,
partition colimit with finite-stage normalization and both factor maps, and g
natural over h with identity component coordinate. They are unchanged from the
returned statement which the independent reviewer found mathematically correct.
The new nodes change ownership only; signatures match their existing sources
verbatim. Rechecked empty component base/empty partition, point base, h=id,
and degree zero. No extra nonemptiness, surjectivity of h or universe equality
was introduced. No theorem proof or definition body was changed.

Repair validation (2026-10-22): `scompile.py` compiled the delivered Lean module
in sandbox and library modes (3.4 s and 3.7 s), cleanly. The revised packet's
`deliver2.py --no-push` passed server preflight and compilation with all three
new existing-definition records (dry-run commit 187fea57685). The current-base
field comparison confirms only lean and the three new stmt_deps change on the
item. Its Lean source is unchanged from the independently reviewed statement.
