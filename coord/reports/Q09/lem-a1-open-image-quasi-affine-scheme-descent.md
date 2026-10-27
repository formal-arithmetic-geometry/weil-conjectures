## Worker report

The module `Sheaf.AlgebraicGeometry.OpenImageQuasiAffineSchemeDescent` states
`AlgebraicGeometry.AlgebraicSpace.openImageQuasiAffineSchemeDescent`, with `sorry`.
No mathematical theorem is proved. The auxiliary `openImageSectionPresheaf` has real data:
it composes Mathlib's `OverPresheafAux.restrictedYonedaObj` with the canonical scheme-test
functor obtained from `Over.iteratedSliceBackward` and `Functor.toCostructuredArrow`.
Thus its values are the existing `OverPresheafAux.OverArrows`, not a new definition of
relative morphisms. Its naturality proof is exactly Yoneda functoriality applied to `Over.w`.
No data are chosen from a postponed existence theorem.

Source read: `literature/stacks-project/spaces-morphisms.tex`, Tag 03XW,
`lemma-neighbourhood-scheme`, lines 10470–10586, particularly the final paragraph.
Earlier separatedness and local quasi-finiteness in that proof establish the quasi-affine
hypothesis already assumed by this node; they are not extra assumptions here.
The node is unchanged except for its Lean record and adding two already-landed definition
nodes to `stmt_deps`: `def-a1-space-open-subspace` and `def-a1-space-point-topology`.
They own the exact notions used, previously written inline in the item's prose.
No new nodes or dependency modules are needed. No statement correction or dispute is needed.

Hypothesis-by-hypothesis correspondence:

- A scheme S is `{S : Scheme.{u}}`. Arbitrary universe u is explicit and autoImplicit is false.
- Affine S-schemes T and T' are `(T T' : Over S)` with `[IsAffine T.left]` and
  `[IsAffine T'.left]`. The S-morphism a is `(a : T' ⟶ T)` and its etaleness is
  `[Etale a.left]`. These use the dependency's recorded Mathlib class, without an added
  finiteness, surjectivity or affineness hypothesis on a beyond the stated affine objects.
- X is `(X : AlgebraicSpace S)` and its morphism to T is the natural transformation
  `(f : X.obj.obj ⟶ yoneda.obj T)`.
- W is `(W : OpenSubspace X)`, the existing subfunctor with inclusion representable by
  open immersions on every scheme base change. `W.val.ι` is that inclusion and
  `W.val.toFunctor` is the actual underlying W functor. Its algebraic-space property
  follows from the existing notion; no unrelated sheaf is substituted for W.
- The open scheme B and inclusion are `(B : Over S) (j : B ⟶ T)` with
  `[IsOpenImmersion j.left]`. This is the usual presentation-independent encoding of
  an open subscheme. `hB` says exactly that its point image equals the image of a.
  There is no `[IsAffine B.left]` hypothesis.
- `pointImage` uses the existing `Point` quotient of field-valued representatives by
  the common-extension relation. The scheme Yoneda maps give the corresponding point
  images, so `hB` matches the scheme's ordinary image and `hW` is the required image
  containment for W to T. No sectionwise surjectivity is substituted for point images.
- A representing scheme for P is `(P : Over S)` with structure map `(v : P ⟶ T')`
  and its map to W `(q : yoneda.obj P ⟶ W.val.toFunctor)`. `hP` is the Cartesian square
  with bottom arrows W to T and a. This is precisely representation of W times_T T',
  retaining both projections. `[IsQuasiAffineHom v.left]` is the exact recorded
  relative quasi-affineness notion: affine target opens have quasi-affine preimages.

Conclusion-by-conclusion correspondence:

- Existential b and `b ≫ yoneda.map j = W.val.ι ≫ f` factor W to T through B.
- Existential p and `p ≫ j = a` give the induced scheme map T' to B.
- `IsAffineHom p.left`, `Surjective p.left`, and `Etale p.left` state all three
  scheme-morphism properties, using the library classes.
- The two `Presieve.singleton p.left` memberships state separately that p is an fpqc
  covering and an fppf covering, using `Scheme.fpqcPrecoverage` and `fppfPrecoverage`.
- `IsPullback q (yoneda.map v) b (yoneda.map p)` identifies the same P with W times_B T'.
- `Presheaf.IsSheaf (Scheme.fppfTopology.over B.left) (openImageSectionPresheaf B b)`
  is the sheaf condition for exactly the specified functor on B-schemes.
  At Q to B the functor is the fibre of W(Q to S) over its fixed map Q to B;
  restrictions are the actual W restrictions. By Yoneda this is Mor_B(Q,W).
- `Nonempty (((Over.map p.left).op ⋙ openImageSectionPresheaf B b).RepresentableBy
  (Over.mk v.left))` says its pullback to T' is represented by that P over T'.
- The existential `D : Over.DescentDatum p.left (Over.mk v.left)` is the dependency's
  actual scheme descent datum. Its transport starts above the first base coordinate
  and lands above the second. The displayed iff, for all Q over S and all m0,m1 into P
  with equal B-coordinate, says its transport sends m0 to m1 exactly when their q-images
  (their W-sections) agree. Therefore it is the canonical comparison retaining w,t0,t1,
  rather than an arbitrary effective datum on a locally isomorphic object. Every point
  in this characterization is over S automatically: its T'-coordinate determines that
  structure. Conversely any scheme test used in the descent datum has this S-structure.
- `D.transport_transport`, a field of the recorded structure, is precisely
  phi02 = phi12 composed with phi01. `transport_self` and naturality give the canonical
  overlap isomorphism and its inverse. Its direction agrees with the node's ordered
  coordinates. No independent cocycle proposition is necessary: the structure contains it.
- `D.IsEffective` asserts effectivity of this very coordinate-preserving datum, with a
  global scheme, a Cartesian square and compatibility of all transports.
- `(openImageSectionPresheaf B b).IsRepresentable` asserts a B-scheme represents the
  specified W-sheaf itself. This is not merely existence of an unrelated scheme with
  isomorphic local fibres.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom` (including docstrings).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (the record's current class).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`; the universal
  property is expressed by `IsPullback`, retaining the specified representation maps.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`: `IsQuasiAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `fpqcPrecoverage`, `fppfPrecoverage`,
  `fppfTopology`, and the covering inclusion used by the proof plan.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum`,
  `transport`, `transport_transport`, `IsEffective`, and the canonical transport documentation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`; its imported
  `AlgebraicSpacePointClasses` defines `Point`, `PointRepresentative`, and their relation.
- `Mathlib.CategoryTheory.Comma.Presheaf.Basic`: `OverPresheafAux.restrictedYonedaObj`,
  `OverArrows`, and `MakesOverArrow`; these supply the helper's entire relative-map data.

The stated proof dependencies are imported privately: `EnlargedEtaleRingedSite`
(schemeSpace), `FppfSheafRepresentabilityDescentData`, `QuasiAffineFpqcDescent`, and
Mathlib's morphism permanence modules. The proof dependency
`lem-a1-space-open-factor-scheme-tests` has no recorded module in the read snapshot,
so there is no import to add for it. It is not needed to type the statement.
The quoted fppf sheaf descent theorem uses Type (u+1); a proof can apply it to the
canonical ULift of this Type u valued functor. The statement itself imposes no universe
equality or stronger condition to fit that proof API.

Edge cases checked before writing and on the final statement:

- T' empty: B is the empty open, image containment forces W empty, and the singleton
  map to the empty scheme is a covering. No `Nonempty`, nonzero ring or point is assumed.
- W empty, with nonempty B: P is empty, its morphism is quasi-affine, and the empty
  scheme represents the specified sheaf. The sheaf still has its unique section on
  an empty test, so it has not been replaced by a constantly empty presheaf.
- Non-surjective a: p is surjective onto B only, as required; a is not assumed surjective.
- Non-affine B: permitted, for example an affine etale cover of D(x) union D(y) in
  an affine plane obtained from the disjoint union of those two affine opens.
- Non-quasi-compact W globally: no global compactness assumption is added. Only the
  hypothesized relative quasi-affineness of P over T' appears.
- All schemes use the algebraic-space framework's arbitrary universe u; no field
  characteristic, noetherian, separated, finite-type or nonempty condition is added.

Searches actually run through msearch.py (2026-10-24; sandbox searches.jsonl):

- LeanFinder: "An algebraic space whose pullback to an affine etale chart is quasi affine
  is a scheme over the open image of the chart". Eight hits: absolute quasi-affineness,
  open immersions and affine properties, no exact statement.
- Loogle: "IsQuasiAffineHom, DescentDatum". Zero hits; the service reports the upstream
  identifier IsQuasiAffineHom unknown, so this is not evidence that the upstream lacks it.
  The upstream declaration was found and read directly.
- grep of Mathlib/AlgebraicGeometry: "AlgebraicSpace|quasi.affine.*descent|descent.*quasi.affine".
  Zero hits.
- LeanSearch: "The sheaf of maps to an algebraic space is representable if its pullback
  along an fpqc cover is a quasi affine scheme". Eight hits, including Zariski local
  representability and affine morphism properties; none is the stated descent theorem.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for open images and
  quasi-affine descent found the existing quasi-affine effectivity tool and other
  statements for etale or separated locally quasi-finite objects, not this full claim.
  Direct grep of the item id in `lean/WeilConjectures` found no declaration.
- Focused searches for field-point classes, point images, open subspaces and descent
  data found the exact existing notions listed above. Searches for relative presheaves
  led to Mathlib's `OverPresheafAux.restrictedYonedaObj`, reused directly.
- Full declaration names `openImageQuasiAffineSchemeDescent` and the chosen helper
  were checked against project/upstream sources; no collision found.

Validation: the required server wrapper compiled both the sandbox and named module
successfully. Initial compiler probes exposed an unqualified namespace reference to
`restrictedYonedaObj`; it was corrected to `OverPresheafAux.restrictedYonedaObj`.
Final import changes are checked again by the delivery dry run. Only the expected
postponed theorem proof remains.

## Second reading by Q09

This is a second pass by the same dispatched worker; the brief forbids starting another
agent, and the maintainer supplies the independent review. I reopened the node, source
paragraph, final module and dependency declarations. I checked each binder and conjunct
against the correspondences above. The use of an arbitrary open immersion j, instead of
an element of T.Opens, is presentation-independent and does not assert B affine.
The actual hP and its repeated Cartesian square over B keep the same P and both maps.
The map-presheaf helper reuses Mathlib rather than redefining relative morphisms.
The descent iff is essential: omitting it would assert only existence of some effective
structure and would lose the node's canonical comparison. It is present, and the cocycle
is in the existing structure with the required composition direction. Effectivity and
representability both concern that W. No node statement was changed. The second pass
added the already-landed open-subspace and point-image definition nodes to stmt_deps
and made the statement dependency imports public. No remaining mismatch was found.
