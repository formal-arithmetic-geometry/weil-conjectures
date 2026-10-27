## Worker report

Module: `Sheaf.AlgebraicGeometry.CanonicalAffineEnvelopeDescentDatum`.
Main declaration: `AlgebraicGeometry.CanonicalAffineEnvelope.exists_descentDatum`.
All definitions have actual data; every theorem has only `sorry` as its proof.
The subsidiary theorems state the comparison and compatibility clauses of this same node,
not independent prerequisites. No statement correction, dependency replacement or new node.

Source read: `literature/stacks-project/descent.tex`, lemma-quasi-affine (Tag 0247),
second paragraph. It constructs the canonical quasi-compact open immersion into the affine
envelope, applies flat base change of the pushforward structure algebra, and transports
phi and its cocycle to the envelope. The node expands that argument on global sections.
No repair note exists for this item. The passed live review is of the stage-1 split;
the node has no live Lean binding, and the prior sandbox contained no delivered sources.

### Hypotheses and objects

- `A B V : Scheme.{u}`, `[IsAffine A] [IsAffine B]`, and `p : A ⟶ B` give the two affine
  schemes and their covering map. `[Flat p] [Surjective p]` are exactly flat and surjective.
  Using arbitrary affine schemes instead of writing A = Spec S retains the chosen scheme
  A; `A.isoSpec` is the canonical identification with Spec Gamma(A). The construction map
  is Spec of the actual section map, followed by this identification's inverse.
- `f : V ⟶ A` and `[IsQuasiAffineHom f]` use the dependency's recorded relative notion.
  Its source documentation defines quasi-affine schemes to be quasi-compact with canonical
  map an immersion (hence open). No finite-presentation, Noetherian or separation hypothesis
  is added. Quasi-separatedness of V is a conclusion.
- `D : Over.DescentDatum p (Over.mk f)` is exactly the recorded datum, with its full
  naturality, identity and cocycle fields, in the project's transport presentation.
- `Gamma(V, top)` is C, `Spec Gamma(V, top)` is W. `map f` is W to A and
  `unit f` has underlying map `V.toSpecΓ`, so j is the canonical adjunction unit,
  corresponding to the identity section map. `Over.w (unit f)` is j over A.

### Each conclusion and comparison clause

- The first four conjunctions of `exists_descentDatum` are `CompactSpace V`,
  `QuasiSeparatedSpace V`, `IsAffineHom (map f)` and `IsOpenImmersion V.toSpecΓ`.
  Together with the constructed `unit`, these are all of the first paragraph's conclusions.
- For any affine T and q : T to A, `comparison f q` is beta. Its domain is
  `pushout f.appTop q.appTop`, the tensor product of commutative rings, with the given
  structural maps. Mathlib's `CommRingCat.pushoutCoconeIsColimit` identifies this pushout
  with the ordinary algebra tensor product; using the universal presentation avoids any
  unrecorded choice of algebra structures. `comparison_apply` states c tensor t maps to
  the product of the two pulled-back sections. The product of `pushout.inl c` and
  `pushout.inr t` is the pure tensor under that identification.
- `baseChange` states that beta and `spectrumComparison` are isomorphisms for flat q.
  Specialize q to `pullback.fst p p` or `pullback.snd p p`: these are the p_i, their common
  source is A_2, and their pullbacks are exactly V_i and W_i. Both are flat as base changes
  of p, and A_2 is affine. No additional assumption is required for those specializations.
- `affineTensorMap` is the affine fibre-product identification with its two projections fixed
  by the tensor inclusions. `spectrumComparison_eq` states it is an isomorphism and that
  `spectrumComparison = Spec beta followed by affineTensorMap`. This fixes the requested
  alpha uniquely: `alpha f q` is the inverse of this precise spectrum comparison.
- `alpha_properties` says `unitBaseChange f q` followed by alpha is the canonical
  map `(pullback f q).toSpecΓ`. Its second clause says alpha inverse is over T.
  `unitBaseChange` is the pullback of the actual `unit f` using `Over.pullback`.
- `transition p (Over.mk f) D a b h` evaluates D on the universal point of the pullback
  along a and lifts the transported point over b. Thus on A_2, for a = p_0 and b = p_1,
  it is the morphism phi from the node. Its section map has direction E_1 to E_0.
  It is an isomorphism because D's identity and cocycle fields give its inverse by
  reversing a and b. It is an over-category morphism, hence is over the overlap base.
- `extendedTransition` is alpha_0.hom, then Spec of phi sharp, then alpha_1.inv.
  This is precisely the displayed psi, with Lean composition written in diagram order.
  The final universally quantified clause of `exists_descentDatum` identifies the induced
  E's transitions with that formula on every flat affine overlap, including A_2 and A_3.
- `E : Over.DescentDatum p (Over.mk (map f))` includes the full cocycle. Its
  `transport_transport` field evaluated on the three universal coordinates of A_3 gives
  psi_02 = psi_12 composed with psi_01, after the usual pullback identifications.
  The first quantified clause says transporting j(x) by E equals j of D's transport of x.
  By Yoneda this is exactly psi composed with j_0 = j_1 composed with phi, including
  all test schemes, not only affine points. The recorded transport notion is used directly;
  no private replacement for descent data or omitted cocycle obligation.
- `comparison_naturality` gives the ring-map equality for an over-base morphism e and
  any q. Specializing e to phi and q to each triple-overlap projection gives the asserted
  theta' lambda_1 = lambda_0 (theta tensor 1). `tensorMap` constructs theta tensor 1 by
  the pushout property, fixing the second ring factor.
- `comparison_successive` states the next comparison is an isomorphism and explicitly
  identifies the successive and direct comparisons on `(c tensor s) tensor t`.
  The right side is the pullback via the canonical pasting isomorphism of beta applied to
  `c tensor (r sharp(s) * t)`. Hence both sides are the product of the three pulled-back
  sections. Such generators generate the iterated tensor product, giving the full equality.
  Its affine and flat hypotheses hold for each A_3 to A_2 projection. The formula retains
  the actual maps and the canonical iterated-pullback identification.
- General q, e and flat affine overlaps in the comparison clauses express the naturality
  implicit in the node: their specializations supply both double and triple intersections.
  The supporting product and naturality equalities need no flatness, while the invertibility
  clauses require exactly flatness and the source qcqs obtained from quasi-affineness.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`, `Scheme.Hom.appTop` (full signatures and docstrings read).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `GammaSpec.adjunction`,
  `Scheme.toSpecΓ`, `Scheme.toSpecΓ_naturality`, the Hom bijection into Spec;
  `Scheme.preimage_basicOpen` in Scheme renders the dependency's other clause.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.isoSpec` and
  `Scheme.isoSpec_inv_naturality` for the canonical affine identification.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, its base-change instances and
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`; `pushoutSection` is the
  same canonical section-product map expressed using appLE at the top opens.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`: `IsQuasiAffineHom`.
- `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine`, its CompactSpace
  parent and canonical-unit open-immersion and separatedness instances.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum`,
  its transport and cocycle fields; its documentation explains the equivalence with the
  double- and triple-fibre-product presentation. `IsEffective` is not needed here.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`; `QuasiSeparatedSpace` is the
  scheme-conventions node's quasi-separated underlying-space predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`,
  `isAffineHom_of_isAffine`; `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, lift, and pushout with its two inclusions and desc.
- `Mathlib.AlgebraicGeometry.Pullbacks`: `pullbackSpecIso`, fixing both projections;
  `Mathlib.Algebra.Category.Ring.Constructions`: `CommRingCat.pushoutCoconeIsColimit`.
- Proof import `Sheaf.AlgebraicGeometry.QuasiAffineBaseChange`:
  `AlgebraicGeometry.isQuasiAffineHom_baseChange`, read with its complete signature and
  proof plan. Other proof dependencies are already supplied by the Mathlib imports above.

### Edge cases

V empty is allowed: C is the zero ring, W is empty, all units and comparisons have their
usual empty/zero-ring meanings and no Nonempty hypothesis is imposed. A = B = empty is
also allowed, with surjectivity interpreted on underlying points. V = A yields the standard
canonical affine comparison. The identity cover and identity overlap maps remain allowed.
Non-finitely-presented affine flat covers are allowed, since no finite-type or
finite-presentation hypothesis is present. All schemes have one arbitrary universe u;
Scheme.{u}'s section rings and test schemes have that same universe, so the pointwise
transport tests do not introduce a smaller universe or a vacuous class of test objects.

### Searches

- msearch.py leanfinder: "A descent datum on a quasi-affine scheme over a faithfully flat
  affine cover extends to the spectrum of global sections". Eight hits, including generic
  affine-property descent and open-immersion descent, but none stating this envelope datum.
- msearch.py loogle: `"toSpecΓ", "pullback"`. One hit,
  `Scheme.isPullback_toSpecΓ_toSpecΓ`; it concerns an affine morphism between quasi-affine
  schemes, not the envelope descent datum or its section comparisons.
- msearch.py grep: `toSpecΓ|affinization|affinis|affiniz`, subdirectory AlgebraicGeometry.
  Existing canonical-unit declarations found and reused; no complete theorem match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for those expressions and canonicalAffine,
  together with an exact item-id search, found no declaration of this item. Related files
  concern invariant opens, intersection embeddings or unrelated affinization comparisons.
- DAG name search found related `lem-a1-invariant-open-affinization-equivariance`,
  `lem-a1-quasi-affine-open-affinization-square`, and the qcqs relative affinization map;
  these do not state the given descent extension. No new independent notion was required.

Validation: the complete module compiled through scompile.py on the live server, separately
in the sandbox and library module name, with no errors or unexpected warnings. The expected
postponed theorem proofs are all covered by this node's comparison and descent clauses.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
