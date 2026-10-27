## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGlobalIdempotentClopen` states
`AlgebraicGeometry.AlgebraicSpace.global_idempotent_clopen`, with one `sorry`.
It also supplies `structureSectionsCommRing`, the pointwise commutative ring instance
on Mathlib's existing compatible sections of the recorded structure presheaf.
This is real instance data (`Subring.toCommRing`), with no postponed data or helper theorem.
No node statement, dependencies, proof plan, or other metadata is changed.

Source read: `literature/stacks-project/spaces-over-fields.tex`, lines 2429–2477,
Tag 0DMY proof (2), whose idempotent/decomposition paragraph uses no properness;
`spaces-properties.tex`, lines 473–520, Tag 03BZ, classifies open subspaces uniquely.
The module docstring includes the complete five-step proof plan, using the recorded
atlas equalizer, scheme correspondence, point calculus, and open-subspace classification.

Hypothesis and clause correspondence:

- A scheme S is `{S : Scheme.{u}}`; an arbitrary algebraic space over S is
  `(X : AlgebraicSpace S)`. Its small étale site and structure presheaf are the existing
  `X.EtaleSite` and `X.structurePresheaf`. No field, properness, quasi-compactness,
  Noetherian, reducedness, separatedness or nonempty hypothesis occurs.
- The atlas topology is the recorded `pointTopologicalSpace` instance on
  `Point X.obj.obj`; every `IsClosed` and `IsClopen` refers to exactly this topology.
- A = Gamma(X_et,O_X) is `RingCat.sectionsSubring X.structurePresheaf`.
  By its definition this is the ring of families in O_X(T) compatible with every
  arrow of the small étale site. This is the definition of global sections on a site
  without assuming a final scheme object. Its universe is u+1, as is the site object
  universe; no Small or artificial universe equality is assumed.
- Idempotents are `{e : ... // IsIdempotentElem e}`, where `IsIdempotentElem e` is
  exactly `e * e = e`. The asserted `∃ E : ... ≃ ...` is the bijection, with target
  `{U : OpenSubspace X // IsClosed (pointImage U.val.ι)}`.
- The first conjunct says every target point image is clopen. The second says every
  clopen C has exactly one `U : OpenSubspace X` with image C (`∃! U`). Together
  they express exactly the clopen images and the unique open-subspace structures.
- Every affine étale chart is quantified as `(B : CommRingCat.{u})`,
  `(p : Spec B ⟶ S)`, `(a : yoneda.obj (Over.mk p) ⟶ X.obj.obj)`, `(ha : IsEtale a)`.
  There is no surjectivity condition. The restriction of e is its family component
  at `op ⟨CostructuredArrow.mk a, ha⟩`; `Scheme.ΓSpecIso B` identifies that component
  with an element of B. The inverse image under `schemePointMap a` is the carrier
  of `PrimeSpectrum.basicOpen` of this element. Since the pullback is an open
  subspace, the unique open-subspace structure makes this point equality precisely
  the asserted equality with the principal-open pullback, not just an image condition.
- The inverse section is `E.symm U`. On EVERY scheme chart T, at EVERY point x,
  its germ is 1 if the image lies in U and 0 otherwise. Equality of sections is
  detected by chart germs, so this is exactly restriction to 1 on U and 0 on its
  complement, including non-affine charts. No arbitrary map replaces the inverse.
- `U_0 = empty` and `U_1 = X` are literal subfunctor equalities
  `(E 0).val.val = ⊥` and `(E 1).val.val = ⊤`.
- `U_(1-e) = X \ U_e` is the equality of the complementary point images, with
  Mathlib's `e.property.one_sub` supplying the idempotence proof. The uniqueness
  conjunct identifies it with the unique complementary open subspace.
- `U_(ef) = U_e intersect U_f` is literal subfunctor equality with `⊓`;
  `e.property.mul f.property` is the existing ring-theoretic idempotence proof.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.ΓSpecIso`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `EtaleSite`, `etaleForget`, `structurePresheaf`, and `structureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`; its upstream point classes and `schemePointMap` are reused.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- Proof imports follow all recorded proof dependencies: `SpaceCotangentRingMap`
  (publicly retaining the enlarged étale equalizer/localization model),
  `WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent`
  (`scheme_clopen_idempotent`), `AlgebraicSpacePointOpenCalculus`
  (`point_open_calculus`), `AlgebraicSpaceEtaleOpenImage`
  (`openSubspace_points_orderIso`, `etale_open_image`), and
  `Mathlib.RingTheory.Spectrum.Prime.Topology`
  (`existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `isIdempotentElemEquivClopens`). The spectrum node is a Mathlib leaf; its match
  rather than a nonexistent lean record is used.
- `Mathlib.Algebra.Category.Ring.Limits`: `RingCat.sectionsSubring`; the full
  definition was read. `Mathlib.Algebra.Ring.Idempotent` and its group prerequisites
  supply the existing idempotent predicates and zero/one/complement/product witnesses.

Edge cases checked mathematically before writing:

- Empty X: compatibility at the empty scheme and empty-cover sheaf condition give
  the zero ring, so 0=1 and there is one idempotent and one open subspace. All
  formulas agree; no Nontrivial or Nonempty instance is requested.
- Empty affine chart / zero ring B: both sides of the chart formula are empty.
- e=0, e=1, ef with a zero factor, and 1-e: the displayed Boolean formulas have
  the prescribed empty/full/complement/intersection interpretation.
- Spec(k[epsilon]/epsilon^2): nilpotents do not create idempotents; no reducedness
  hypothesis is required. A disconnected affine product gives its usual components.
- Infinite disjoint unions and non-quasi-separated algebraic spaces: global sections
  are unrestricted compatible families and the proof uses arbitrary atlases, with
  neither finite products nor a finite subcover imposed.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder: “Idempotent global regular functions on an algebraic space
  correspond bijectively to clopen open subspaces”: eight hits, all spectrum results,
  including `PrimeSpectrum.isIdempotentElemEquivClopens`; no algebraic-space result.
- msearch.py loogle: `"IsIdempotentElem", "Clopens"`: eleven spectrum hits,
  including the correspondence, complement and multiplication; no algebraic-space result.
- msearch.py leansearch: “Idempotent global sections of an algebraic space structure
  sheaf correspond bijectively to clopen subspaces”: eight spectrum hits, no general
  algebraic-space correspondence.
- msearch.py grep: `[Ii]dempotent.*[Cc]lopen|[Cc]lopen.*[Ii]dempotent|AlgebraicSpace`
  in Mathlib/AlgebraicGeometry: zero hits.
- rg in `lean/WeilConjectures` for idempotent/clopen patterns finds the scheme
  correspondence and categorical clopen projectors, not the algebraic-space result.
  `grep -rn 'lem-sfb-space-global-idempotent-clopen' lean/WeilConjectures` gives no hits.
- rg in `lean/Sheaf/AlgebraicGeometry` finds the recorded points and opens interfaces,
  references in Stein factorization, and its `steinGlobalFunctions` on the different
  small affine model. That existing small-model definition is not duplicated: the
  statement directly uses Mathlib's general compatible-family ring on the existing
  whole small étale site, without a new global-functions definition. Searches for
  `global_idempotent_clopen` and `structureSectionsCommRing` in both roots give no hits.

Validation: scompile.py compiled both the sandbox module and its library module
successfully, with no warnings. The initial affine formula required `.carrier`
explicitly, rather than relying on a coercion across the definitional spectrum
carrier equality; this was repaired without changing the mathematical statement.
No statement dispute or dependency repair was necessary.

## Second reading by Q48

A separate in-thread rereading opened the node and the final signature together.
No second agent was started, as the dispatcher explicitly prohibits it; the maintainer's
independent review remains the independent reading of this delivery.
The rereading checked the five named statement dependencies against the actual imported
notions. It checked the equivalence target includes closedness, every clopen has a
unique open subspace, the affine formula quantifies all (not only surjective) charts,
the inverse has both germ values on all scheme charts, and the four Boolean clauses
refer to the same E. The spectrum element uses ΓSpecIso.hom in the correct direction.
The main universe is explicit and the empty space is not excluded. The complement
point-image equality and chart inverse-image equality determine subspaces uniquely
by the explicit unique-open-structure clause. No mismatch was found in this rereading.
