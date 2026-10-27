## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceChowDenseModification` states
`AlgebraicGeometry.AlgebraicSpace.exists_chow_dense_modification`. Its sole theorem
has proof `sorry`; there are no new definitions or helper theorems.

I read Stacks `spaces-more-morphisms.tex`, Tag 088U
(`lemma-chow-noetherian-separated`), the preceding 088S/088R construction, and
Tag 08BE (`theorem-grothendieck-existence`), especially the paragraph applying Chow's
lemma. The last explicitly supplies a scheme, a representable proper surjection,
isomorphism over a dense open, and H-quasi-projectivity over A. The statement is
unchanged. The source's reverse immersion factorization (open then closed) is
written explicitly; the generic immersion convention of def-weil-closed-immersion
is not silently substituted for it.

Hypothesis and conclusion correspondence:

- Arbitrary scheme S: `{S : Scheme.{u}}`; arbitrary commutative Noetherian ring A:
  `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- The specified map Spec A to S is the binder `a : Spec (.of A) ⟶ S`.
  The algebraic space over S is `X : AlgebraicSpace S`; its given map to Spec A
  is `f : X ⟶ schemeSpace (Over.mk a)`.
- Separated and finite type are exactly `hsep : MapIsSeparated f` and
  `hft : MapIsFiniteType f`, with their existing chart/diagonal/topological meanings.
- The scheme V with its S-structure is `V : Over S`. Its A-structure is
  `b : V ⟶ Over.mk a`. The source of q is the actual representable algebraic
  space `schemeSpace V`, not an unrelated presentation.
- Noetherian V is `IsNoetherian V.left`: Mathlib defines this as locally
  Noetherian and quasi-compact. Its existing
  `IsLocallyNoetherian.quasiSeparatedSpace` instance supplies quasi-separatedness.
  This is the node's equivalent three-part convention for a scheme; locally
  Noetherian schemes have locally Noetherian etale scheme charts by the existing
  locally-finite-type permanence result. No stronger property is substituted.
- `q : schemeSpace V ⟶ X` is representable, proper and surjective via the three
  conjuncts `IsRepresentable q.hom.hom`, `MapIsProper q`, and
  `IsSurjective q.hom.hom`. The last is representable scheme-test surjectivity,
  exactly surjectivity for this representable map. Its compatibility over A is
  `(q ≫ f).hom.hom = yoneda.map b`; b already commutes with the S-structures.
- `U : OpenSubspace X` is the existing open subfunctor, so its inclusion is
  representable by scheme open immersions. `Dense (pointImage U.val.ι)` means its
  image is dense in the existing field-point atlas topology of X.
- The actual inverse image is `pullback q.hom.hom U.val.ι`; the induced map to U
  is its second projection. `IsIso (pullback.snd q.hom.hom U.val.ι)` is exactly
  the entire inverse image mapping isomorphically to U, rather than a chosen
  smaller open of V or a mere abstract isomorphism.
- The integer r >= 0 is `r : ℕ`. Projective r-space over A is
  `ProjectiveSpace (ULift.{u} (Fin (r + 1))) (Spec (.of A))`; the coordinate type
  has r+1 elements and the lift changes only its universe.
- e is the displayed scheme map into that projective space. The witnesses
  `W : Scheme.{u}`, `j : V.left ⟶ W`, `i : W ⟶ ProjectiveSpace ...`, with
  `IsOpenImmersion j`, `IsClosedImmersion i` and `j ≫ i = e`, give precisely
  the node's open-then-closed factorization. Giving W its composite structure
  map `i ≫ (ProjectiveSpace ... ↘ Spec (.of A))` makes both factors A-maps:
  `e ≫ (ProjectiveSpace ... ↘ Spec (.of A)) = b.left` and the factorization
  give the required identity for j as well. Thus there is no lost A-linearity.
- No reducedness, irreducibility or flatness assumption occurs. The ringed-site
  module and functor sentence fixes background conventions; it introduces no
  module or additional geometric hypothesis. Their recorded modules are imported.
- Universe u is explicit on schemes, A, and all constructions; point classes
  retain the existing universe u+1 and the same atlas topology. No independent
  test-scheme universe or extra universe equality is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentable`, `IsRepresentableWith`, `IsSurjective`; these use actual
  presheaf pullback squares over all scheme tests.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsProper` and their defining
  diagonal, chart, quasi-compactness and universal-closedness interfaces.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`,
  `IsNoetherian`, `IsLocallyNoetherian.quasiSeparatedSpace`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`
  and `ProjectiveSpace.over`, using exactly the recorded base-change model.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- Existing background conventions:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`, `QCoh`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`,
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`.
  The metatheoretic size convention is rendered by explicit universe binders.
- Existing definitions additionally cited in stmt_deps, as authorized by brief
  stage 2 section 5: `def-trf-scheme-algebraic-space` owns `schemeSpace` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`;
  `def-a1-space-open-subspace` owns `OpenSubspace` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`;
  `def-a1-space-point-topology` owns `pointImage` and `pointTopologicalSpace` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`. Their node statements,
  records and exact declaration bodies were read. They are already landed, so
  no new node or duplicate construction is needed.

The module imports recorded proof dependencies: ProjectiveAffineBaseBlowup,
SpaceFiniteTypeComposition, the relative affine/projective chart module, and
Mathlib affine, quasi-compact, quasi-separated and Noetherian geometry.
The two proof-only nodes lem-sfb-space-dense-affine-immersion and
lem-sfb-space-blowup-embedding-extension have no Lean record in the read base;
they are described in the theorem's five-step proof docstring and need no object
or extra hypothesis in this theorem's statement. Their nonexistent modules are
not imported. The full proof plan remains unchanged.

Edge cases checked before writing: A is allowed to be the zero ring; X and V
may be empty, with U empty and dense in the empty point space. Neither
`Nonempty` nor a positive coordinate-dimension assumption is used. For r=0,
Fin (r+1) has one homogeneous coordinate and gives P^0, not the empty projective
scheme. Nonreduced or reducible X is admitted; a dense open is topological,
not an added schematic-density hypothesis. No flatness or integral-source
condition enters any binder. The inverse-image-isomorphism clause covers the
whole inverse image and hence cannot ignore extra components above U.

Searches actually run:

- msearch leanfinder, query `Chow lemma separated finite type algebraic space
  proper surjective quasi-projective scheme modification dense open`: eight
  scheme properness/separatedness/projective-spectrum hits, no space theorem.
- msearch loogle, query `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsClosedImmersion`:
  two matches, `IsClosedImmersion.iff_isProper_and_mono` and
  `IsClosedImmersion.eq_proper_inf_monomorphisms`. Neither states Chow's lemma.
- msearch grep, query `Chow|AlgebraicSpace|quasiProjective`, subdirectory
  `AlgebraicGeometry`: zero hits in Mathlib.
- msearch leansearch, query `Chow lemma dense open proper surjection from a scheme
  to a separated finite type algebraic space`: eight hits, namely scheme
  properness, scheme isomorphisms, dominant maps and their closed-image criterion;
  none supplies the requested algebraic-space modification.
- rg in lean/WeilConjectures and lean/Sheaf for Chow/chow and dense modification,
  plus the exact node id and proposed declaration name: upstream ChowLemma is
  scheme-only; Sheaf ChowFactorization is also scheme-only; SpaceDerivedChowNeighbourhood
  states the different derived local-neighbourhood theorem (0CTR). The exact
  item id and proposed name had no existing declaration. The scheme theorem's
  source signature was read, rather than treating its name as a space result.
- rg in the project for schemeSpace, OpenSubspace, pointImage, MapIsProper,
  ProjectiveSpace and matching node records found and reused the declarations
  above; no private counterpart is supplied.

No statement fault or dispute was found. Only lean and the three additions of
existing definition nodes to stmt_deps change. No new node or dependency module
is delivered. The source repository remains read-only; all edits are in this
item's sandbox. Compilation uses scompile.py only.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
