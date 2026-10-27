## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceZariskiAfterAdmissibleBlowup` states
`AlgebraicGeometry.AlgebraicSpace.exists_openImmersion_blowups_of_isIso_over_open`.
Its sole theorem has proof `by sorry`; there are no new definitions or helper axioms.
The statement is unchanged. The node gains three already-landed definition dependencies:
`def-sfb-space-quasi-coherent-ideal`, `def-sfb-space-blowup-presentation`, and
`def-sfb-space-absolute-quasi-separated`. These name the existing notions actually used,
rather than introducing copies or modifying the scheme-only blowup dependency.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `X T U XU : AlgebraicSpace S` use the
  recorded fppf-sheaf algebraic spaces. The single explicitly bound universe `u`
  follows their established size convention, with site objects in `u+1` and module
  sections in `u`. `autoImplicit` is disabled.
- The morphism is `f : X ⟶ T`. Its separatedness is `hfsep : MapIsSeparated f`,
  the recorded closed-immersion scheme-test predicate for its diagonal. Its finite
  type is `hfft : MapIsFiniteType f`, the recorded quasi-compactness plus chartwise
  locally finite-type predicate.
- Quasi-compactness of T is `hTqc`, an existential surjective representable etale
  atlas `a : yoneda.obj V ⟶ T.obj.obj` with `CompactSpace V.left`.
- Absolute quasi-separatedness of T is `hTqs : IsAbsolutelyQuasiSeparated T`,
  using the landed affine-test criterion, not relative separatedness over S.
- The open subspace is presented by `j : U ⟶ T` and `hj`, exactly
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`.
- Quasi-compactness of U is `hUqc`, the same surjective etale atlas criterion for U.
- The inverse image `X ×_T U` is an arbitrary cartesian representative `XU`, with
  projections `q : XU ⟶ X`, `fU : XU ⟶ U`, and `hU : IsPullback q fU f j`.
  Its projection is an isomorphism by `hfU : IsIso fU`. Specifying a cartesian
  representative adds no hypothesis; the category has these sheaf fibre products.
- The output ideal is `I : QuasiCoherentIdeal T`. This is the existing subobject
  of the structure module with Mathlib's quasi-coherence predicate.
  `(I.val : T.Modules).IsFiniteType` means local finite generation.
- `IsIso (idealTensorMap j I)` says the canonical tensor pullback of its inclusion
  is an isomorphism to O_U: precisely I restricted to U is the unit ideal, with
  its embedding specified, not merely an abstract isomorphism of modules.
- The extended centre is `J : QuasiCoherentIdeal X`, specified by the existential
  epi `e` and `e ≫ J.val.arrow = idealTensorMap f I`. Since `J.val.arrow` is a
  subobject inclusion, this epi-mono factorization pins J to the image of the
  canonical tensor map. No arbitrary centre on X is substituted.
- `B : BlowupPresentation I` and `C : BlowupPresentation J` carry actual algebraic
  spaces and blowup projections. Their chart conditions identify them over every
  affine etale chart with the ordinary scheme blowup in the restricted ideal.
  Thus they express the node's descended Rees Proj up to isomorphism over its base.
- `v : C.space ⟶ B.space` is representable by scheme open immersions, using the
  same `IsRepresentableWith` predicate as hj.
- `v ≫ B.projection = C.projection ≫ f` is exactly b_T v = f b_X in Lean's
  diagrammatic composition convention.
- `IsPullback lT (𝟙 U) B.projection j` identifies the ENTIRE inverse image of U
  in the base blowup with U, with its canonical projection. Likewise
  `IsPullback lX (𝟙 XU) C.projection q` identifies the inverse image of XU in the
  source blowup with XU. The latter equals its inverse image of U by hU.
  `lX ≫ v = fU ≫ lT` identifies the restricted map with fU. Since hfU identifies
  XU with U, this is exactly the identity under the canonical identifications.
- There are no density, properness, Noetherian, reducedness, or finite-presentation
  hypotheses. The doubled-origin paragraph in the node explains why the retained
  separatedness assumption matters; it is not an additional quantified conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `Modules` and
  `structureSheaf`. These are the recorded spaces, representable chart tests,
  small etale structure sheaf, and its module sheaves.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  through the recorded separatedness predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`
  and `MapIsFiniteType` with their full chart-test definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  Mathlib predicate `SheafOfModules.IsQuasicoherent`, used by QuasiCoherentIdeal.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`:
  `QuasiCoherentIdeal`, `idealTensorMap`; the latter uses the landed canonical
  `moduleTensorPullback` and `moduleTensorAdjunction`, not an arbitrary map.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`: `BlowupPresentation`
  and its `blowupChartIdeal`, which uses
  `WeilConjectures.Blowup.Gluing`'s `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- Local finite generation is the existing `SheafOfModules.IsFiniteType` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`.

The already-stated proof dependencies are imported privately:
`AlgebraicSpaceQcOpenBoundaryIdeal.exists_finiteType_ideal_boundary`,
`AlgebraicSpaceStrictTransformAsBlowup.strictTransform_as_blowup`,
`SpaceFlatteningByAdmissibleBlowup.exists_flat_finitePresentation_spaceStrictTransform_admissibleBlowup`,
and `AlgebraicSpaceCompositionCentresTransforms.exists_blowupPresentation_comp_centres_strictTransforms`
(the declaration namespace in each case is `AlgebraicGeometry.AlgebraicSpace`).
Their source signatures and docstrings were read. The proof dependencies
`lem-sfb-space-blowup-chart-properties` and `lem-sfb-space-flat-isomorphism-dense-open`
have no Lean record at preparation time, so there is no module to import yet.
Their statements are retained in the proof docstring. They are proof prerequisites,
not missing notions needed to type this statement.

Source and edge-case checks:

Read `spaces-more-morphisms.tex`, lemma-zariski-after-blowup (087F),
`flat.tex`, lemma-zariski-after-blowup (081S), and `spaces-divisors.tex`,
lemma-strict-transform (0864(1)). The space source omits separatedness;
the reviewed node already correctly retains it, as the scheme source does.
The current blueprint unit proof's compactification paragraph was also read.
No statement correction is needed and no dispute remains.

For U empty, I=0 is allowed and the blowups can be empty; no density is imposed.
For U=T and f an isomorphism, I=O_T gives the identity blowups and v=f;
all restriction equations have the required orientation. Empty T forces empty X
and is permitted. Nonreduced spaces and zero-divisor centres are included by the
actual chart blowups; there is no Cartier hypothesis on I. An arbitrary base S
need not be quasi-separated: the absolute quasi-separatedness predicate for T
is retained. The doubled-origin morphism is excluded precisely by hfsep, not
by an extra injectivity or density condition.

Searches performed on 2026-10-24:

- `msearch.py ... leanfinder`: "A separated finite type morphism of algebraic
  spaces is an isomorphism over a quasi compact open and becomes an open immersion
  after admissible blowup". Eight hits, including scheme separatedness and
  preimmersion declarations; none is the space blowup theorem.
- `msearch.py ... leansearch`: "Zariski main theorem for algebraic spaces after
  an admissible blowup whose strict transform is an open immersion". Eight hits,
  chiefly `Algebra.ZariskisMainProperty` and scheme local-property transport;
  none states this theorem.
- `msearch.py ... loogle '"strictTransform"'`: zero hits.
- `msearch.py ... grep 'zariski.*blow|strict.?transform|admissible.?blow'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Zariski/blowup,
  admissibleBlowup and strictTransform found the upstream scheme-only
  `exists_admissibleBlowup_isOpenImmersion_strictTransformMap` in
  `WeilConjectures.Compactification.EliminationOfIndeterminacy` (read its full
  signature). It quantifies over schemes, so is not this algebraic-space theorem.
  The item-id search in `lean/WeilConjectures` has no hits; in `lean/Sheaf` it
  appears as a proof citation in CommonAdmissibleBlowups, not as a declaration.
- `rg` of the proposed declaration name in Mathlib, upstream, Sheaf, and
  `dag/lean_names_upstream.json`: zero hits. Existing ideal, blowup-presentation,
  and absolute quasi-separatedness nodes and modules were found and reused.

Validation: scompile.py compiled the delivered module in both sandbox mode (1.8s)
and library mode (1.6s), with no errors or warnings. No direct compilation or
Git mutation was run in the read-only clone.

## Second reading by Q41

A fresh self-reading was performed with the node and module open; this is not
an independent-worker review (the dispatcher explicitly forbids starting agents).
The maintainer's independent review remains the independent reading.
Checked each hypothesis and output clause against the mapping above. In particular:
absolute rather than relative quasi-separatedness, the canonical image factorization,
the base projection equation, and both full inverse-image cartesian squares are
present. The restriction equation involves the given isomorphism fU, so it really
becomes the identity on U and is not an arbitrary automorphism. No added hypotheses
or strengthened conclusions were found. No changes were required by this reading.
