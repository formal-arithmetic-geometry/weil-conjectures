## Worker report

The new module `Sheaf.AlgebraicGeometry.SpacePartialSectionSchematicImage` states
`AlgebraicGeometry.AlgebraicSpace.partialSection_schematicImage`, with the sole proof
`sorry`. It defines no new data or predicates. The natural-language node statement,
proof, and proof dependencies are unchanged. Two already-landed definition nodes are
added to `stmt_deps`: `def-sfb-space-closed-subspace` and
`def-sfb-presheaf-map-separated-diagonal`. Their existing declarations are used directly.
No new node, dependency repair, or statement correction is needed.

The source was read in `literature/stacks-project/spaces-morphisms.tex`,
lemma-scheme-theoretic-image-of-partial-section (0CP3),
lemma-scheme-theoretic-image (082X), and
lemma-quasi-compact-scheme-theoretic-image (082Z), including their proofs. The blueprint
unit and its direct-images proof were read in `literature/blueprint/latest/blueprint/`.
The node is a geometric prerequisite, not the unit's own assertion.

Every hypothesis and conclusion is rendered as follows:

- Base scheme and universes: `{S : Scheme.{u}}`, with explicitly declared `universe u`.
  This is the universe-polymorphic model of the existing algebraic-space interface;
  the size-convention node is metatheoretic and introduces no additional Lean object.
- Algebraic spaces over S: `(B Y O : AlgebraicSpace S)`. This is the recorded full
  subcategory of fppf sheaves; its maps are natural transformations. The source O is
  an arbitrary algebraic space, and is not assumed to be a scheme or affine.
- Morphism f: `(f : B ⟶ Y)`.
- Separatedness: `(hsep : IsSeparatedPresheafMap f.hom.hom)`. Its recorded definition
  tests the canonical relative diagonal by `IsRepresentableWith` closed immersions.
- Open immersion: `(a : O ⟶ Y)` and
  `hopen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) a.hom.hom`.
  This tests representability and the existing scheme open-immersion predicate.
- Quasi-compactness of a: `hqc : IsRepresentableWith
  (fun _ _ p ↦ QuasiCompact p.left) a.hom.hom`. This uses the scheme predicate, not an
  arbitrary substitute or a global quasi-compactness assumption on O. For a
  representable map it is exactly the node's affine-test condition: restricting a
  test T to each affine open V identifies the inverse image with the affine test
  pullback. Those sources are quasi-compact by the node's assumption, which is the
  affine-local criterion for `QuasiCompact` of the representing scheme projection.
  Conversely, on affine T a quasi-compact scheme projection has quasi-compact source.
  Representations are unique up to isomorphism, so the existential representative in
  `IsRepresentableWith` does not change the condition. In particular this neither
  adds global compactness of O nor excludes non-quasi-compact Y.
- Partial section: `(s : O ⟶ B)` and `(hs : s ≫ f = a)`.
- Closed subspace and factorization: `∃ (C : ClosedSubspace B)
  (t : O ⟶ (C.val : AlgebraicSpace S)), t ≫ C.val.arrow = s ∧ ...`.
  `ClosedSubspace` already includes the closed-immersion property on scheme tests.
  Its underlying subobject supplies both the source space and its inclusion.
- Smallest such closed subspace: for every `D : ClosedSubspace B`, an existential
  factorization `v ≫ D.val.arrow = s` implies `C.val ≤ D.val`. This is inclusion of
  subobjects with their full scheme structures, not inclusion of point supports.
- Restriction of f i to O: the sheaf fibre product is
  `Limits.pullback (C.val.arrow ≫ f).hom a.hom`; its canonical morphism to O is
  `Limits.pullback.snd (C.val.arrow ≫ f).hom a.hom`. These are sheaf pullbacks, not
  an unprovided pullback instance on the full subcategory of algebraic spaces.
  Closure as an algebraic space is supplied by the recorded fibre-product theorem.
- Isomorphism and its specified inverse: the existential `e` is an isomorphism from
  that sheaf pullback to `O.obj`. The equation `e.hom = pullback.snd ...` identifies
  the morphism in the node, rather than asserting an unrelated abstract isomorphism.
  The equation `e.inv ≫ pullback.fst ... = t.hom` fixes the first component of its
  inverse. The second component is the identity because
  `e.inv ≫ pullback.snd ... = e.inv ≫ e.hom = 𝟙 _`. By the pullback universal
  property its inverse is therefore precisely the induced map `(t,id_O)`.
- There are no Noetherian, finite-type, reducedness, properness, nonemptiness,
  global compactness, or scheme-representability assumptions on B, Y, or O.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; read their full signatures and docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `IsAlgebraicSpace`. Its sheaf, atlas and
  representable diagonal definitions were read, including the full-subcategory model.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`. These are the scheme predicates in test projections.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicGeometry.AlgebraicSpace.diagonalPresheafMap` and
  `AlgebraicGeometry.AlgebraicSpace.IsSeparatedPresheafMap`, owned by the landed
  definition node `def-sfb-presheaf-map-separated-diagonal`. The theorem of etale
  locality is not assumed as a statement hypothesis.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`:
  `AlgebraicGeometry.AlgebraicSpace.ClosedSubspace`, owned by the landed
  `def-sfb-space-closed-subspace`; source Tag 03MB.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`; the full signature
  and proof docstring give closure and the sheaf-pullback universal property.

The module has plain proof imports for the recorded, available proof dependencies:
`AlgebraicSpaceQuasiCoherentModule` (`QCoh`),
`AlgebraicSpaceQuasiCoherentPushforward`
(`isQuasicoherent_moduleDirectImage_of_quasiCompact_separated`),
`AlgebraicSpaceIdealClosedSubspaceCorrespondence` (`ideal_closedSubspace_correspondence`),
and `AlgebraicSpaceEtaleModulePushforwardRestriction`
(`etale_module_pushforward_restriction`). Their signatures and proof docstrings were
read. The closed/open-immersion and fibre-product proof dependencies are already public
imports because the statement uses them. At reading time the proof-only nodes
`lem-sfb-space-qc-cancellation`, `lem-sfb-qc-space-affine-etale-atlas`, and
`lem-sfb-space-qcoh-kernels-colimits` had no Lean record. No imports are invented for
these; their uses remain explicit in the theorem's six-step proof docstring.

Edge cases checked before drafting:

- O empty: its smallest closed subspace is empty, and both sides of the restriction
  isomorphism are empty. No nonemptiness assumption appears.
- O = Y and a the identity: s is a section of the separated morphism, hence closed;
  its image is s(O), and the projection to O is the asserted isomorphism.
- f the identity: the result is schematic closure of a quasi-compact open, whose
  restriction back to that open is unchanged.
- Nonreduced spaces: `ClosedSubspace` and its order retain the ideal/scheme structure;
  replacing the image by topological or reduced closure was explicitly avoided.
- Non-quasi-compact Y and O: a quasi-compact open immersion need not have globally
  quasi-compact source. Only quasi-compact scheme-test projections are assumed.
- Arbitrary base scheme and characteristic: no hidden field, Noetherian, or finite-type
  binder is introduced, and no extra universe variable makes tests vacuous.

Searches made (via the prescribed `msearch.py Q52 <item>` unless otherwise stated):

- LeanFinder: "Scheme theoretic image of a partial section of a separated morphism
  of algebraic spaces is an isomorphism over a quasi compact open". Eight hits included
  `Scheme.Hom.isoImage`, `IsClosedImmersion.instIsIsoSchemeToImage`,
  `IsImmersion.instIsOpenImmersionToImageOfQuasiCompact`, `Scheme.Hom.image`,
  `Scheme.instQuasiCompactToImage`, `Scheme.Hom.toImage`, `specTargetImageFactorization`,
  and `Scheme.Hom.isoOpensRange`. They concern schemes or open/closed images, not the
  assertion for algebraic spaces. Their returned signatures were inspected.
- Loogle: "AlgebraicGeometry.Scheme.Hom.toImage, AlgebraicGeometry.IsSeparated";
  successful search, zero hits.
- LeanSearch: "Scheme theoretic image of a partial section of a separated algebraic
  space morphism". Eight hits on scheme image constructions and partial rational
  maps, none on algebraic spaces or the full partial-section assertion.
- Mathlib grep: `partial.section|schematic.image` in `AlgebraicGeometry`; zero hits.
- Direct `rg -n 'partial.section|schematic.image' lean/WeilConjectures`: scheme-level
  partial-section graph/image material in Mathlib/AlgebraicGeometry/Pullbacks.lean
  and OpenImmersion.lean, plus compactification uses. The relevant declarations
  `partialSectionRestrictIso`, `isPullback_toImage_partialSection`, and
  `isIso_restrict_imageι_comp_fst` were read; they are for schemes and specific
  projections X times_S Y, so do not state the algebraic-space result.
- `rg -n 'lem-sfb-space-partial-section-schematic-image' lean/WeilConjectures`: no hits.
- Direct `rg` in `lean/Sheaf` found downstream proof-docstring references but no
  declaration of this result. Searches for `IsRepresentableWith`,
  `IsSeparatedPresheafMap`, `IsQuasiCompactPresheafMap`, and closed subspaces found
  the existing interfaces used here. No new notion had to be supplied.
- The chosen full name was checked with `rg` in Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json`: no existing declaration with that name.

Validation: `scompile.py Q52 lem-sfb-space-partial-section-schematic-image <module>`
passed in both sandbox and library module modes, with no errors or unexpected warnings.
All variables are bound explicitly (`set_option autoImplicit false`). The only postponed
proof is the theorem named above, matching this DAG node. Its docstring includes every
step of the accepted natural-language proof. No STATEMENT-DISPUTED issue was found.

## Second reading by Q52

I reopened the node and the completed Lean file for a separate second pass. This is
this dispatcher's worker's own second reading; the maintainer's independent review
remains separate, as the brief specifies, and no other agent was started.

The base and all three spaces are arbitrary, the separatedness hypothesis is exactly
the recorded closed-diagonal predicate, and a is an arbitrary representable open
immersion with the stated quasi-compactness. I checked specifically that the scheme
`QuasiCompact` test formulation is equivalent to quasi-compact source on affine tests,
and does not assume O itself globally compact. The factorization t has domain the same
O as s. Minimality quantifies over every closed subobject of B admitting a factorization
of that same s. The pullback cospan is the composite C to B to Y and the given a, and
e.hom is exactly its second projection. Reading the inverse equation together with
e.inv_hom_id shows its components are t and the identity of O; thus it is the requested
canonical inverse, not merely some isomorphism. The chosen subobject presentations do
not weaken the closed-subfunctor or minimality assertions. No clause is missing.

The second pass found no mathematical mismatch. I made the scheme dependency an
explicit public import and tidied the theorem docstring. Only the item's `lean` field
and the two justified additions to `stmt_deps` are changed; every added dependency
already has its declaration on the base. There are no definition bodies to audit for
hollowness, no private or local notation, and no proofs other than the single `sorry`.
