## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.isScheme_of_trait_closure_thickenings`
in `Sheaf.AlgebraicGeometry.TraitSpaceClosureThickeningsScheme`. Its only theorem proof is
`sorry`. There are no new definitions, new nodes, dependency repairs, or statement changes.
The accepted five-step split and every other existing node field are preserved.

The inherited BLOCKED ending concerned the already accepted stage-1 split, not this
stage-2 statement. The current live item has `status: split`, a Q50/L stage-1 review on
2026-10-24, and no `lean` record. The current queue lists it at stage 2. The explicit
2026-10-22 stage handoff in coord/brief-stage2.md §0 says to continue precisely in this
situation. There is no released repair note or N9 return entry for this item. The old
report mentioned in the inherited ending is absent from the retained stage-2 sandbox.

### Hypothesis and conclusion correspondence

- The commutative discrete valuation domain is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The class excludes fields and the zero ring.
- The uniformizer and its specified ideal are `(π : R)` and
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`. This is the definition of a
  generator in the dependency node, with no independent nonzero hypothesis.
- The base is literally `Spec (CommRingCat.of R)` everywhere; no arbitrary base scheme
  or unrecorded identification is introduced.
- `Y : AlgebraicSpace (Spec (CommRingCat.of R))` is the recorded full subcategory of
  big fppf sheaves with representable diagonal and a surjective étale scheme atlas.
- `hsep` applies the dependency's `IsRepresentableWith` to the diagonal
  `prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)`, using `IsClosedImmersion p.left` as the
  scheme-test property. Products of presheaves on schemes over S are relative products
  over S, so this is the relative diagonal required by the node.
- `hft` quantifies every scheme `U : Over S` and étale chart
  `a : yoneda.obj U ⟶ Y.obj.obj`, and asserts `LocallyOfFiniteType U.hom`.
  This is exactly local finite type on étale scheme charts; no quasi-compactness is
  conjoined. All scheme charts, including affine ones, have the base ring's universe.
- `C : ClosedSubspace Y` uses the recorded subobject definition. Its arrow
  `C.val.arrow` includes its full closed scheme structure and its representable
  closed-immersion property; it is not just a subset of points.
- `hclosure` quantifies every ring `B : CommRingCat.{u}`, every base ring map
  `φ : CommRingCat.of R ⟶ B`, and every representable étale chart
  `a : yoneda.obj (Over.mk (Spec.map φ)) ⟶ Y.obj.obj`.
  The existential `U,p,q` and `IsPullback q (yoneda.map p) C.val.arrow.hom.hom a`
  give its actual scheme base change of C. The latter is automatically a closed
  subscheme of Spec B by the recorded closed-subspace condition, hence affine.
  The equality
  `RingHom.ker (((Scheme.ΓSpecIso B).inv ≫ Scheme.Γ.map p.left.op).hom) =
  RingHom.ker (algebraMap B (Localization.Away (φ.hom π)))`
  says its defining ideal is exactly the kernel of B → B[1/φ(π)]. Here
  `ΓSpecIso.inv` identifies B with the regular functions on Spec B; `Γ.map` then
  restricts them to the closed pullback. For a closed immersion into an affine
  scheme this kernel determines the closed subscheme, including nilpotents. Thus
  the existential scheme test is exactly the closure characterization specified
  by the node, and adds no assumption beyond C being that closure.
- `hC` asserts that the presheaf of the chosen subobject C is isomorphic to the
  Yoneda presheaf of some `U : Over S`. This is representation by an S-scheme.
- `hthick` quantifies every `n : ℕ` with `1 ≤ n`. The ring map is literally
  `Ideal.Quotient.mk (Ideal.span {π ^ n})`, so its spectrum is S_n with its
  canonical S-map. The presheaf pullback of Y and its Yoneda presheaf over the
  terminal presheaf is the sheaf fibre product Y_n = Y ×_S S_n. Limits of sheaves
  are computed in presheaves, so representability of this presheaf is exactly
  representability of Y_n. Its representing scheme is again an object of Over S.
  Positive natural indices enumerate exactly the positive integer indices of
  the node; no n=0 assumption is used, and no common exponent is chosen.
- The conclusion `∃ U : Over S, Nonempty (Y.obj.obj ≅ yoneda.obj U)` is
  representation of Y by an S-scheme, including its structure morphism. An
  isomorphism of the underlying presheaves suffices because both are fppf sheaves.
  No group operations, flatness, global quasi-compactness, or affine-neighbourhood
  condition is imposed.

### Dependencies and source inspection

I read each statement dependency's entire statement and recorded declaration:

- def-sc-discrete-valuation-ring is a Mathlib leaf: `IsDiscreteValuationRing`,
  Mathlib.RingTheory.DiscreteValuationRing.Basic, with `[IsDomain R]`; its
  `irreducible_iff_uniformizer` confirms the chosen ideal-generator convention.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme; their definitions and signatures were read.
- def-trf-algebraic-space: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and `AlgebraicSpace.IsEtale`,
  Sheaf.AlgebraicGeometry.AlgebraicSpace. I read their scheme-test definitions,
  full-subcategory encoding, atlas condition, and docstrings.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, a closed embedding with
  surjective stalk maps. This module is publicly available through the recorded
  ClosedSubspace import.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, whose affine section-map
  condition was read; no quasi-compact part is used in the hypotheses.
- lem-trf-space-fibre-products-etale-covers:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme`,
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers; all three
  signatures and their proof docstrings were read. The fibre products here use
  the same categorical pullbacks, viewed on underlying presheaves.
- def-sfb-space-closed-subspace: `AlgebraicGeometry.AlgebraicSpace.ClosedSubspace`,
  Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace, read in full; in particular
  `C.val.arrow.hom.hom` is its actual inclusion, not a separately supplied map.

Mathlib's actual quotient, localization, Yoneda and global-section constructions
are used directly. I read `Scheme.ΓSpecIso : Γ(Spec B, ⊤) ≅ B`, and the displayed
normalization agrees with the normalization used in GammaSpecAdjunction.lean.

All already stated proof-dependency modules are imported privately as the stage
requires: AlgebraicSpaceEtaleOpenImage, AlgebraicSpaceMorphismProperties,
AlgebraicSpaceClosedIdealCorrespondence, AlgebraicSpaceOpenSubspace,
FerrandSchemePushout and AlgebraicSpacePointOpenCalculus. The DVR Mathlib leaf
is already a public import. The proof dependencies noetherian-coherent-acc,
qcoh-kernels-colimits, ferrand-pushout-space-agreement, closed-space-union-pushout,
and space-largest-schematic-open have no recorded Lean modules on the read base;
there is consequently no module for them to import. They remain explicitly
named in the theorem's five-step proof docstring. They are proof inputs, not
missing notions required to type the statement.

I read the current blueprint's direct-images proof, branch (3), and opened the
primary Anantharaman scan at
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf, printed pages 20–21.
The OCR calls Proposition 1.3.2 “1.5.2”; it gives representation from the generic
schematic closure and every infinitesimal special fibre and reduces locally to
a trait. The elementary reconstruction and local stabilization appear also in
§1.0 and §1.2.2(c). The item is the accepted separated trait specialization;
its statement and proof route need no correction.

### Edge cases

Empty Y and C are permitted, represented by the empty scheme, and all chart
conditions retain their ordinary meaning. On an empty affine chart B is the
zero ring: both kernels are the unique ideal, so no chart is improperly excluded.
The DVR assumptions exclude π=0 and unit π automatically. The first required
thickening is n=1; n=0 would be the empty quotient spectrum and is not requested.
If π acts invertibly on a chart, the localization kernel is zero and the closed
pullback is the entire chart. If it acts nilpotently, that kernel is the unit
ideal and the closed pullback is empty. In mixed horizontal/vertical charts the
full kernel ideal, rather than a reduced support, is used. Arbitrarily many open
charts and unbounded local torsion exponents are allowed. Scheme and chart
universes are explicitly bound by u, matching the recorded size convention.
There are no auto-bound variables, hollow definitions, or disputed statements.

### Searches for an existing statement

The prescribed msearch.py calls are preserved verbatim in searches.jsonl:

- LeanFinder: “An algebraic space over a discrete valuation ring is a scheme if
  its schematic generic closure and all infinitesimal special fibres are
  schemes” returned eight hits about schemes, integral/Artinian properties and
  valuative criteria; none states this representability criterion.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, Localization.Away` returned zero
  hits, reporting AlgebraicGeometry.AlgebraicSpace unknown to the Mathlib index.
- Mathlib grep: `AlgebraicSpace|schematicClosure|closure.*thicken`, subdirectory
  AlgebraicGeometry, returned zero hits.
- LeanSearch: “An algebraic space is a scheme if its generic schematic closure
  and infinitesimal special fibres over a discrete valuation ring are schemes”
  returned eight hits about definitions of schemes, affine schemes and locally
  ringed spaces; none is the criterion.
- Local rg of WeilConjectures for `schematicClosure|closure.*[Tt]hicken|trait.*[Ss]cheme`
  found trait-normalization lemmas about already given schemes and one unrelated
  open-immersion comment; searching the item id found no declaration.
- Local rg of Sheaf for the closure/thickening and ClosedSubspace terminology
  found the existing schematic-closure and closed-ideal correspondence APIs.
  Their source was read: they construct or characterize a closure, and do not
  assert schematicity from that closure and infinitesimal fibres. No matching
  theorem or duplicate notion was found.

### Validation

Every delivered Lean file is checked using the prescribed server scompile.py;
the required deliver2.py dry run and direct delivery follow. No shared source,
project Git state, global build, or launcher tool is edited by the worker.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
