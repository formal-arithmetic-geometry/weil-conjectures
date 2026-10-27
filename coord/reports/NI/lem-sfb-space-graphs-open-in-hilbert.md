## Worker report

Stage 2, group NI, 2026-10-24. The main module is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceGraphsOpenInHilbert`, declaration
`AlgebraicGeometry.AlgebraicSpace.space_graphs_open_in_hilbert`.
Source read directly: `literature/stacks-project/quot.tex`, lines 3140--3208,
Tags 0D1A and 0D1B, including the preceding definition of Mor. The current
blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read; this is a supporting graph-Hilbert lemma, not the unit statement.
The item's source, statement and six-step proof remain unchanged.

Hypotheses and clauses, individually matched:

- S a scheme: `{S : Scheme.{u}}`; Z,W,B algebraic spaces over S:
  `{Z W B : AlgebraicSpace S}`, `z : Z ⟶ B`, `w : W ⟶ B`. Universes are explicit,
  autoImplicit is false. Scheme tests are the existing `SchemeTests B.obj.obj`.
- Z proper: `hz_proper : MapIsProper z`; flat: `hz_flat : MapIsFlat z`.
  Finite presentation has exactly its three constituents: `hz_lfp`, `hz_qc`,
  `hz_qs`, respectively `MapIsLocallyOfFinitePresentation z`,
  `MapIsQuasiCompact z.hom.hom`, and quasi-compactness of its sheaf diagonal.
- W separated: `hw_separated : MapIsSeparated w`. There is no lfp, qc, qs,
  properness or flatness hypothesis on W.
- The existing `MapIsLocally` chart tests render scheme flatness and local finite
  presentation; `MapIsProper` expands to separated, finite type and universally
  closed. Existing `MapIsQuasiCompact` uses affine tests of the underlying
  algebraic-space point topology. These are the same interfaces used by the
  landed flat/proper/fp permanence theorem.
- Z_T and W_T: `relativeSpace z T` and `relativeSpace w T`, actual sheaf pullbacks
  bundled using `enlargedFibreProduct`. Ordering T ×_B Z instead of Z ×_B T is
  the canonical symmetry of the same fibre product, not a restriction.
- The morphism values are `RelativeMorphism z w T`: maps Z_T → W over B.
  The fibre-product universal property identifies them with Hom_T(Z_T,W_T),
  including for empty and nonrepresentable algebraic spaces.
- H(T): `SpaceHilbertFamily (relativeProductMap z w) T`. Its closed-subspace
  inclusion is the existing `ClosedSubspace` arrow. The five explicit conjuncts
  are proper, flat, locally finitely presented, quasi-compact and quasi-separated
  for D → T. Subobjects identify isomorphic presentations over the ambient space.
- The existential M,H and value equivalences eM,eH specify these exact presheaves.
  The first conjunct fixes the morphism transition map to precomposition with
  `relativeSpaceMap z h`; the second fixes H transitions by an actual `IsPullback`
  square of closed immersions. This is the inverse-image transition, not an
  arbitrary action on the family values. Functor identity/composition laws and
  naturality of γ are built into `Functor` and `NatTrans`.
- The graph γ: `∃ γ : M ⟶ H`. Its graph normalization conjunct supplies an
  isomorphism from the chosen family representative to Z_T whose composite with
  the actual `relativeSpaceGraph` is the family's inclusion. Thus it is the
  precise closed graph subobject; its closedness follows from the family type.
- Injectivity: `∀ T, Function.Injective (γ.app (op T))`.
- Image iff invertible projection: `(∃ f, γ.app (op T) f = D) ↔ IsIso (eH T D).first`.
- Unique recovery: for every isomorphism e with `e.hom = (eH T D).first`, the
  `∃! f` clause requires graph(f)=D and `(eM T f).val = e.inv ≫ (eH T D).second`.
  `.second` is the projection composed to W; together with the T component this
  is exactly the stated map to W_T. It does not discard any information.
- The open V_D is `∃ (V : SchemeTests B.obj.obj) (j : V ⟶ T),
  IsOpenImmersion j.left.left`. Such a map identifies V with an open subscheme
  of T. Every map T'→T is quantified, including identity and nonflat maps.
- The universal criterion is `IsIso (eH T' (H.map h.op D)).first ↔
  ∃ a : T' ⟶ V, a ≫ j = h`. It is about the actual pulled-back closed family.
- The final `β` and `IsPullback β (uliftYoneda.map j) γ
  (uliftYonedaEquiv.symm D)` give the claimed natural identification
  h_T ×_H Mor ≅ h_V over h_T. Type (u+1) accommodates the actual closed-subobject
  type. `uliftYoneda.{u+1}` changes only representation of morphism sets by ULift,
  not the test category or morphisms. No universe equality or smallness restriction
  on the allowed test schemes is imposed.

Dependencies read and used (names below are in `AlgebraicGeometry` or
`AlgebraicGeometry.AlgebraicSpace`, as appropriate):

- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom; Morphisms.Flat: Flat;
  Morphisms.FinitePresentation: LocallyOfFinitePresentation;
  Morphisms.ClosedImmersion: IsClosedImmersion;
  Morphisms.FiniteType and Morphisms.QuasiCompact: LocallyOfFiniteType, QuasiCompact;
  Morphisms.Proper and Morphisms.UniversallyClosed: IsProper, IsSeparated,
  UniversallyClosed; OpenImmersion: IsOpenImmersion. Their full definition
  signatures and docstrings were read. These are also the scheme properties used
  by the inherited space chart and representability tests.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  IsAlgebraicSpace; AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace and the two etale-cover clauses.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: schemeSpace,
  enlargedFibreProduct, enlargedFibreProductFst. These are recorded in the existing
  enlarged-etale-model node (whose expanded interface is now also reexported by
  SpaceCotangentRingMap). The owning definitions were read at their source.
- Sheaf.TraceFormula.SpaceLinePresentationDefs: SchemeTests. Search found this
  existing category abbreviation, so no duplicate scheme-test definition remains.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace: ClosedSubspace;
  AlgebraicSpaceMorphismProperties: MapIsLocally, MapIsFlat,
  MapIsLocallyOfFinitePresentation, MapIsSeparated, MapIsProper and their underlying
  finite-type/universal-closed predicates; ProperCurveModuli: MapIsQuasiCompact.
- Proof imports: AlgebraicSpaceFlatProperFpLocality.flat_proper_fp_locality and
  AlgebraicSpaceUniversalIsomorphismOpen.exists_openSubspace_universal_isomorphism.
  Their full signatures and docstrings were read. The separated-composition node
  currently has no Lean record, so its import is absent. It is a proof prerequisite,
  not needed to type this statement; no version of that theorem is fabricated.
- Mathlib CategoryTheory: CostructuredArrow, Subobject, pullback.map/lift,
  IsPullback, Functor, NatTrans, Equiv, uliftYoneda, uliftYonedaEquiv.

Edge cases checked before writing and on rereading: Z empty (only the empty graph,
open locus all T); T empty; W empty with Z nonempty (no morphisms, an empty family
can still be a Hilbert value, graph locus the open where Z_T is empty); Z=W=B=Spec k
(Hilbert families are clopen subspaces, with graph locus D); identity base change;
arbitrary composite and nonflat base changes; nilpotent structures (closed
subobjects, not point subsets); no restriction on characteristic, dimension, or
finite presentation of W. Invertibility is genuine sheaf-map invertibility, not
bijectivity on points.

Searches: msearch.py leanfinder queried the graph-open-in-Hilbert statement and
relative-morphism/Hilbert-family notions (hits: scheme gluing, affine spaces,
scheme ideal sheaves, no general-space match); leansearch queried proper flat
finitely presented closed subspaces and relative morphisms (scheme proper/flat
properties only); loogle `Subfunctor, CategoryTheory.Subobject` gave no match,
`"Hilbert"` gave analytic Hilbert-space declarations; msearch grep
`HilbertFunctor|hilbertFunctor|HilbertFamily|graphs.*[Oo]pen` in AlgebraicGeometry
returned zero. Further grep of `SpaceHilbertFamily|HilbertFunctor|hilbertFunctor|
RelativeMorphism|SchemeTest` found unrelated simplicial relative morphisms in
Mathlib. rg of the live WeilConjectures and Sheaf sources found the scheme-only
ProperHilbertPresheaf, RelativeMorphismsPresheaf and GraphsOpenInHilbert,
fixed-degree Hilbert.Defs, and the reused SchemeTests and ClosedSubspace.
The item-id search in WeilConjectures gave no match. DAG searches and
blueprint_refs.py searches confirmed the scheme-only/fixed-degree distinction.
The two new nodes carry the actual msearch outputs and the local-search findings.

Validation: all three modules compiled individually and in dependency order via
scompile.py against the live published build. Compiler-guided adjustments were
limited to definitional reductions in the canonical pullback maps and line width.
The only postponed theorem is the item's named theorem, with `by sorry` and the
complete six-step natural-language proof in its docstring. Both added modules
contain real definition data and no postponed theorem.

No statement correction, no disputed statement, and no dependency repair.

## New nodes

`def-sfb-space-relative-morphism-values`, module
Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeMorphisms: relative morphism values,
canonical base-change maps, the ambient relative product and actual graph and
projection maps for general algebraic spaces. Source is the paragraph before
0D1A and 0D1A--0D1B. The scheme-only relativeMorphismsPresheaf does not cover this
notion. Existing SchemeTests and bundled sheaf pullbacks are reused. The node's
search records include LeanSearch, LeanFinder, Loogle, Mathlib grep, project grep,
DAG grep and blueprint searches. All helper declarations are recorded.

`def-sfb-space-hilbert-family-values`, module
Sheaf.AlgebraicGeometry.AlgebraicSpaceHilbertFamily: exact Hilbert-family value
types for arbitrary space morphisms, their underlying closed-subobject
representatives and inclusions, and the two graph projections. Source is the
Hilbert definition and 0D1A--0D1B. Existing scheme-only proper Hilbert functor and
fixed-degree finite Hilbert functor do not apply. Reuses ClosedSubspace and
MapIsProper/Flat/LocallyOfFinitePresentation/QuasiCompact, with no copy of those
notions. Searches are recorded as for the first new node.

## Second reading by NI

A second in-thread reading opened the item, both added definition nodes and all
three Lean modules after the clean compilation. No other agent was started, as
the dispatcher brief explicitly prohibits that; this is an author rereading,
not a claim of independent review. The maintainer supplies independent review.

The rereading found an existing SchemeTests abbreviation in
SpaceLinePresentationDefs: the initially drafted singular abbreviation was
removed, and every binder now uses the existing declaration. It also checked
that the Hilbert values are closed subobjects (isomorphic presentations identified),
that the transition condition is a cartesian square rather than an arbitrary
bijection, that the graph equality is over the ambient space, and that every
hypothesis and conclusion has the corresponding clause listed above.
The isomorphism-recovery clause uses the second projection to W, equivalent to
W_T when paired with the already fixed T projection. The lifted Yoneda square
expresses natural representability, with the same open V as the universal
first-projection criterion. W has exactly the separatedness hypothesis. No
mismatch with the unchanged source statement remains. The author rereading
makes no claim that the missing stage-3 proofs have been supplied.
