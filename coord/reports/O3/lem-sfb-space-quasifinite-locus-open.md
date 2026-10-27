## Worker report

Item: lem-sfb-space-quasifinite-locus-open. The delivery states the node in
Sheaf.AlgebraicGeometry.SpaceQuasiFiniteLocusOpen. There is one real predicate definition,
AlgebraicGeometry.AlgebraicSpace.MapToSchemeQuasiFiniteAt, spelling out the pointwise notion
introduced explicitly by this node, and one theorem with whole proof `sorry`,
AlgebraicGeometry.AlgebraicSpace.isOpen_mapToSchemeQuasiFiniteAt. No theorem is proved and
no construction has postponed data. Source read: literature/stacks-project/spaces-morphisms.tex,
lemma-locally-finite-type-quasi-finite-part (Tag 04NW), lines 6887–6903. The node is its
scheme-target form; the chart argument is the expanded proof already recorded on the node.

Hypothesis and clause correspondence:

- Schemes and universes: `{S : Scheme.{u}} (T : Over S)` use the existing Scheme and
  explicitly bound universe u. Here S is an ambient base and the node's target scheme
  is T.left. The node's algebraic space is `(E : AlgebraicSpace S)` and its structure
  map to the target is `(h : E.obj.obj ⟶ yoneda.obj T)`. These are natural transformations
  between the original fppf sheaf presheaves. An E with such a map is a space over T.left.
  This is the usual fixed-site rendering, also used by SpaceLqfAtlasRefinement; no property
  is imposed on the ambient base. Taking ambient base equal to the node's target and
  T the identity object includes every E over that target.
- The finite-type hypothesis is
  `(hft : MapToSchemeIsLocally (@LocallyOfFiniteType) E T h)`. Unfolding the recorded
  helper gives exactly `∀ U a, IsEtale a → LocallyOfFiniteType
  (yoneda.preimage (a ≫ h)).left`, the node's every-chart test, with no global
  quasi-compactness, separation, flatness or Noetherian assumption.
- The node's definition of quasi-finite at x is the actual body of
  `MapToSchemeQuasiFiniteAt h x`: for every scheme `U : Over S`, every
  `a : yoneda.obj U ⟶ F` with `IsEtale a`, and every `z : U.left` with
  `schemePointMap a z = x`, the scheme composite satisfies
  `Scheme.Hom.IsQuasiFiniteAtPoint (yoneda.preimage (a ≫ h)).left z`.
  IsEtale already includes representability. This uses pqf-def-quasifinite directly,
  including its finite-type requirement; it does not substitute Mathlib's weaker
  stalk-map-only QuasiFiniteAt. The helper is defined for arbitrary presheaf F solely
  so the same predicate applies literally to the chosen sheaf fibre product.
- The underlying point space is the existing `Point E.obj.obj` with the existing
  `pointTopologicalSpace` instance. The first conclusion is precisely
  `IsOpen {x : Point E.obj.obj | MapToSchemeQuasiFiniteAt h x}`.
- The open-subspace clause is `∃ J : OpenSubspace E, pointImage J.val.ι = ...`.
  OpenSubspace is the already recorded subtype of subfunctors whose inclusion is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)`. Thus its inclusion is
  an open immersion on every scheme test, exactly as required. Its point image is
  exactly Q_h, rather than merely contained in Q_h.
- For base change the quantifiers are `∀ (T' : Over S) (b : T' ⟶ T)`.
  These cover every scheme morphism B → T.left: give B the structure morphism
  B → T.left → S, obtaining an object of Over S and the corresponding arrow to T.
  In particular there is no restriction that b be flat, surjective, or finite type.
  The presheaf underlying the sheaf fibre product is `Limits.pullback h (yoneda.map b)`.
  Its source projection is `Limits.pullback.fst h (yoneda.map b)` and the base-changed
  map is its second projection. The existing `mapPoint` of the first projection pulls
  back Q_h, and the last equality identifies that inverse image exactly with
  `{x | MapToSchemeQuasiFiniteAt (Limits.pullback.snd h (yoneda.map b)) x}`.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.IsEtale, IsRepresentableWith, IsAlgebraicSpace. Full signatures and
  docstrings were read, including the actual scheme-test pullback witnesses and atlas.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion. The actual declarations,
  including the all-affine-pairs finite-type condition, were read.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointTopologicalSpace,
  pointImage. Also read AlgebraicSpacePointClasses: Point, PointRepresentative,
  schemePointMap, including the field-extension equivalence and residue-field map.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback, etale_fibreProduct_isScheme.
  The chosen presheaf pullback expresses the underlying sheaf pullback, since
  limits of sheaves are computed on the underlying presheaves.
- WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism:
  Scheme.Hom.IsQuasiFiniteAtPoint (used in the helper) and IsLocallyQuasiFinite
  (used by the proof inputs). Read their full affine-witness definitions/docstrings.
- Added already landed statement dependency def-a1-space-open-subspace for
  Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace.OpenSubspace, and
  def-sfb-proper-curve-moduli for Sheaf.AlgebraicGeometry.ProperCurveModuli:
  AlgebraicSpace.mapPoint and MapToSchemeIsLocally. Their full definitions were read.
  No replacement definition, dependency module, or new node is needed.

Proof-only imports follow the recorded proof plan: IsLocallyQuasiFiniteEtaleSource
(isLocallyQuasiFinite_etale_source), SpaceInvariantOpenQuotient
(space_invariant_open_quotient), SpaceLqfAtlasRefinement (space_lqf_atlas_refinement),
AlgebraicSpacePointOpenCalculus (point_open_calculus), QuasiFiniteLocusOpen
(Scheme.Hom.isOpen_quasiFiniteAtPoint), and Mathlib.AlgebraicGeometry.Morphisms.Etale
(the restriction instance of lem-a1-etale-open-restriction). Their module sources and
statement docstrings were read. Mathlib's FiniteType import also supplies the base-change
instance for lem-weil-pbc-lft-base-change. The proof dependency
lem-sfb-scheme-quasifinite-at-base-change currently has neither a Lean module nor a
mathlib_match, so there is no module of it to import; it remains explicitly named in
the proof docstring and the unchanged DAG proof plan. It supplies no object needed to
type the present statement.

Edge cases checked before writing:

- Empty E gives empty Q_h and the empty open subspace; after any base change the same
  equality of empty sets is required. No Nonempty assumption or chosen atlas is bound.
- A chart with no points over a given x contributes the correct vacuous implication;
  algebraic-space atlases ensure the all-chart condition has actual lifts for every x.
- For an étale map or finite map, every point is quasi-finite, so the locus is the
  whole source and the conclusion includes identity base change.
- A positive-dimensional affine space over a field has empty quasi-finite locus;
  a disjoint union with a finite component has precisely that finite open component.
  Thus the statement does not assert local quasi-finiteness everywhere.
- Empty T', arbitrary field extensions, and nonflat base changes remain in the last
  quantifier. There is no independent smaller test-scheme universe and no field,
  characteristic, connectedness or compactness restriction.

Searches for an existing statement/notion (2026-10-24):

- msearch.py leanfinder, query "For a locally finite type morphism of algebraic spaces
  the quasi-finite locus is open and commutes with arbitrary base change": eight hits,
  including scheme LocallyQuasiFinite and its stability/multiplicativity instances;
  no algebraic-space pointwise openness and exact locus base-change statement.
- msearch.py loogle, query "AlgebraicGeometry.LocallyQuasiFinite, IsOpen": zero hits.
- msearch.py leansearch, query "The quasi-finite locus of a locally finite type map
  of algebraic spaces is open": eight scheme/ring quasi-finite declarations, no match.
- msearch.py grep in AlgebraicGeometry, query
  `[Qq]uasi[Ff]inite.*[Ll]ocus|[Ll]ocus.*[Qq]uasi[Ff]inite|algebraic.?space`:
  five hits in Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean, notably
  Scheme.Hom.quasiFiniteLocus, mem_quasiFiniteLocus and its normalization open-immersion
  lemma. These concern schemes and do not replace the algebraic-space statement.
- rg of lean/WeilConjectures for the node id found no declaration. Topic searches
  for QuasiFinite, quasiFiniteLocus, and quasi-finite locus in WeilConjectures and Sheaf
  found the recorded scheme notions, the proof inputs, and SpaceFieldDiscretenessCriterion.
  Targeted searches of Space*.lean/AlgebraicSpace*.lean found no existing pointwise
  predicate or quasi-finite-locus theorem. ProperCurveModuli supplies the reused general
  chartwise local-property and point-map helpers. The upstream-name index has no
  matching algebraic-space locus declaration. All msearch results are also recorded
  by the launcher in this sandbox's searches.jsonl.

Validation: scompile.py O3 lem-sfb-space-quasifinite-locus-open compiled both its sandbox
probe and the module at its final library name cleanly (15.6 s and 1.7 s). No errors or
warnings. Only the named theorem has a postponed proof. No statement correction,
STATEMENT-DISPUTED flag, or node fault was found. The item changes only lean and gains
those two already landed statement dependencies; its statement and proof plan stay intact.

## Second reading by O3

A separate pass over the actual node and final file rechecked the universal chart and
lift quantifiers in the predicate, the single chartwise finite-type hypothesis, the
openness conclusion, exact point-image equality for the existing OpenSubspace, and
exact equality after every scheme base change. The first projection is used for the
inverse-image point map and the second for the new structure map, in the correct order.
The source is allowed to be an algebraic space throughout. The scheme predicate retains
finite type; no finiteness or separation assumption was introduced. The ambient-base
Over encoding covers every map into the target scheme, as explained above. The helper
has real definitional data and its two uses refer to precisely the same condition.
No mismatch was found and no changes were needed in this pass. This pass was performed
by this dispatched worker in-session; no independent worker was spawned, as the launcher
brief expressly prohibits starting other agents. The maintainer's independent delivery
review remains the independent reading specified by this dispatch.
