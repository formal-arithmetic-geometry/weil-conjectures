## Worker report

The statement is `AlgebraicGeometry.minimalVolumeModel_smooth_baseChange` in
`Sheaf.AlgebraicGeometry.MinimalVolumeModelSmoothBaseChange`. Its sole proof is `by sorry`.
`Sheaf.AlgebraicGeometry.TraitVolumeModels`, attached to the new definition node
`def-sfb-trait-volume-models`, supplies explicit geometric predicates; it has no postponed
proofs, choices from existence assertions, axioms, arbitrary comparison maps or abstract
model interfaces. All declarations bind universes and variables explicitly with
`set_option autoImplicit false`. Both delivered modules compile individually through
scompile.py against the published live project, with no warnings other than the expected
postponed-proof warning (suppressed by the server).

The original node statement and proof plan are unchanged. In particular the already
corrected final clause says that the removed subset is contained in the special fibre.
The only additional statement dependency is the new definition node. No recorded
statement dependency needs a replacement module.

Source read: BLR, Néron Models, 4.3, printed pp.103–106, especially the order paragraph
before Lemma 1, Proposition 2 and Lemma 3; also the opening shrinking operation of
Proposition 4. The primary scan was opened directly at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The latest blueprint's sec-six-functors-basics chapter and sk-thm-sf-ctf-stability unit
were read. This is a supporting BLR result, not that blueprint unit's statement. The
ancestor tool reports None for the inherited broken created-item chain; the new node
preserves that ancestry rather than inventing a blueprint ancestor.

Hypotheses and clauses, with their Lean renderings:

- DVR and uniformizer: `R`, `[CommRing R]`, `[IsDomain R]`,
  `[IsDiscreteValuationRing R]`, `π`, `hπ : Irreducible π`.
  The recorded DVR interface explicitly identifies irreducibility with generating the
  maximal ideal; it excludes fields and the zero ring.
- Fraction field: `E`, `[Field E]`, `[Algebra R E]`, `[IsFractionRing R E]`.
  The trait is exactly `Spec (.of R)` and its closed point is `IsLocalRing.closedPoint R`.
  Residue fields are those of the scheme-theoretic fibres, not unrelated chosen fields.
- Geometric strict henselization: `Ω`, `[Field Ω]`, `[IsAlgClosed Ω]`, the morphism `s`,
  and `hs` fixing its image to the closed point. The ring is exactly the recorded
  `Scheme.strictHenselizationRing s`; `strictMap` is computed from the recorded structural
  morphism on global sections and `ΓSpecIso`. `F` with its algebra and fraction-ring
  instances is its fraction field. `ι` and `hι` express the uniquely determined extension
  of the fraction-field embedding, not an extra generic map or an arbitrary action.
- Smooth separated finite-type group of dimension d: `G : Over (Spec (.of E))`,
  `[GrpObj G]`, `[SmoothOfRelativeDimension d G.hom]`, `[LocallyOfFiniteType G.hom]`,
  `[QuasiCompact G.hom]`, and `[IsClosedImmersion (pullback.diagonal G.hom)]`.
  Constant relative dimension is the recorded smooth-dimension convention for a smooth
  group scheme; no connectedness, properness, characteristic or residue-perfectness
  assumption is added.
- Invariant nowhere vanishing volume form: `ω : Γ(TopForms G.hom d, ⊤)`;
  `TopForms` is the recorded exterior sheaf of the recorded relative differentials.
  `hω` uses the existing `Scheme.Modules.GeneratesAt` at every point.
  `hleft : IsLeftInvariant G d ω` compares pullback along multiplication and second
  projection relative to the first factor, so it expresses invariance under universal
  left translation, rather than only invariance on E-rational points.
- Canonical differential pullback: `TraitVolume.IsPullback` requires local expressions
  as finite sums of coefficient-weighted wedges of universal differentials, and the
  corresponding pulled-back expression on neighbourhoods covering the target. The
  equations determine the usual pullback on all generating wedges. It contains no
  arbitrary map parameter and no Nonempty choice. It covers change of base as well as
  generic identifications. Smoothness makes the local differential generators available;
  sheafification makes their finite-sum descriptions local.
- Boundedness: `hbounded : IsBounded ... G`. It chooses a finite affine cover `U`, finite
  algebra generating lists `b`, and integer lower bounds `c`. Ring closure of the image
  of E and the generators is the entire coordinate ring, which is exactly finite
  generation as an E-algebra. Each F-point factors through one selected chart and has
  `π^(-c i) * b_ij(x)` in the image of the actual strict henselization ring. This is
  `v(b_ij(x)) ≥ c_i`, including zero. A choice of chart per point is equivalent to the
  decomposition into the subsets C_i in the node; overlapping chart subsets are allowed.
- Smooth model: `TraitVolume.Model` has the actual scheme, structure morphism, smooth,
  locally finite type, quasi-compact and closed-diagonal proofs, and an isomorphism
  in `Over (Spec E)` of its actual generic pullback with G. It does not replace a model
  by abstract data. `Model.Admissible` is `IrreducibleSpace` of the special fibre,
  which includes nonemptiness.
- Order: `HasOrder π G d ω M n` chooses the special-fibre generic point and an actual
  global normalized extension β, uses canonical differential pullback relations to
  express β_E = π^(-n) ω, and requires the existing `GeneratesAt` at that generic point.
  This is the integer specified by the node's stalk condition. The use of a global
  extension changes no condition: BLR's paragraph before Lemma 1 proves that on a smooth
  model with irreducible special fibre the normalized form extends globally. First it
  extends near the only vertical codimension-one generic point and over the generic
  fibre, hence across all codimension-one points; normality extends it across the
  remaining codimension-at-least-two set. Any components not meeting the special fibre
  already lie entirely in the generic fibre. No extra theorem or assumed extension is
  passed as input to the main statement.
- The minimum exists and is attained: `∃ n₀, IsMinimum π G d ω n₀`. The first conjunct
  of IsMinimum exhibits an admissible model with order n₀; the second bounds every
  order of every admissible model below by n₀. Thus the minimum is not an infimum that
  could fail to be attained.
- Finitely many nonempty classes: the first conclusion exhibits `r` and `M : Fin r → Model`;
  `Representatives` includes `0 < r`, admissibility and order n₀ of every member, and
  coverage of every admissible model of order n₀ by `Model.Equivalent`. A finite cover
  of an equivalence relation is equivalent to finiteness of its quotient. Repetitions
  are permitted; hence all choices of representatives in the node are included.
- Birational equivalence: `Model.Equivalent` exhibits an actual isomorphism between
  open subschemes, fibrewise dense on both sides, over the trait and inducing the
  identity under the chosen generic identifications. One may adjoin the entire generic
  fibres to the witnessing opens, since their generic morphism is the identity and
  the maps agree on the overlaps. Thus requiring their entire generic fibres does not
  strengthen the node's relation. No ordinary generic-only rational-map predicate is
  substituted for fibrewise birationality. Rational-map quotients and maximal domains
  are not needed in the final assertion and are not redeclared.
- Every representative list: the last conclusion is a universal implication from
  `Representatives ... M` to `SmoothBaseChange ... M`, in addition to the existential
  representative list. It is not restricted to the initially chosen weak family.
- Arbitrary smooth finite-type Z and special generic ξ: SmoothBaseChange quantifies
  over every scheme Z, structure morphism f, smoothness, local finite type and
  quasi-compactness, and every `ξ ∈ genericPoints (f.fiber closedPoint)`.
  Empty Z has no such ξ and gives the required vacuous clause.
- A = O_(Z,ξ) is a DVR with uniformizer π: the ring is the actual stalk
  `Z.presheaf.stalk (f.fiberι closedPoint ξ)`. The conclusion supplies IsDomain,
  IsDiscreteValuationRing and irreducibility of `localMap f ... π`.
  `localMap` is precisely the germ of the structural global section, hence the
  canonical map R → A, not a freely chosen local algebra.
- L and the pulled-back form: universally quantify over a field L with its A-algebra
  and fraction-ring structure; the existential `c : E →+* L` is constrained on every
  element of R by the local map. There is only one such extension of a fraction-field
  embedding. Its scheme base change is `(Over.pullback (Spec.map (.ofHom c))).obj G`.
  The form `ωL` is required to be the canonical pullback of ω along that base change.
- The new minimum is the same n₀: SmoothBaseChange includes IsMinimum for G_L, ωL and
  the image of the same uniformizer, not just inequalities for a supplied family.
- Component opens are minimal and exhaust all classes: `ComponentRepresentatives`
  has three clauses. Every irreducible component of the actual special fibre of the
  actual pullback M_i ×_R A admits its open submodel. Every such open is admissible
  and has order n₀. Finally every admissible A-model of order n₀ is equivalent to a
  component open of some M_i. `IsComponent` explicitly requires an open immersion
  into the base change, contains the entire generic fibre, and has exactly that
  special component. Its three generic comparison equations preserve the specified
  generic identification. No arbitrary noncanonical lift is substituted.
- Shrinking: `Model.IsShrinking` is an open immersion over R, containing the entire
  generic fibre, dense on the special fibre and compatible with generic identifications.
  Its complement is closed, contained in the special fibre and nowhere dense there,
  exactly the node's permitted removal. SmoothBaseChange universally quantifies over
  every such shrunk list N and asserts ComponentRepresentatives for N with the same
  n₀, L, c and ωL. Shrinking is not asserted for a subset meeting the generic fibre.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`,
  `irreducible_iff_uniformizer`; fraction fields use `IsFractionRing`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: the recorded convention is
  actual `Limits.pullback`, its projections, and `Over.pullback`; the main declaration
  `Scheme.Modules.moduleBaseChange` is for modules and is not misused as a scheme.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`, `SmoothOfRelativeDimension`;
  Morphisms.FiniteType/QuasiCompact: `LocallyOfFiniteType`, `QuasiCompact`;
  Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, with multiplication `MonObj.mul`;
  the scheme specialization is publicly imported by GroupScheme.Defs.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`; geometric points use
  `Scheme.SpecToEquivOfField` from Mathlib.AlgebraicGeometry.ResidueField.
- WeilConjectures.AlgebraicGeometry.StrictHenselization: `strictHenselizationRing` and
  `strictHenselizationScheme`; StrictHenselizationStructuralMap:
  `strictHenselizationStructuralMap`, through its already recorded definition node.
- WeilConjectures.AlgebraicGeometry.Modules.Differentials: `relativeDifferentials`,
  `relativeDifferentialsDerivation`; DifferentialsSections: `specStructureMap`.
- Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf: the dependency's exact `exteriorSheaf`
  and `exteriorSheafSection`, not the separate upstream exteriorPower interface.
- WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus: existing `GeneratesAt`,
  through def-sc-section-generating-locus. A preliminary local version was removed
  when this exact upstream definition was located; the delivery does not duplicate it.
- Proof-only imports: Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen and
  Mathlib.RingTheory.Kaehler.TensorProduct, including the recorded universally-open
  field projection and `KaehlerDifferential.tensorKaehlerEquivBase`. The three geometric
  statement proof dependencies (weak family, spreading, order comparison) have no
  recorded Lean declarations on the read base, so there is no module to import yet.

Edge cases checked by reading the explicit definitions:

- d = 0 uses the existing exteriorSheaf zero power and empty wedges. The scalar
  identification is built into local pullback expressions; no positive-dimension binder.
- Zero coordinate values satisfy integrality with witness 0, respecting v(0) = infinity.
- The empty affine index family cannot cover a nonempty group scheme, so hbounded does
  not create an empty-family loophole; the identity section ensures G is nonempty.
- The representative index is explicitly positive; empty special fibres are excluded
  by Admissible, while empty smooth test schemes make only their local clause vacuous.
- Disconnected G and splitting of special fibres after residue extension are allowed.
  Components are not assumed geometrically irreducible. All component opens are
  quantified over, and different components may represent the same birational class.
- The residue field can have arbitrary characteristic and need not be perfect.
- Proper shrinking in the special fibre, empty removal, and the identity shrinking
  are all allowed; deleting a generic point of the special fibre fails density.
- All schemes, rings and tests use the same explicit universe u, following the scheme
  APIs. No unrelated small test universe makes a universal assertion vacuous. No
  local/extension field is chosen from an unproved existence theorem.

Searches made (all service searches through msearch.py; details and digests accompany
new-node mathlib_searches and the sandbox searches.jsonl):

- LeanSearch: “Smooth trait models birational equivalence minimal volume order bounded
  rational points over a discrete valuation ring”. Eight hits, ordinary smoothness,
  DVRs and Weierstrass minimality; no trait volume interface or theorem.
- LeanFinder: “Smooth models over discrete valuation rings with bounded rational points
  and differential volume order at the generic point of the special fibre”. Eight
  Weierstrass-reduction hits; no match to smooth models of arbitrary bounded groups.
- Loogle: `IsDiscreteValuationRing`. Twelve hits confirm the existing DVR class and
  basic valuation API; no model/equivalence/volume-order theorem. An earlier combined
  query reported unknown identifier Scheme; that is not used as absence evidence.
- msearch grep: `SmoothModel|BaseDense|volumeOrder|invariantForm` in Mathlib's
  AlgebraicGeometry directory: zero hits.
- rg in source WeilConjectures, project Sheaf and upstream name index for those names
  and TraitVolume: no relevant interface; finiteSmoothModelCoordinates is unrelated
  finite-proetale coordinates. rg over definition DAG nodes found no such notion.
- blueprint_refs.py search “smooth model” and “trait volume”: zero blueprint matches.
- Direct source searches found relativeDifferentials, exteriorSheaf, strict henselization
  and GeneratesAt. These exact declarations are reused. No declaration says the main
  node's whole assertion, so existing:true would be incorrect.

No STATEMENT-DISPUTED issue remains. The inherited missing blueprint ancestor and absent
local BLR PDF are recorded above; the primary scan was available and read.

## New nodes

`def-sfb-trait-volume-models` packages the missing notion of a smooth model with its
specified generic identification and the volume/minimality predicates on such models.
It introduces concrete models, fibrewise birational equivalence, full-point boundedness,
canonical local wedge pullback, invariant forms, order, finite representative lists,
permitted shrinkings and component representatives, and the smooth-local base-change
conclusion predicate. Its sources are BLR 1.1 Definition 2, 2.5, 4.2 and 4.3, especially
pp.103–106. The three kinds of searches above found no existing interface; every existing
scheme, group, differential, exterior, generating-locus and henselization notion is
imported instead of copied. This single definition node owns the helper module and all
18 explicit declarations listed in its lean record. It is cited directly by the item.

## Second reading by Q15

Second reading performed by the maintainer's independent cc reviewer (the delivered
section was a same-worker self-read, delivery-errors H11). Each item of the node with its
Lean rendering and verdict:

- DVR R, uniformizer π, fraction field E, T = Spec R: `IsDiscreteValuationRing R`,
  `hπ : Irreducible π`, `IsFractionRing R E`; closed point `IsLocalRing.closedPoint R`. Exact.
- Geometric closed point and R^sh, E^sh: `Ω` algebraically closed, `s`, `hs` (image = closed
  point); `Scheme.strictHenselizationRing s` (def-weil-pbc-strict-henselization-limit) with
  `strictMap` built from the landed `strictHenselizationStructuralMap` (pinned by the limit
  legs); `F` its fraction field; `ι` pinned on R by `hι`, hence the unique extension. Exact;
  no `IsDiscreteValuationRing` presupposition on R^sh is added.
- Boundedness of G(E^sh): `IsBounded` = finite affine cover, generating lists (Subring
  closure of the image of E and the b_ij is everything = finite generation as E-algebra),
  integers c_i, every F-point over ι factoring through some U_i with π^{-c_i} b_ij(x) ∈ R^sh,
  i.e. v(b_ij(x)) ≥ c_i, zero included. Exact.
- G smooth separated finite type of dimension d, group: `GrpObj G`,
  `SmoothOfRelativeDimension d`, `LocallyOfFiniteType` + `QuasiCompact`, closed-immersion
  diagonal. Exact.
- ω nowhere vanishing left invariant in Ω^d: `TopForms` = exteriorSheaf of
  relativeDifferentials; `hω` via landed `GeneratesAt`; `IsLeftInvariant` = m^*ω = pr_2^*ω
  relative to pr_1 (universal translation). Exact.
- Smooth model, admissible, order n(M): `Model` (actual scheme, smooth, lft, qc, separated,
  `genericIso`); `Admissible` = irreducible (hence nonempty) special fibre; `HasOrder` =
  global β with β|_E = π^{-n}ω (via the local-wedge `IsPullback` relation along the
  generic identification) generating at the special generic point. On a smooth model
  with irreducible special fibre, π^{-n}ω generating at ζ has trivial divisor (the only
  vertical codimension-one point is ζ) and M is normal, so it is a global section: the
  global form is equivalent to the stalk definition. n is unique since π is a uniformizer
  of O_{M,ζ}. Exact.
- Minimum n_0 exists: `∃ n₀, IsMinimum` (attained + lower bound). Exact.
- Finitely many classes, at least one, representatives: `Representatives` (0 < r, members
  admissible of order n₀, coverage by `Model.Equivalent`), existential list plus a universal
  implication for every representative list (repetitions allowed; true and harmless).
  `Equivalent` requires the witnessing opens to contain the generic fibres; equivalent to
  the node's relation by gluing with the identity on the generic fibre. Exact.
- Smooth finite-type Z, generic point ξ of Z_k, A = O_{Z,ξ} DVR with uniformizer π:
  `SmoothBaseChange` quantifies over all Z, f smooth lft qc, ξ ∈ genericPoints of the
  special fibre; stalk IsDomain + DVR + `Irreducible (localMap … π)`. Exact.
- L, ω_L, minimum again n_0: ∀ L fraction field, ∃ c pinned on R, ∃ ω_L = pullback of ω,
  `IsMinimum` over A with n₀. Exact.
- Component opens minimal and exhaustive: `ComponentRepresentatives` with `IsComponent`
  (open immersion into M_i ×_R A over A, containing the entire generic fibre, special
  part exactly the component C, generic identification induced by the canonical map q).
  **Mismatch found and corrected**: the delivered second clause read
  `∀ i P, ∃ C, IsComponent … P C → P.Admissible ∧ HasOrder …`, which is vacuous (take C
  not an irreducible component, e.g. ∅). It now reads `∀ i P (C : Set …), IsComponent … P C → …`,
  saying, as the node says, that every component open is admissible of order n₀.
  Component opens are quasi-compact because M_i ×_R A is Noetherian, so clause 1 is
  satisfiable as stated.
- Shrinking: `Model.IsShrinking` (open immersion over T containing the generic fibre,
  dense in the special fibre, same generic identification) = removal of a closed nowhere
  dense subset of the special fibre; ComponentRepresentatives asserted for every shrunk
  list. Exact.

Edge cases: d = 0 (empty wedges, exterior power 0); zero coordinates (witness 0); empty Z
(vacuous); residue characteristic arbitrary; disconnected G and non-geometrically
irreducible components allowed; repetitions allowed. One universe u throughout, as the
scheme APIs require.

Searches: Mathlib `BirationalOver` (generic-only birationality, not fibrewise),
WeierstrassCurve minimality (different notion); project trees for TraitVolume, SmoothModel,
volume order: none. A parallel delivery of this item by NW (f3ca7290, same file paths and the
same new node id with different content) is not landed; only one of the two may land.

Change made: `lean/Sheaf/AlgebraicGeometry/TraitVolumeModels.lean`, clause 2 of
`ComponentRepresentatives` (∃ C → ∀ C). Both modules compiled clean through nt_compile
(only the postponed-proof warning).
