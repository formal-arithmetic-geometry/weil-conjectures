## Worker report

The module `Sheaf.AlgebraicGeometry.TraitComponentMinimalEnvelope` states
`AlgebraicGeometry.TraitComponentEnvelope.minimal_envelope` with `sorry`.
All preceding declarations are explicit constructions or predicates unpacking this
same node's objects and clauses. There are no new independent notions requiring
new DAG nodes, no dependency repairs, and no changes to the natural-language node.
In particular, `envelope` is the actual infimum of the candidate subfunctors in
Mathlib's complete lattice, not a choice of data from a postponed existence proof.

Hypothesis and clause correspondence:

- The arbitrary DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The nonfield requirement is part of Mathlib's DVR
  class. The base is exactly `Spec (.of R)`; `specialMap` uses the residue field
  quotient and `genericMap` uses the canonical fraction field inclusion.
- The group sheaf is `F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}`. `IsForm F`
  requires `Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (F ⋙ forget GrpCat)`.
  Thus it imposes the fpqc equalizer condition on underlying sets and actual
  group homomorphisms on restrictions, without commutativity.
- The fpqc morphism is the existential `p : T ⟶ S` in `IsForm`, with
  `Presieve.singleton p ∈ Scheme.fpqcPrecoverage S`. This does not assume that
  `p` is quasi-compact: it uses the covering notion recorded by the dependency.
- Its representing scheme is `P : FibreModel F p`; `P.repr` is the recorded
  `Functor.RepresentableBy`. The group structure is canonically transported by
  `GrpObj.ofRepresentableBy`, so requiring a set-valued representation loses no
  group-scheme data. `IsSeparated P.X.hom`, `Flat P.X.hom` and
  `LocallyOfFinitePresentation P.X.hom` are exactly the three chart properties.
  Mathlib defines `IsSeparated` by the diagonal being a closed immersion.
- The existential models `Ms` and `Mg` represent the special and generic group
  functors, respectively. `FieldComponents Ms ∧ FieldComponents Mg` gives local
  finite type and, for every point, its connected component as an open whose
  underlying subset is also closed and whose structure morphism is locally
  finite type and quasi-compact, hence finite type. Every nonempty connected
  component has such a point; no global finite number of components is assumed.
- `neutral Ms` is the connected component of the identity point with the group
  structure transported from the original functor by the representation.
  `NeutralProperties Ms` states geometric connectedness of that open subscheme,
  and that its sections form a subgroup on every scheme test. It also identifies
  the identity component of every representing model of `F × F` with the
  intersection of the inverse images of the two neutral components along the
  two induced projection maps. This is the fibre-product clause, independent of
  a choice of representing product scheme.
- `HasFibre E Ms C` expresses the prescribed fibre on every scheme test, not just
  on field-valued points: a section belongs exactly when its representing
  morphism has point image in `C`. This is precisely factorization through the
  open component subscheme. Nonreduced test schemes are retained.
- `IsComponentUnion E Mg` supplies an arbitrary set of connected components,
  using the quotient `ConnectedComponents` and its canonical projection.
  `IsCandidate` combines this with the special-fibre condition and the actual
  relatively representable open-immersion property of `E.ι` on every test scheme.
- For each special component, the `IsLeast` clause says both that the explicitly
  constructed `envelope` belongs to that candidate set and that it is contained
  in every candidate. Thus it asserts smallestness, not merely minimality.
- `IsFiniteComponentUnion` additionally requires the indexing subset of generic
  components to be finite. It is a conclusion, not part of the candidate
  predicate, so minimality is among all component-saturated candidates.
- `FiniteOnCharts` gives a representing scheme for the base change of the
  envelope to each fpqc representing chart of the stated kind, together with
  separatedness, flatness, local finite presentation, quasi-compactness and
  quasi-separatedness. The last three properties are finite presentation.
  Quantifying over charts restates the original assertion for arbitrary choices
  of the given chart, rather than choosing one extra privileged chart.
- Membership of `1` on every `V : Over S` is the factorization of the identity
  section through the envelope of the neutral component. Naturality already
  holds for the original identity and the inclusion of a subfunctor.
- `IsoCompatibility` uses the induced special-fibre morphism `modelMap a.hom`
  to transport the component and asserts equality of the image envelope with
  that component's envelope for the isomorphic form.
- Only `IsStrictlyHenselianLocalRing R → ProductCompatibility Ms Mg` requires
  strict henselianity. `ProductCompatibility` identifies the product envelope
  with the intersection of the inverse images of the individual neutral
  envelopes along the actual projections `prod.fst` and `prod.snd`.
  The component of the product identity is precisely the product of the two
  identity components; this is expressed without arbitrarily choosing product
  coordinates on the representing schemes. No product condition is imposed on
  nonneutral components or over a nonhenselian DVR.
- `MapCompatibility` quantifies over another form and a group-functor morphism.
  `IsLocallyFlatLfp` imposes relatively representable flat lfp on an fpqc base
  change. Equality of the special component's image with the target component
  renders “onto”. The conclusion is the image-subfunctor inclusion between the
  two canonical envelopes. No stronger special-fibre assumption is substituted.
- There is no smoothness, reducedness, commutativity, finite-type-total-space,
  completeness, excellence, or henselian assumption in the initial hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec`, `Spec.map` (scheme and spectrum dependencies).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and projections; products and induced maps
  use the compatible categorical product/Over interfaces.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage` and the
  associated `fpqcTopology`; `Mathlib.CategoryTheory.Sites.Over` gives its
  slice-site topology.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.RepresentableBy`, used by
  `FibreModel.repr`; `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` supplies
  `GrpObj.ofRepresentableBy` for the unique transported group structure.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Morphisms.Flat`: `Flat`;
  `Morphisms.ClosedImmersion`: `IsClosedImmersion` via
  `Morphisms.Separated.IsSeparated`; `Morphisms.FiniteType`:
  `LocallyOfFiniteType` and `Morphisms.QuasiCompact.QuasiCompact`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing` (Mathlib leaf, without a separate lean record).
- `Mathlib.CategoryTheory.Subfunctor.Basic`: `Subfunctor` and its actual
  complete lattice; `Subfunctor.Image` supplies `image` and `preimage`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.CategoryTheory.MorphismProperty.Representable`:
  `MorphismProperty.presheaf` implements testing by represented pullbacks.
- `Mathlib.Topology.Connected.Basic`: nonempty `ConnectedSpace` and
  `connectedComponent`; `ConnectedComponents` is Mathlib's component quotient.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`, extending henselianity with separably closed
  residue field, exactly the recorded terminology dependency.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint`,
  the actual identity point used to define `neutral`.

Statement dependencies use public imports. Modules of all currently recorded
proof dependencies are imported (plain imports where only the proof needs them).
The following proof prerequisites have no recorded Lean declarations and hence
cannot yet be imported: `lem-sfb-field-fpqc-group-form-effectivity`,
`lem-sfb-group-local-minimal-prime`,
`lem-sfb-field-extension-irreducible-components`,
`lem-sfb-lft-field-group-neutral-component`, and
`lem-sfb-henselian-unavoidable-component-valuation-section`. These are proof
prerequisites, not missing notions in this statement. The theorem docstring
carries all eleven proof steps and their dependency names.

Edge cases checked before and after writing:

1. A DVR is not a field; the two canonical field maps are the intended ones,
   rather than two arbitrary points or field extensions.
2. Each fibre group has an identity, so its space is nonempty; components are
   indexed by their points, and empty subsets are never mistaken for components.
   The empty test scheme is still allowed in all section conditions.
3. An arbitrary infinite component group is allowed: only each envelope's generic
   component set is asserted finite. Candidate generic component sets are not
   required finite.
4. Nonreduced and nonsmooth groups are allowed, including positive characteristic
   examples. Fibre membership uses all scheme tests, so it retains nilpotent data
   through factorization into the prescribed open.
5. For a connected field fibre the component clauses reduce to the whole fibre.
   The trivial group is admitted. No new finite-type assumption on the fpqc
   covering scheme is imposed.
6. The product equality has a strict-henselian premise and uses neutral
   components only; it does not reinstate the rejected arbitrary-DVR product
   assertion. Morphism compatibility retains the stated flat/lfp/onto assumptions.
7. All schemes, rings and section groups use the same `u`, the project's usual
   scheme-test and Yoneda size convention. There is no smaller independent test
   universe that could make any hypothesis vacuous. `autoImplicit` is false.
8. The infimum exists before its candidate property is proved. Even if the
   candidate set were empty, the definition would still have real data; the
   theorem asserts that this does not occur under the mathematical hypotheses.

Searches (the exact automated outputs are logged by msearch.py):

- LeanFinder: “Minimal component saturated open subfunctor of an fpqc group
  sheaf over a discrete valuation ring”: eight unrelated valuation/topological
  and fpqc/open-neighborhood hits; no matching statement.
- Loogle: `connectedComponent, Subfunctor`: no hits, service reports unknown
  identifier `Subfunctor`. Direct source reading located Mathlib's actual
  Subfunctor API, including the lattice, image and preimage, and uses it.
- Mathlib grep: `component.*[Ee]nvelope|minimal.*[Oo]pen|[Oo]penSubfunctor`
  in `AlgebraicGeometry`: zero hits.
- LeanSearch: “Canonical minimal open subfunctor with fixed connected special
  fibre component and component saturated generic fibre over a trait”: hits
  include Subfunctor projections and general affine/open diagrams, no envelope.
- Project `rg`: `TraitComponent|traitComponent|componentEnvelope|minimalEnvelope|
  FpqcGroup|fpqcGroup|OpenSubfunctor|IsOpenSubfunctor` on both `lean/Sheaf` and
  `lean/WeilConjectures`: only imports of the existing fppf open-subfunctor
  descent theorem, not a component-envelope declaration. Read those interfaces.
- Exact-node-id search on `lean/WeilConjectures` and `lean/Sheaf`: no matches.
  Read the source signatures/docstrings of every recorded statement dependency.
  The example CompactObject Sheaf module is withdrawn; its node points to the
  upstream `WeilConjectures.CategoryTheory.CompactObject` definition.

Source checked: primary scan
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf,
Anantharaman 4.2.4, printed pp.59-60, and the following neutral-component argument
on pp.60-61, together with this node's explicit strict-local product correction.
The local archive is WANTED in the inherited source record; the scan itself was
opened and its lemma and surrounding argument read. No statement correction or
STATEMENT-DISPUTED flag is introduced.

Validation: scompile.py compiled the sandbox and final library module cleanly.
The sole postponed theorem is `minimal_envelope`; every definition has full data.
The final delivery dry-run result is recorded by the wrapper.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
