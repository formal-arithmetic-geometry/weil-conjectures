## Worker report

The delivery states `AlgebraicGeometry.neron_connected_model_globalization` in
`Sheaf.AlgebraicGeometry.NeronConnectedModelGlobalization`. It reuses the now-landed
`AlgebraicGeometry.IsNeronLftModel` and supplies one missing relative identity-component
predicate with its own new definition node and module. The only postponed proof introduced by this delivery
is this theorem; every delivered definition has actual data and there are no axioms or hidden
sorries in the delivered files.
The item's natural-language statement and proof are unchanged. No dependency module or
statement correction is needed.

Source read: BLR, Néron Models, §10.1 Proposition 9 (b) ⇒ (a), printed pp.294–295
(PDF pages 300–301), together with the component-chart gluing on printed p.293
(PDF page 299) in Proposition 7. Local PDF is absent. Read the primary scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
Proposition 9 first constructs a global connected model and then glues the local models;
our node starts with that global connected model already supplied. The current blueprint
is literature/blueprint/latest; this is the retained historical BLR subargument recorded
in the node's provenance, not a change to a blueprint unit.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- D Noetherian, integrally closed domain: `CommRing D`, `IsDomain D`,
  `IsNoetherianRing D`, `IsIntegrallyClosed D`. Dimension one is `hdim`:
  `ringKrullDim D = 1`. K is the actual `FractionRing D`, and S is `Spec (.of D)`.
  Choosing the canonical fraction field does not restrict any field-of-fractions choice.
- The canonical generic map is `neronGenericPoint D`; the localization is
  `neronLocalization D m`, induced by `algebraMap D (Localization.AtPrime m.asIdeal)`.
  `m : MaximalSpectrum D` ranges over every maximal ideal with its primality instance.
  `neronLocalizedGenericPoint` uses the canonical
  `algebraMap (Localization.AtPrime m.asIdeal) (FractionRing D)` from Mathlib
  RingTheory.Localization.LocalizationLocalization. Its existing `IsFractionRing` instance
  identifies this same K as the fraction field of the local ring. It is the
  canonical map from the local ring into the same fraction field, not an arbitrary map.
- A group scheme is Mathlib's `Grp (Over ...)`, whose `X` has the `GrpObj` structure.
  `IsCommMonObj G.X` and `IsCommMonObj B.X` give commutativity. The generic identifications eB, eL and eN are
  isomorphisms in `Grp (Over ...)`, so their group compatibility is built in. The local
  isomorphisms q are over-category isomorphisms with `IsMonHom` of their forward map;
  their inverses are automatically group homomorphisms. No duplicate group structure is introduced.
- G is smooth, separated, geometrically connected and finite type: exactly the five
  binders `Smooth`, `IsSeparated`, `GeometricallyConnected`, `LocallyOfFiniteType`,
  `QuasiCompact` on `G.X.hom`. The separated predicate is a closed diagonal. Mathlib's
  geometric-connectedness predicate says every field-valued base change is connected.
- B has exactly the corresponding five binders on `B.X.hom`, including connected geometric
  fibres. `eB` is a group isomorphism identifying its generic fibre with G.
- The local models are `L m`; `eL m` is the specified generic identification.
  `hL m : IsNeronLftModel (L m) G (eL m)` includes smoothness, separatedness, the group property of
  that identification, and bijectivity of restriction for *every* smooth test scheme.
  The local model has no quasi-compactness or finite-component assumption. It need not
  be separately assumed commutative: its multiplication and swapped multiplication
  agree generically, hence agree by uniqueness in its Néron property, since its square
  is smooth. Thus `L` supplies exactly local group models of the commutative generic G.
- `jL m` is the composite of the given isomorphism B_m ≅ L_m^0 with its open inclusion.
  `hjL m` says it is an open group homomorphism and its image on each geometric fibre
  is exactly the identity component. An open immersion identifies the full source scheme
  with the open subscheme, so this is equivalent to that isomorphism, including nilpotents.
- `hcompat` expresses the specified generic agreement of this inclusion with eB and eL.
  Its left side pulls back jL, maps to G via eL, goes back via eB, and projects to B.
  Its right side is the composite of the two canonical projections to B. Both maps are
  over the same generic base; their second projection is fixed, so this equality of first
  projections is equivalent to the usual equation using the canonical iterated-base-change
  isomorphism. It neither chooses an arbitrary comparison nor adds an extra condition.
- The conclusion quantifies `N : Grp (Over (Spec (.of D)))` and the generic isomorphism eN.
  `IsCommMonObj N.X` supplies commutativity; `IsNeronLftModel N G eN` supplies smoothness,
  separatedness, group identification and the unrestricted mapping property. Smoothness
  implies locally finite type. No quasi-compactness of N is asserted.
- The existential j embeds B as the relative identity component, giving N^0 ≅ B as groups.
  The equation `(Over.pullback ...).map j ≫ eN.hom.hom.hom = eB.hom.hom.hom` preserves the generic
  identification. The final `∀ m, ∃ q` gives group localization isomorphisms with every L_m.
  Its `IsMonHom q.hom` and first-projection equation preserve their generic identifications
  in exactly the same way as hcompat. These isomorphisms automatically respect the connected
  component inclusions by the identity-component characterization and generic uniqueness.
- Nothing restricts the number of maximal ideals, the component groups, or smooth tests.

Dependency declarations used, with signatures and docstrings inspected:

- def-weil-affine-spectrum and def-pc-scheme: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme`, `Scheme.Hom` in Mathlib.AlgebraicGeometry.Scheme.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion` in
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion; `IsSeparated` in Morphisms.Separated
  is precisely its application to `pullback.diagonal`.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth` in
  Mathlib.AlgebraicGeometry.Morphisms.Smooth. No formal-smoothness substitution.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` in Morphisms.FiniteType and
  `QuasiCompact` in Morphisms.QuasiCompact, as the recorded conjunction.
- def-pc-base-change: WeilConjectures.AlgebraicGeometry.BaseChangeConventions,
  `baseChange_morphism_projections`, `baseChange_iterated`, and the underlying
  `CategoryTheory.Over.pullback`/`Limits.pullback` convention. The record's main
  `Scheme.Modules.moduleBaseChange` is for module sheaves and is not misused for schemes.
- def-weil-pbc-localization-at-prime: `Localization.AtPrime` in
  Mathlib.RingTheory.Localization.AtPrime.Basic; the induced maps use IsLocalization.map.
- def-weil-open-immersion: `AlgebraicGeometry.IsOpenImmersion` in
  Mathlib.AlgebraicGeometry.OpenImmersion.
- def-weil-connected-scheme: `ConnectedSpace` and `connectedComponent` in
  Mathlib.Topology.Connected.Basic. `GrpObj.onePoint` is reused from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic with the induced pullback group object.
- The relative identity-component predicate uses the existing def-sc-group-scheme interface:
  `CategoryTheory.GrpObj`, `IsCommMonObj`, `IsMonHom`, `Grp` in Mathlib.CategoryTheory.Monoidal.
  New definition nodes cite this owning node, rather than duplicating it.

The main module imports the recorded proof-dependency modules: Proper (proper/smooth
base change), PointedSectionStageDescent, LimitFibreProducts,
SpecStalkLimitAffineNeighbourhoods, with the relevant Mathlib gluing, finite-stability,
affine-transition-limit and morphism-property APIs. The newly landed proof prerequisite
`lem-sfb-closed-point-fp-patching` is now imported as
`Sheaf.AlgebraicGeometry.ClosedPointFPPatching`; its
`AlgebraicGeometry.finitePresentation_closedPoint_patching` signature and full proof
docstring were read during this repair. Its equivalence and detection clauses are the
ones used in steps 2 and 5 of the theorem docstring.

The landed definition node `def-sfb-neron-lft-model` is now a statement dependency.
Its declaration in `Sheaf.AlgebraicGeometry.NeronLftModel` is read both locally and via
scompile.py --source. It accepts the actual group model N, generic group V and a group
isomorphism of their canonical generic fibres, with `[IsFractionRing D E]`. It states
smoothness, a closed diagonal, and bijective restriction on every smooth test scheme.
The global application uses D and FractionRing D. The local application uses
Localization.AtPrime m.asIdeal and the same FractionRing D, with the canonical Mathlib
Algebra, IsScalarTower and IsFractionRing instances. No added hypothesis or replacement
mapping-property definition is needed. The `.hom.hom.hom` projections in the compatibility
equations forget the bundled group isomorphisms down to maps in Over.

Edge cases checked by reading definitions and the source:

- The trivial connected group is allowed; there is no positive dimension/rank hypothesis.
- The field case is excluded precisely by dimension one, as the node requires; local
  Dedekind domains with a single maximal ideal remain included.
- Infinitely many maximal ideals and infinitely many components are permitted. Neither L
  nor N is assumed quasi-compact; B and G retain exactly the stated finite-type assumption.
- Every smooth test scheme, including empty and non-quasi-compact ones, occurs in the
  mapping predicate. Empty schemes do not vacuously satisfy geometric connectedness, since
  ConnectedSpace contains Nonempty; groups have their identity section in each fibre.
- Imperfect residue fields and arbitrary characteristic are included. The component
  predicate quantifies over all algebraically closed field-valued points of the base and
  uses full open-subscheme structures rather than reduction. Smoothness ensures this is
  the fibrewise component notion in BLR.
- All schemes, their field-valued points and test schemes use the common arbitrary universe
  u, as the existing Scheme/GeometricallyConnected API does. No independent smaller test
  universe or imposed equality between distinct site universes occurs. autoImplicit=false.
- The generic compatibility equations were typechecked using canonical maps and projections;
  no arbitrary identification, stronger splitting datum or extra finite-type local model
  was substituted.

Original searches, before the parallel landing (full response summaries preserved in
searches.jsonl and new-node mathlib_searches). The repair found and reuses the subsequently
landed Néron-model definition, so the original no-match results are historical:

- msearch leanfinder: “Local Neron lft models globalize over a Dedekind domain with common
  connected identity component model”: 8 unrelated valuative/normalization/reduction hits.
- msearch loogle: “GrpObj, CommGrp, Over.pullback”: service reported unknown identifier
  GrpObj, 0 hits; supplemented by direct inspection of the pinned Mathlib group-object API.
- msearch grep: “Neron|Néron|neron”, AlgebraicGeometry: 0 hits.
- msearch leansearch: “Neron lft model mapping property smooth test schemes”: 8 smoothness
  API hits, no Néron mapping-property definition.
- msearch leansearch: “Open subgroup scheme whose geometric fibres are the connected
  components of the identity”: 8 topological-group/open-subgroup hits, no scheme predicate.
- msearch leanfinder: “Open immersion of group schemes inducing identity components on
  all geometric fibres”: 8 general open-immersion/gluing hits, no such predicate.
- msearch grep: “IsRelativeIdentityComponent|IsNeronLftModel|Neron|Néron”: 0 Mathlib hits.
- rg of the full lean/WeilConjectures and lean/Sheaf trees for Neron/Néron and the new names:
  no matches. The exact item id is also absent upstream. dag/lean_names_upstream.json has
  no Néron match. Searched group/component source files and read GroupScheme.Basic/Defs.
- rg of DAG definition nodes for Néron mapping-property and relative geometric identity
  components: no owning node. tools/blueprint_refs.py search Neron: 0 matches; search
  identity component: 36 general matches, with def-wf-algebraic-components only a closed
  algebraic matrix-group notion. It does not define the relative predicate.

No STATEMENT-DISPUTED flag or node fault remains. The example CompactObject module is
withdrawn in this checkout, so its current node's existing Mathlib binding and the module
header conventions in brief-stage2 and other live statement modules were followed.

Validation uses only scompile.py for the two delivered modules, independently in dependency
order, followed by deliver2.py --no-push and deliver2.py. No global build is run.

## New nodes

`def-sfb-relative-identity-component` defines `AlgebraicGeometry.IsRelativeIdentityComponent`
in Sheaf.AlgebraicGeometry.RelativeIdentityComponent. Source: BLR §10.1 Proposition 9.
It characterizes an open subgroup inclusion by its image on every geometric fibre.
The field-only, finite-type `GrpObj.identityComponent` cannot encode a smooth relative
lft group over Spec D. The new predicate reuses `GrpObj.onePoint`, connectedComponent,
Over.pullback, IsMonHom and IsOpenImmersion, so it is not a duplicate construction.

The item's stmt_deps gains the one new relative identity-component node and the existing
landed def-sfb-neron-lft-model. The latter node and its module are not part of this delivery.
The new node's blueprint ancestor is null, as tools/blueprint_refs.py ancestor reports;
its via chain is the item followed by the existing provenance chain.

## Repair of returned delivery

Return: independent immutable head 56a80e4bbec4 collided with the subsequently landed
`def-sfb-neron-lft-model` created by Q92. This repair removes our sandbox copies of that
node and `NeronLftModel.lean`, retains the dependency id, and imports the landed module.
The landed definition is specialized to a domain and its fraction field, and uses bundled
group isomorphisms rather than an over-category isomorphism plus IsMonHom. Accordingly:

- eB, eL and eN are now isomorphisms of bundled group objects under mapGrp; the redundant
  heB binder is removed because eB itself now asserts that same group compatibility.
- The local generic map uses Mathlib's canonical algebra map from the localization to
  FractionRing D, with the existing fraction-field instance. Thus both the local and
  global Néron assertions use the single landed IsNeronLftModel without restating it.
- The generic-compatibility equations use the underlying Over maps of those same group
  isomorphisms; their mathematical meaning is unchanged.
- ClosedPointFPPatching has meanwhile landed and is added as a plain proof import.
- The item JSON is regenerated from current main, preserving every original field except
  lean and the authorized definition-dependency additions. The new relative-component
  node remains absent on main. There is no modification to the landed Néron definition.

The current main item and retained returned item differ only in lean and stmt_deps.
The retained delivered contents are those of returned head 56a80e4bbec, as stated by the
dispatcher. This is an interface adaptation plus removal of the conflicting new node,
not an unchanged re-push or a renaming of the duplicate definition. Independent mathematical
review remains with the maintainer; no second worker was launched.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
