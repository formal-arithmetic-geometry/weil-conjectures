## Worker report

The module `Sheaf.AlgebraicGeometry.ConnectedActionOrbitSectionAmpleness` states
`AlgebraicGeometry.Scheme.Modules.isAmple_of_connected_action_orbit_section_cover`,
with one postponed theorem and no new definitions. The node is unchanged except for
its `lean` field. No new nodes or dependency repairs are needed.

Hypothesis and conclusion correspondence:

- The Noetherian normal domain A is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]`. This is the normal-domain
  clause of the recorded normal-ring dependency, not a new normal-ring predicate.
- S = Spec A is written explicitly as `Spec (.of A)`; `H X : Over (Spec (.of A))`
  bundles the two schemes and their structure morphisms `H.hom` and `X.hom`.
- The multiplication, identity, inverse, and group identities are exactly `[GrpObj H]`.
  This extends Mathlib's `MonObj` with both inverse identities; it imposes no commutativity.
- The action a is `[ModObj H X]`. Its map is `(γ[H,X]).left`; its `one_smul` and
  `mul_smul` fields impose precisely the unit and associativity identities. The action
  is a morphism in `Over S`, so compatibility with the structure maps is included.
- Smoothness of H and X is `[Smooth H.hom]` and `[Smooth X.hom]`.
- Separatedness is `[IsSeparated H.hom]` and `[IsSeparated X.hom]`; Mathlib defines
  this as `IsClosedImmersion (pullback.diagonal ...)`, exactly as the node requires.
- Finite type of each map is the pair `[LocallyOfFiniteType ...] [QuasiCompact ...]`,
  following its dependency's recorded interface. Finite presentation is not added.
- Geometrically connected fibres are `hconnected`, quantifying over every field Ω and
  every `s : Spec (.of Ω) ⟶ Spec (.of A)`, with conclusion
  `ConnectedSpace (Limits.pullback (C := Scheme.{u}) H.hom s)`. This tests the whole scheme fibre and includes
  nonemptiness. The universe u is the common scheme/ring universe: fields testing a
  Scheme.{u} morphism use Type u as in Mathlib's geometric-property convention. Larger
  field extensions give the equivalent condition by descent to a small subextension;
  no equality between otherwise independent site universes is imposed here. This is
  exactly `geometrically_iff_of_isClosedUnderIsomorphisms` for ConnectedSpace,
  together with `GeometricallyConnected.eq_geometrically` in Mathlib; the relevant
  signatures and docstrings were read directly.
- The arbitrary invertible module is `(L : X.left.Modules) [L.IsInvertible]` using the
  recorded scheme-module predicate, not `SheafOfModules.IsInvertible`.
- The node's open V is `(V : X.left.Opens)`. Its defining equation `hV` is literally
  the supremum of all opens U with a positive n (`0 < n`), a global section of
  `L.tensorPow n`, `IsAffineOpen U`, and equality of U's underlying set with the
  recorded `nonvanishingLocus`. Thus V is exactly the union prescribed by the node;
  it is not an arbitrary smaller union, a selected finite family, or a hypothesis
  requiring affineness of the union. V is uniquely specified by this equation.
- The orbit-cover condition is `horbit`: the image under `(γ[H,X]).left` of the
  inverse image of V under `(snd H X).left` equals `Set.univ`. Mathlib's cartesian
  tensor in Over S is its chosen scheme pullback, so this domain is the underlying
  open H ×_S V in H ×_S X. It covers all scheme points, with residue-field extensions
  implicit in the fibre product, rather than merely the H(S)-translates of V.
- The sole conclusion `IsAmple X.left L` is the recorded absolute ampleness notion.
  There is no square-condition, generic connectedness, base section, transitivity,
  commutativity, properness, or nonemptiness assumption on X.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  the standard domain class `IsDomain` from Mathlib's ring definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, through
  the separatedness definition in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`
  identifies `(H ⊗ X).left` with `pullback H.hom X.hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `Scheme.Modules.tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.nonvanishingLocus`,
  `Scheme.Modules.IsAmple`.
- The additional existing categorical interfaces are `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp` (publicly imported by its Cartesian module)
  and `CategoryTheory.ModObj` in `Mathlib.CategoryTheory.Monoidal.Mod`.

Public imports supply the statement dependencies; plain imports supply recorded
proof dependencies with declarations available. In particular the normal-component,
invertible-pullback, relative-to-absolute twist and ample-isomorphism interfaces are
imported. The following proof-only nodes have no Lean record or Mathlib match in the
read DAG, so have no module to import: `lem-sfb-smooth-normal-ascent`,
`lem-sfb-pointed-generic-integral-action-square-power`,
`lem-sfb-square-action-affine-orbit-criterion`,
`lem-sfb-smooth-self-product-component-rank`, and
`lem-sfb-space-relative-ampleness-fpqc-descent`. None is needed to state this item.
The docstring carries all eleven proof steps from the node, including the induction
and descent over the open image, without adding their conclusions as hypotheses.

Source check: opened the primary PDF
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf and read
Proposition 6.4(b) and its sufficient-direction proof. In the current PDF this is
printed p.16 (zero-based PDF page 15); the node's source description says printed p.15.
This bibliographic page discrepancy does not change the mathematical statement.
The node's smooth finite-type Noetherian specialization fits the strict (N)-type
hypotheses; affine section loci are allowed among the source's quasi-affine loci.
No source statement correction is needed.

Edge cases checked before writing: for empty X, V is empty and `horbit` is the empty
image equality; the conclusion's compactness holds and pointwise assertion is vacuous.
No `Nonempty X` binder excludes this. For a trivial group, the image equality is exactly
V = X, reducing to the section-open definition of ampleness. Degree zero is excluded
by `0 < n`; degree one is allowed. Zero sections have empty nonvanishing locus and
cannot create spurious covering points. The open V itself need not be affine.
The map X to S can have a proper open image. L has no equivariant structure.
A connected fibre is nonempty, as required by the node's connected-scheme dependency.
No characteristic restriction is present. For example O(-1) on projective space does
not meet the covering hypothesis, rather than giving a false ampleness assertion.

Searches (via `/home/ubuntu/weil-launcher-all/batch2/msearch.py`, group NK and this item):

- LeanFinder: "An invertible sheaf is ample if the translates of affine nonvanishing
  loci of its global sections cover a smooth scheme under a connected group action".
  Eight hits, mainly Proj affine charts, affine-basic-open statements, and the
  quasi-affine open-cover construction; no matching orbit criterion.
- Loogle: "GrpObj, Action, IsAmple". Zero hits, with `unknown identifier 'GrpObj'`
  from the remote index. This search failure was supplemented by direct source reads
  of the categorical interfaces and by the successful searches below.
- LeanSearch: "An invertible sheaf is ample if translates of its affine section opens
  cover the scheme". Eight hits, ordinary affine covers and Proj basic opens; no match.
- Mathlib grep via msearch: `IsAmple|GrpObj|MulAction` under `AlgebraicGeometry`.
  Twenty-three hits, standard group objects, affine group schemes, smooth groups,
  and point-set actions on elliptic curves. No ampleness orbit criterion.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf`: group schemes, categorical
  actions, affine orbit criteria, Guo, and ampleness. Reused existing `GrpObj`,
  `ModObj`, `IsInvertible`, `tensorPow`, `nonvanishingLocus`, `IsAmple`. The nearby
  `SquareActionProjImmersionLocusStable`, `AffineNormalConnectedGroupAmple`, and
  `AmpleOrbitAffinePair` state different results with different hypotheses/conclusions.
- Direct rg for the exact node id in `lean/WeilConjectures` and for the proposed theorem
  name in both source trees and `dag/lean_names_upstream.json`: no matching declaration.

No STATEMENT-DISPUTED flag, statement fault, new node, or dependency repair.

## Second reading by NK

The dispatcher explicitly prohibits starting other agents. I reread the node and
completed module myself; the maintainer's independent reading follows delivery.
This section records that second pass without claiming another worker reviewed it.

The domain/normal/Noetherian hypotheses match the first sentence. The bundled Over
objects introduce exactly S-morphisms, with group and action laws supplied by GrpObj
and ModObj. Smooth, separated, locally finite type and quasi-compact are present for
both H and X. The connectedness hypothesis tests field base changes, not just ordinary
fibres. The line remains arbitrary. The defining equation for V uses all positive
powers and all global sections and requires each locus to be affine, while making
no affineness claim about V itself. The image equality uses the projection from the
scheme product, and concludes precisely absolute ampleness of the same line on X.
The empty case, absence of square/section/generic-connectedness assumptions, and
all eleven proof steps were checked again. The source PDF's printed page was updated
in the new module docstrings from the node's p.15 reference to the current p.16;
no existing source metadata was modified. The compiler caught the namespace-local
`Scheme.Modules.pullback` shadowing the scheme pullback; this was repaired with
`Limits.pullback (C := Scheme.{u})` in the field-fibre hypothesis, explicitly
fixing the category before the scheme-to-type coercion. No mathematical mismatch was found.

Validation: the final module passed `scompile.py NK
lem-sfb-connected-action-orbit-section-ampleness <module path>` on 2026-10-24,
in both sandbox and library modes, with no diagnostics. The initial scheme-pullback
elaboration was repaired by explicitly specifying `C := Scheme.{u}`; the only style
warning was repaired by writing `γ[H,X]` with the notation's expected spacing.
The node's recorded signature was regenerated verbatim from this final file.
