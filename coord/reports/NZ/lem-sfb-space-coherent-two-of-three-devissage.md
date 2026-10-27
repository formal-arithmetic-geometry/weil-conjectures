## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentTwoOfThreeDevissage`
states `AlgebraicGeometry.AlgebraicSpace.coherent_two_of_three_devissage`, with
one whole-body `sorry`. There are no new definitions or auxiliary postponed
lemmas. I read the node's entire ten-step proof and Stacks
`literature/stacks-project/spaces-cohomology.tex`, lines 2561–2630,
Tag 08AN, `lemma-property-higher-rank-cohomological-variant`. The docstring
carries all ten DAG proof steps, including the annihilator-to-support argument,
the zero-ideal cases, and the final filtration.

Hypotheses and clauses, matched individually:

- The base scheme is `{S : Scheme.{u}}`; the space over that base is
  `X : AlgebraicSpace S`. Modules are the existing `X.Modules`, on its actual
  small etale ringed site, with section and ring universe `u`. There is no
  scheme specialization or equality of independent universes.
- Locally Noetherian on every etale scheme chart is `hln`, namely
  `∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)`.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)` in the existing
  atlas topology. Quasi-separatedness is `hqs`: compactness of the point spaces
  of `h_U ×_X h_V` for all affine scheme tests U,V. These test the diagonal on
  an affine basis of X ×_S X, exactly the quasi-compact-diagonal condition.
  This is the same interface used by the closed-coherent and support-power
  dependencies, without imposing separatedness.
- The property is `P : X.Modules → Prop`, used only on coherent modules.
  The node's isomorphism invariance is `hP_iso`, restricted to coherent F,G.
  Both have site `IsQuasicoherent` and chartwise `RingedSpace.IsCoherent`.
  Applying it to the inverse isomorphism gives the reverse implication too.
- Coherence is throughout the precise conjunction specified by the node:
  `F.IsQuasicoherent` and
  `∀ T, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
    ((X.schemeRestriction T).obj F)`.
  In particular finite type alone does not replace the finite-kernel condition.
- (0) is `hP_zero : P (⊤_ X.Modules)`. The terminal sheaf of modules has zero
  section modules and is a zero object, also in the empty-space case. This is
  the same zero-module representative used by the coherent-abelian dependency.
  Isomorphism invariance makes the choice of representative immaterial.
- (1) is `hP_seq`, quantified over every ambient `ShortComplex X.Modules` with
  `c.ShortExact`. All three terms have the explicit coherence conditions.
  Its three disjuncts cover pairs (1,2), (1,3), and (2,3); its conclusion gives
  all three P-values, hence exactly the previously missing third value.
- (2) is `hP_sum`, for every coherent F and every natural r with `1 ≤ r`.
  `b : Bicone (fun _ : Fin r ↦ F)` and `b.IsBilimit` specify the finite direct
  sum of r copies by its simultaneous product/coproduct universal properties.
  `P b.pt → P F` is the required reflection. Finite sums of module sheaves
  exist, so quantifying over their models is not vacuous. It needs no extra
  global choice of biproducts, and iso invariance identifies all models.
- (3) is `hP_witness`, for every Z and i with
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  Reducedness is `∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)`.
  `IrreducibleSpace (Point Z.obj.obj)` includes nonemptiness (as read in
  Mathlib's class), not merely preirreducibility.
- Its witness is an actual `M : X.Modules`, with site quasi-coherence,
  coherent chart restrictions, and `P M`. For every chart T and ring section
  a, the last iff says: a restricts to a scalar killing every module section
  on every `f : V ⟶ T` iff `a ∈ closedIdealSections i T`.
  The left side is precisely the sheaf annihilator's sections, not just the
  annihilator of M(T). The right side is the existing defining kernel ideal,
  computed by all canonical direct-image chart projections. Equality of
  membership on every chart is equality of these ideal subsheaves. This
  keeps scheme theoretic support, not merely equality of point supports.
- The conclusion quantifies over every `F : X.Modules` with exactly those two
  coherence conditions and concludes `P F`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `EtaleSite`, `etaleForget`,
  `structureSheaf`, `Modules`. The representability definition quantifies over
  scheme-valued pullback squares, as required for closed immersions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: its public slice
  sheafification instances and `QCoh` specialize the unchanged Mathlib
  `SheafOfModules.IsQuasicoherent` used directly in the signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleChartScalar`, `ModuleDirectImageModel`, `moduleDirectImage`,
  `moduleTensorPullback` and `moduleTensorAdjunction`. The closed-ideal kernel
  uses these canonical chart projections rather than an arbitrary ring map.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; this is the exact finite-type
  plus finite-type-kernels definition, not its weaker retained conjunction.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; scheme tests use this exact predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` on the existing `Point` classes.
- The already landed `def-trf-space-module-scheme-restriction` supplies
  `schemeRestriction` in `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`.
  The already landed `def-sfb-space-closed-ideal-filtration` supplies
  `closedIdealSections` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealFiltration`.
  Both nodes are added to stmt_deps to expose the exact existing constructions
  now used in the statement. Neither node is changed or duplicated.
- Mathlib `ShortComplex.ShortExact`, `Bicone.IsBilimit`, and `IrreducibleSpace`
  have their ordinary meanings, checked in their source signatures/docstrings.

The modules of all recorded proof dependencies available in the read clone are
plain imports: `AlgebraicSpaceCoherentAbelian`,
`AlgebraicSpaceClosedCoherentModules`, `AlgebraicSpaceCoherentSupportIdealPower`,
`ReducedClosedSubspaceSupport`, `AlgebraicSpacePowerIdealKills`, and
`AlgebraicSpaceCoherentIdealFiltration` (all under `Sheaf.AlgebraicGeometry`).
`def-trf-space-etale-module-functors` is also a statement dependency and is a
public import. Four proof-only dependencies have no Lean record in the read
clone, so no module can yet be imported for them:
`lem-sfb-space-noetherian-coherent-support`,
`lem-sfb-space-closed-immersion-quasi-coherent-modules`,
`lem-sfb-noetherian-space-topology`, and
`lem-sfb-space-reduced-support-generic-ideal-inclusion`.
They are not needed to type this statement and are named in its proof docstring.

Edge cases checked before writing: empty X (witness condition vacuous but P(0)
remains), F=0, r=1 and exclusion of r=0, Z a point, empty Z excluded exactly by
nonempty irreducibility, non-reduced X, zero ideal, intersecting identical ideals,
and finite sums represented by a different isomorphic bilimit. For the
annihilator formula, f=id forces a to kill M(T), and all further restrictions
ensure it kills the sheaf, including when M(T) fails to generate M locally.
For an affine example A/(x^2) versus the reduced closed space V(x), the ideals
(x^2) and (x) differ and our iff correctly rejects that module as the witness.
There is no statement correction and no disputed assertion.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- `leanfinder`: “A property of coherent modules on a Noetherian algebraic space
  follows from two out of three finite sum reflection and a module with
  prescribed annihilator on each reduced irreducible closed subspace”. Eight
  hits: Noetherian scheme predicates, module finite-type/presentation predicates,
  and ring-module induction; none is the algebraic-space theorem.
- `loogle`: `"IsCoherent", "Noetherian"`. Zero hits.
- `grep`: `devissage|d[eé]vissage|coherent.*property|property.*coherent`.
  Five Mathlib hits concern the quasi-coherence object property or coherent
  sites; no matching devissage statement.
- `leansearch`: “Coherent sheaves on a Noetherian algebraic space two out of
  three devissage with a faithful module on every integral closed subspace”.
  Eight hits concern local presentations, quasi-coherence, and faithful
  forgetful functors; no matching devissage statement.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` with those same
  devissage/property patterns found scheme devissage and unrelated constructible,
  derived and module devissages. I read `CoherentPropertyDevissage` and
  `CoherentSupportedPropertyDevissage`: neither treats algebraic spaces, and
  their witness/closure hypotheses differ. An item-id search in
  `lean/WeilConjectures` found no declaration. The chosen full declaration name
  also has no match in Mathlib, WeilConjectures or Sheaf.
- Additional direct searches for annihilator, schemeRestriction and closedIdeal
  found the exact closed-ideal construction reused here and the scheme-only
  annihilator ideal sheaf; no additional definition is needed.

Validation: prescribed `scompile.py NZ
lem-sfb-space-coherent-two-of-three-devissage <module>` succeeded for both its
sandbox and final module-path checks, with no errors or warnings. All variables
and the sole universe u are explicit, and there are no diagnostic commands.

## Second reading by NZ

This is a second pass by the same dispatcher-started worker; no independent
reader was started, following the explicit no-other-agents instruction. The
maintainer's independent delivery review remains separate. I reopened the node,
the final Lean file, the relevant Mathlib class signatures, and Tag 08AN.

I checked all three Noetherian components separately against hln/hqc/hqs; checked
that hP_iso and every term of hP_seq/hP_sum/hP_witness/the conclusion use both
site quasi-coherence and chartwise finite-kernel coherence; and checked the three
pairs in hP_seq individually. I checked the finite sum is r copies rather than
a free rank-r structure module, and that 1≤r is explicit. I checked that
IrreducibleSpace includes Nonempty. I checked the witness lives on X, rather
than Z, and that the annihilator iff tests restrictions to every V over T,
matching equality of sheaf ideals rather than point supports. The direct-image
kernel is the recorded closedIdealSections, not a new chosen map. P(0) is
present and zero is the terminal module used by the existing coherent-abelian
interface. No mismatch or statement correction was found in this pass.
