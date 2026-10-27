## Worker report

Item: `lem-sfb-subcanonical-residual-duality`. The delivered module is
`Sheaf.AlgebraicGeometry.SubcanonicalResidualDuality`. It defines the canonical
`AlgebraicGeometry.Scheme.Modules.subcanonicalEvaluation` with real data and states
`AlgebraicGeometry.Scheme.Modules.subcanonical_residual_duality` with `sorry`.
There is one postponed theorem, matching this DAG node. No node statement changes,
new nodes, or dependency modules are needed.

The canonical map is `(λ_ Hom(F,ω)).inv`, followed by tensoring
`homOfGlobalSection F s` with the identity and then the inverse tensor–Hom adjunction
applied to the identity of `Hom(F,ω)`. It therefore evaluates local homomorphisms
at restrictions of precisely the supplied section s. The helper is part of this
node's evaluation-image construction, as permitted by brief §1 (missing helpers),
and is listed in `lean.declarations`; it introduces no independent notion or choice.

Hypothesis and clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  The scheme and its specified k-structure are `X : Scheme.{u}` and
  `[X.Over (Spec (.of k))]`. Projectivity, nonemptiness, connectedness, and
  reducedness are the four explicit typeclass binders in the theorem.
- The existing `D : SubcanonicalClusterData k X S i` packages
  `D.pure_dimension : X.IsPureDimension 1` and `D.nodal`. The latter gives an
  isomorphism from each singular closed point's completed local ring to
  `MvPowerSeries (Fin 2) k / (X 0 * X 1)` AND the equation respecting scalar k.
  Thus it retains the completed local **k-algebra**, not merely an abstract ring.
  This is existing data from the recorded dependency, not an extra regularity condition.
- `hTwoConnected` quantifies over nonempty reduced closed subschemes A,B. Its
  `P,Q ⊆ irreducibleComponents X`, `Disjoint P Q`, union equality, and range
  equalities with `⋃₀ P, ⋃₀ Q` specify exactly reduced unions of components
  covering X with no common component. Their intersection is the recorded
  `CategoryTheory.Limits.pullback a b`; scalar degree-zero module cohomology
  of its structure sheaf has finrank at least two. Reducedness plus these
  ranges fixes the reduced closed-subscheme structures, excluding extra points.
- `S`, `i`, and `[IsClosedImmersion i]` specify the closed subscheme with its
  actual kernel ideal. `D.zero_dimensional` is `topologicalKrullDim S ≤ 0`,
  including the empty scheme. The additional `hSsub : IsSubcanonicalCluster i
  D.dualizing` requires the node's generic nonvanishing even for the empty
  cluster: D alone intentionally permits every empty cluster independently
  of subcanonicality for its splitting-index convention. It adds no restriction
  beyond the node's assumption that S is subcanonical.
- The dualizing line is `D.dualizing`, with `D.invertible`, the natural
  `D.duality` on all coherent finite-type modules, and `D.duality_natural`.
  These are the specified representing data of the nodal Serre-duality dependency,
  rather than an arbitrary invertible module or unnormalized linear equivalence.
  The splitting index mentioned as background is the already defined
  `subcanonicalSplittingIndex D`; the node asserts no formula about it, so
  there is no unused index parameter or invented index-invariance conclusion.
- `subcanonicalModule i D.dualizing` is exactly `i.ker.toModules ⊗ D.dualizing`.
  Its degree-zero scalar cohomology is V_S. The first conclusion is injectivity
  of the actual canonical inclusion on global sections, expressing the stipulated
  subspace of canonical sections. The sheaf map is O-linear, hence k-linear.
- Throughout, genus is written out as the integer `1 - eulerChar k (unit X)`.
  Each length is the finrank of scalar degree-zero cohomology of the cluster's
  structure sheaf along its composite structure morphism. Degree-zero module
  cohomology canonically equals global sections, with scalars restricted along
  this very k-structure map; no rational-point count or reduced length is used.
  Each h0 is scalar degree-zero module cohomology of the specified module.
- `∀ s : Γ(subcanonicalModule i D.dualizing, ⊤)` followed by the generic-germ
  nonvanishing hypothesis retains **every** admissible section. It uses
  `genericPoints.ofComponent` for every irreducible component. The conclusion
  `Mono (subcanonicalEvaluation ... s)` is a monomorphism of sheaves, not merely
  injectivity on global sections.
- The existential `J : X.IdealSheafData` specifies the residual as its canonical
  closed subscheme `J.subscheme` with closed immersion `J.subschemeι`.
  Its dimension is at most zero. Equality of `imageSubobject`s in ω states
  equality as the embedded subsheaf with the canonical `I_J ⊗ ω`, not merely
  an abstract isomorphism of modules. The following universal K clause states
  uniqueness among every zero-dimensional ideal with that evaluation image.
  Quasi-coherent ideal sheaves represent closed subschemes up to their unique
  over-X isomorphism, so literal equality of arbitrary scheme presentations is
  neither required nor substituted for ideal uniqueness.
- `IsSubcanonicalCluster J.subschemeι D.dualizing` is residual subcanonicality.
  The following t is a section in its ideal twist with nonzero generic germs;
  the equality of its image in ω with the image of s specifies the **same**
  ambient canonical section. The second evaluation is mono and has image equal
  to the canonical inclusion for the original i. Thus the second residual
  defines exactly the original ideal and closed subscheme, including nilpotents.
  Neither residual evaluation is an arbitrary existentially chosen map.
- The next two integer equalities state length(S)+length(S*) = 2pa-2 and
  h0(F_S)-h0(F_S*) = pa-1-length(S), respectively. All dimensions in integer
  formulas are cast to integers; there is no truncated natural subtraction.
- The final equality expands c(S*)=c(S) as the two expressions
  `2 * (1 - eulerChar k (unit X)) - length - 2 * h0`.
- Explicit `FiniteDimensional` conclusions cover canonical sections, V_S,
  Γ(S,O_S), global Hom(F_S,ω), Γ(S*,O_S*), and V_S*. The global-Hom space is
  represented by degree-zero cohomology of the recorded internal Hom sheaf.
  The earlier equality is h0(ω)=pa itself, and the pair of integer inequalities
  is 0≤length(S)≤2pa-2. There is no Cartier or reducedness assumption on S or J.

Dependency interfaces read and used (modules are imported directly or publicly
through `SubcanonicalSplittingIndex` and `NodalLineSerreRiemannRoch`):

| Node | Module and declaration |
| --- | --- |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective` |
| def-pc-euler-characteristic | `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, `AlgebraicGeometry.Scheme.Modules.eulerChar` |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`, `.fst`, `.snd` |
| def-pc-reduced-scheme | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced` |
| def-pur-sheaf-hom | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, `SheafOfModules.homObj`; its scheme abbreviation is `Scheme.Modules.homObj` in `WeilConjectures.AlgebraicGeometry.Modules.Dual` |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal`, the existing sheafification tensor |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`, via the `smoothLocus` used by D |
| def-sc-ringed-space-module-cohomology | `WeilConjectures.Topology.RingedSpaceModuleCohomology`, `AlgebraicGeometry.RingedSpace.moduleCohomology` |
| def-sfb-subcanonical-splitting-index | `Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex`, `subcanonicalModule`, `subcanonicalModuleInclusion`, `IsSubcanonicalCluster`, `SubcanonicalClusterData`, and the available `subcanonicalSplittingIndex` in `AlgebraicGeometry.Scheme.Modules` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed` (the relevant part of the Mathlib match) |
| def-weil-connected-scheme | `Mathlib.Topology.Connected.Basic`, `ConnectedSpace` |
| def-weil-irreducible-components | `Mathlib.Topology.Irreducible`, `irreducibleComponents` |
| def-weil-pbc-adic-completion | `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`, `AdicCompletion` and `AdicCompletion.of` |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries` |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension` |
| lem-sfb-nodal-line-serre-riemann-roch | `Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch`, `AlgebraicGeometry.exists_nodal_line_serre_riemann_roch`; its natural dualizing data are the existing fields of D |
| def-sbc-closed-immersion-ideal-sheaf | `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, `AlgebraicGeometry.Scheme.Hom.ker` |

Scalar cohomology is the existing `Scheme.Modules.scalarCohomology` in
`WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, whose
carrier is `RingedSpace.moduleCohomology` and whose action is `Module.compHom`
along `scalarMap f ⊤`. The evaluation helper uses existing
`homOfGlobalSection` from `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`
and `SheafOfModules.tensorHomEquiv` from
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
`imageSubobject` is Mathlib's `CategoryTheory.Subobject.Limits` construction.

Already stated proof dependencies are imported without `public`: projective
properness, Noetherianity (Mathlib), proper coherent Euler finiteness,
vanishing above dimension (already public), global functions, reduced-curve
dualizing module, coherent kernels/cokernels, zero-support Euler characteristic,
and Euler additivity. The nodal duality node is already public via the statement
interface. `lem-sfb-reduced-curve-torsionfree-biduality` has no Lean record yet:
it is used only in the future proof, introduces no object needed to type this
statement, and therefore has no import. Its natural-language role is retained
in proof steps 2 and 3 of the docstring. An earlier incomplete sandbox draft of
that proof-only dependency was removed rather than delivered as an unrelated
or weakened prerequisite.

Edge cases checked before finalizing:

- The empty cluster is allowed by `≤ 0`; subcanonicality still means an actual
  generic section. On a smooth genus-one curve the nonzero canonical section
  has empty zero scheme: S=S*=empty, lengths are zero and both h0 are one.
- On a genus-zero smooth curve there is no generically nonzero canonical
  section, so no S satisfies the subcanonical hypothesis; the statement does
  not incorrectly infer a negative upper bound for an admissible S.
- At a node the ideal `(u,v)` need not be invertible; sheaf Hom and the
  canonical image construction still make sense. Nothing replaces it by a
  Cartier divisor. A nonreduced finite subscheme is likewise retained by its
  whole ideal, with length given by its Artin ring, not its support.
- On a reducible curve, a section vanishing on one component is excluded by
  the explicitly universal generic condition, even if it is globally nonzero.
  An irreducible curve has no nontrivial P,Q decomposition, so the two-connected
  condition is correctly vacuous. All field characteristics are retained.
- Twisting a chosen dualizing line by its unique representing isomorphism
  transports all maps and sections; D's naturality prevents substituting an
  unrelated line bundle. All universes are explicit and `autoImplicit false`.

Searches for reuse (2026-10-24):

- `msearch.py ... leansearch "Residual cluster duality for a subcanonical zero dimensional subscheme on a projective nodal curve"`: eight residue-field and closed-immersion hits; none is residual duality.
- `msearch.py ... leanfinder "Residual duality for a subcanonical zero dimensional subscheme of a reduced nodal curve, evaluation image, complementary lengths and equal Clifford index"`: eight hits, mainly Weierstrass ideal identities and smooth/etale loci; none is this statement.
- `msearch.py ... loogle "SheafOfModules.homObj, AlgebraicGeometry.Scheme.IdealSheafData, subcanonicalModule"`: no hits; Loogle reports its index does not know `SheafOfModules.homObj`. The existing upstream declaration was then read directly, not treated as absent.
- `msearch.py ... grep "subcanonical|residual.*cluster|Clifford.*index" AlgebraicGeometry`: fifteen site-subcanonical hits, no residual-cluster theorem.
- `rg -n` for the same pattern over `lean/WeilConjectures` and `lean/Sheaf`, and the item id over `lean/WeilConjectures`: the upstream hits concern subcanonical sites; the project has exactly the useful `SubcanonicalSplittingIndex` interface and no residual-duality declaration. Read and reused it. Direct source searches also located the tensor–Hom adjunction and section-to-map construction, so no private copy of either was made.

Source checked: author-hosted primary PDF
<https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf>, Definitions 2.9 and 2.10,
Remarks 2.11 and 2.13, printed pp.231–232. The evaluation-image formula and
Clifford equality agree with the node. No statement dispute or correction remains.

Validation: server-only `scompile.py Q34 lem-sfb-subcanonical-residual-duality`
compiles both the sandbox presentation and the actual library module. Definitions
have real data and the only postponed proof is the matching theorem's `sorry`.

## Second reading by Q34

This is a second clause audit by the dispatched worker, not a claim of an
independent agent review. The dispatch explicitly says not to start other
agents and assigns the independent delivery review to the maintainer.
With the node and final file open, I checked every correspondence above and
re-read the defining dependencies used in D and the evaluation construction.

The interrupted draft's defects were repaired: it had only existentially chosen
evaluation with no specified s; it asserted injectivity only on top sections;
it gave only an abstract image isomorphism and no residual uniqueness; it did
not connect the second residual with the first or the same section; it lacked
scalar compatibility in the nodal isomorphism and naturality of duality; its
section difference had pa in place of pa-1; it omitted several finite-dimensional
spaces; and its decomposition condition allowed closed subcurves with added
points rather than exactly reduced unions of components. The final theorem uses
the actual evaluation at every generic section, sheaf monomorphisms, image
subobjects and ideal uniqueness, the common ambient section in the second image
identity, D's recorded k-compatible nodal and natural dualizing data, correct
integer formulas, the explicit finiteness clauses, and exact component unions.
The first conclusion was narrowed to injectivity of the section inclusion to
match precisely the node's stipulated subspace. Empty S remains allowed but is
never automatically called subcanonical merely by D's empty-cluster convention.
No clause about splitting-index invariance has been added.
