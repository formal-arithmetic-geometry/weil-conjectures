## Worker report

The delivery states `AlgebraicGeometry.NodalNormalizationPicard.normalization_picard_sequence`
in `Sheaf.AlgebraicGeometry.NodalNormalizationPicardSequence`. Its only postponed theorem is
that declaration, with proof `sorry`. No definition obtains data from a postponed existence
theorem. The helper structures package the clauses of this single node; they introduce no
independent mathematical notion. There is no statement correction or disputed statement.

The signature takes an arbitrary universe `u`, an algebraically closed field `k : Type u`,
a scheme `C : Scheme.{u}`, its actual structure morphism `f`, properness, reducedness,
local finite presentation and `HasNodalGeometricFibres f`. The latter is the recorded
notion of nonempty connected dimension-one nodal geometric fibres, and thus supplies the
connected-curve hypothesis, including nonemptiness, rather than assuming an arbitrary graph
or an arbitrary collection of smooth curves. Local finite presentation is part of that
recorded dependency's definition. Over an algebraically closed field this is precisely the
nodal condition in the node, with its standard invariance under algebraically closed extension.

Clause-by-clause correspondence:

- The normalization is exactly `C.reducedNormalization`, not a supplied finite cover.
  `componentMap C i` is its coproduct injection followed by `C.fromReducedNormalization`,
  and `component f i` has source `(C.reducedNormalizationComponent i).normalization`.
  Its index is the actual `irreducibleComponents C`. These are the recorded constructions
  of `def-weil-pbc-reduced-normalization`.
- Existence of normalization geometry is `Nonempty (Branches f)`. Its
  `finite_components`, `finite_nodes`, `smooth`, `relative_dimension`, `projective`,
  `connected`, `curve`, `proper`, and `geometricallyIntegral` fields express the finite
  component and node sets and the smooth projective connected curve assertion. The last
  geometric properties spell out consequences of that assertion used to type the recorded
  Jacobian definition. No such facts are assumptions on the input curve.
- `Nodes f = {x : C // x ∉ f.smoothLocus}` is the actual node set. `Branches.index`,
  `point`, `section_eq`, `same_node`, `image`, `distinct`, and `exhaustive` encode an ordering
  of both normalization preimages at each node, over the field, on their actual components.
  `distinct` is in the total normalization, not a condition that their component indices
  differ. `exhaustive` says that precisely those two points lie over the node. The theorem
  supplies a sequence for EVERY such ordering: `∀ N : Branches f, Nonempty (Sequence N)`.
- `P_C` and each `P_i` are the recorded `picardFunctorGrp f` and
  `picardFunctorGrp (component f i).hom`. Their underlying set functors are exactly
  `picardFunctor`, the fppf sheafifications used in `sk-def-picard-pic`.
  `commutative` and `component_commutative` state commutativity with the existing group laws.
- Every unit parameter is an actual element of `Γ(T.left, ⊤)ˣ`, for arbitrary
  `T : Over (Spec (.of k))`. Restriction is `Units.map h.left.appTop.hom.toMonoidHom`.
  This is the big-site multiplicative group, not the small-etale constant sheaf.
- The diagonal is the displayed function `a ↦ fun _ ↦ a`; `diagonal_injective` states its
  injectivity, and `diagonal_kernel` identifies its image with the kernel of delta.
  Delta is written inline as the function
  `fun e : Nodes f ↦ a (N.index e 1) * (a (N.index e 0))⁻¹` in every unit group,
  in all three kernel clauses. It has the source and target orientation of the node.
- `glue T` is a homomorphism from edge parameters to the relative Picard group and
  `glue_natural` is its naturality. `glue_spec` requires an actual invertible module `L`
  realizing its class, with component frames satisfying `Glues N T z L`. `branchFrame`
  uses the existing canonical pullback-composition, pullback-congruence and unit comparisons.
  The compatibility equation says that the plus-frame relative to the minus-frame is
  multiplication by `z e`. Thus this map assigns exactly the gluing of trivial component
  lines specified in the node, and is not an arbitrary map satisfying an exactness predicate.
  In particular changing a frame by `a_i` changes the parameter by `a_+ / a_-`, with the
  orientation required in the statement.
- `restrict T`, `restrict_natural` and `restrict_spec` specify the normalization pullback
  map. On an actual line class it is `Scheme.Pic.map (componentBaseMap f T i)` followed
  by the canonical sheafification map. The base map is the recorded `pinchingBaseMap`.
  Naturality and the value on the locally generating line classes determine the sheaf map.
- `glue_kernel` and `restrict_kernel` identify the kernels with the fppf-local images of
  delta and glue, respectively. `restrict_epi` states fppf-local surjectivity. Together
  with the diagonal clauses these are precisely all places of the sequence
  `1 → Gm → Gm^I → Gm^E → P_C → product P_i → 0`.
  The `Sieve.generate ... ∈ (Scheme.fppfTopology.over (Spec (.of k))) T` expressions use
  the actual covering topology; they do NOT impose surjectivity on global sections.
- `jacobians`, `jacobian_groups`, `isJacobian`, `jacobian_rep`, and `jacobian_rep_mul`
  use `IsJacobian`, `picardFunctorDegree ... 0`, and `IsPicardZeroMul`. The representations
  are chosen existentially as part of the theorem's conclusion and include compatibility
  with the existing group laws. `B`, `projections`, `projections_group` and `product`
  specify an actual finite product of these group schemes by its limiting fan.
  `abelian : IsAbelianVariety B` is the asserted abelian variety property.
  `b_inclusion_spec` identifies the product inclusion using the existing
  `picardFunctorDegreeι` on every factor, rather than supplying an unspecified subgroup.
- `Q`, `q_group`, `q_finite_type`, `q_quasiCompact`, and `q_separated` supply an algebraic
  group representing the cokernel. `quotient` is natural on all test schemes;
  `quotient_kernel` identifies its kernel with the sheaf image of the specified delta,
  and `quotient_epi` states it is a sheaf epimorphism. These properties characterize the
  sheaf cokernel among group sheaves, without choosing an unspecified quotient object.
- `D`, `d_sheaf` and `d_space` supply a small group-valued representative and its property
  `AlgebraicSpace.IsAlgebraicSpace`. This uses the recorded algebraic-space definition
  directly. The small representative embeds by `d_inclusion` into the larger Picard
  functor; `d_inclusion_natural`, `d_inclusion_injective` and `inverse_image` identify its
  image with precisely `(nu*)⁻¹(B)` on EVERY test scheme. This retains all schemes in the
  big site while accommodating the existing Picard functor's `Type (u+1)` values.
  `d_commutative` is the commutative group law, and `d_smooth` states absolute smoothness
  on every representable etale scheme chart.
- `projection` is the morphism to `h_B`, is a homomorphism by `projection_mul` and
  `projection_one`, and is the required induced map by `projection_spec`.
  `projection_geometry` uses `AlgebraicSpace.IsRepresentableWith` with the conjunction
  `Smooth p.left ∧ Surjective p.left ∧ IsOpenMap p.left`, so each of the smooth,
  surjective and open clauses is present on every scheme base change.
- `local_sections` states that this projection has fppf-local sections.
  `kernel_inclusion`, `kernel_natural` and `kernel_spec` identify the kernel group with
  the specified cokernel `Q`, compatibly with the gluing map. The action is the explicit
  translation `kernel_inclusion T q * d`. `action_over` says this action is over `B`,
  and `torsor` says each two sections of a common fibre differ by a UNIQUE element of Q.
  Together with local sections this is equivalent to the specified fppf-local translation
  torsor: translating any local section gives a natural equivariant isomorphism with Q.

Dependency declarations read and used:

- `Field` and `IsAlgClosed` (Mathlib), and `IsProper` with its separated, universally
  closed, locally finite type signature (Mathlib.AlgebraicGeometry.Morphisms.Proper).
- `AlgebraicGeometry.HasNodalGeometricFibres`,
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: its full quantified geometric-fibre,
  connectedness, dimension and completed-local-ring signature and docstring were read.
- `AlgebraicGeometry.Scheme.reducedNormalizationComponent`, `reducedNormalization`, and
  `fromReducedNormalization`, `Sheaf.AlgebraicGeometry.ReducedNormalization`: read in full.
- `AlgebraicGeometry.picardFunctor` and `toPicardFunctor`,
  `WeilConjectures.AlgebraicGeometry.Picard.Defs`: the upstream closed declarations recorded
  in `sk-def-picard-pic.lean_audit.slopmaster2`, since that node has no separate lean record.
  The docstring and full signature establish fppf sheafification. The existing group
  encoding is `picardFunctorGrp`, with `picardFunctorGrp_comp_forget` and
  `toPicardFunctorHom`, in `WeilConjectures.AlgebraicGeometry.Picard.Group`.
- `AlgebraicGeometry.IsJacobian`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`: read its full signature,
  docstring and fields, including genus dimension and group-valued representation.
  `picardFunctorDegree`, `picardFunctorDegreeι`, and `IsPicardZeroMul` are the upstream
  definitions in `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`.
- `AlgebraicGeometry.IsAbelianVariety`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`: proper, smooth and connected.
- `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsRepresentableWith`, and
  `IsEtale` in `Sheaf.AlgebraicGeometry.AlgebraicSpace`: read the actual scheme-test
  pullback definition and the representable diagonal and etale-surjective-atlas clauses.
- The added statement dependency `def-sfb-pinching-line-data` is an ALREADY LANDED
  definition node providing `AlgebraicGeometry.Scheme.Modules.pinchingBaseMap` in
  `Sheaf.AlgebraicGeometry.PinchingLineData`. Its source and declaration were read.
  Adding this existing recorded definition dependency is authorized by brief-stage2 section 5.
  Delta is now the displayed inline formula; no graph theorem is imported or cited as a
  statement dependency.

The stated proof dependencies are imported as the stage-3 plan: finite pinching patching,
smooth connected curve local rings, proper global sections, flat base change of cohomology,
faithfully flat completion and tensor exactness, proper and smooth permanence, geometric
connectedness of products, and upstream Picard/Jacobian existence. Dependencies with no
recorded declaration (`lem-sfb-nodal-completed-normalization-model`,
`lem-trf-split-lattice-torus-projection`, and
`lem-sfb-smooth-affine-group-torsor-representability`) have no module to import; they are
proof-only dependencies, not missing notions needed to type this statement. Their proof
roles remain explicitly named in the seven-step theorem docstring.

Edge cases checked before and during writing:

- A smooth connected curve has no nodes and one normalization component. Empty edge
  parameter products and the trivial quotient group are admitted; no branch is demanded.
- A tree of components gives trivial Q. The exactness clauses use local images and so
  do not incorrectly assert that all line classes lift globally over every base.
- An irreducible self-node has both branch indices equal. No inequality between them is
  assumed: the two points in the normalization are distinct and delta is 1 on that edge.
- Multiple edges and reversed orientations are allowed. Reversal inverts the unit parameter.
- Arbitrary disconnected or nonreduced base schemes, and the empty test scheme, are included.
  For the empty test scheme every group of sections has its unique element, as required.
- The empty input curve is excluded by the node's nonempty connected curve convention,
  already built into HasNodalGeometricFibres. No accidental extra field-characteristic,
  genus, component count, rational basepoint, or universe equality is imposed.
- The D representative is Type u, but it is related by an injection and exact image
  characterization to the full Type (u+1) Picard sheaf, with no restriction of the base site.

Searches (all via the prescribed search wrapper, or read-only rg):

- LeanFinder: `Normalization of a nodal curve exact sequence of Picard fppf sheaves and
  gluing torus`: eight results, all general normalization declarations; no Picard sequence.
- Loogle: `picardFunctor, IsJacobian, HasNodalGeometricFibres`: zero results,
  unknown identifier picardFunctor in Mathlib.
- Mathlib grep: `[Nn]odal.*[Pp]icard|[Pp]icard.*[Nn]ormal|[Gg]luing.*[Pp]aram`,
  subdirectory AlgebraicGeometry: zero hits.
- LeanSearch: `relative Picard functor normalization nodal curve gluing exact sequence`:
  eight general normalization and gluing declarations, none stating this sequence.
- Read-only rg of WeilConjectures and Sheaf for nodal/Picard/normalization/gluing parameters
  found the existing graph helper and general Picard definitions, not this theorem.
  The mandated search for this blueprint id under WeilConjectures returned no match.
- Additional concept searches for units functors, branch-frame comparisons, Picard maps,
  finite pinching, smooth group spaces and scheme group functors selected existing APIs.
  `tools/blueprint_refs.py ancestor` reports the inherited ancestor is null; no new node
  is created. The existing algebraic-space and Picard definitions remain authoritative.

Validation: the prescribed scompile.py compiled the complete module both as a sandbox file
and under its intended library module name, cleanly with no errors or warnings. Only the
main theorem uses sorry; definitions and statement packages have real data.

## Returned delivery repair

The maintainer returned immutable head `0da9e85a8bf5` for H2/H3: the statement dependency
`lem-sfb-finite-graph-cycle-character-quotient` owned a theorem, while this delivery used
only its plain coboundary definition without a definition-node owner. Applied the explicitly
authorized inline alternative: replaced all three coboundary applications in
`diagonal_kernel`, `glue_kernel`, and `quotient_kernel` by
`fun e : Nodes f ↦ a (N.index e 1) * (a (N.index e 0))⁻¹`, removed the graph module import,
and removed that theorem id from `stmt_deps`. No new node or declaration is needed.
The formula retains the exact plus/minus orientation, including self-nodes.

Rebased the sandbox node on the current main node, retaining its current metadata and the
reviewed `statement`, `proof` and `proof_deps` verbatim. Its only statement-dependency addition
is the already landed definition `def-sfb-pinching-line-data`. The main theorem signature
and every other conclusion field remain unchanged. The report's clause mapping and dependency
list above describe the repaired module. The full module is compiled again and the prescribed
dry run and delivery are rerun for this repair.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
