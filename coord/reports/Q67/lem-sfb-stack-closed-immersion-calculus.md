## Worker report

The module `Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus` states all four
assertions of `lem-sfb-stack-closed-immersion-calculus` in four named theorems.
Each proof is `sorry`; no definitions, constructions, axioms, or instances are added.
Only the item's `lean` field changes. The source statement needs no correction.
There are no new nodes or dependency modules.

The source was read in `literature/stacks-project/stacks-properties.tex` at
`definition-immersion`, `lemma-base-change-immersion`,
`lemma-composition-immersion`, and `lemma-subspace-induced-topology` (Tags 04YL,
0501, 0502, 0H20), and in `stacks-morphisms.tex` at
`lemma-immersion-locally-finite-type` and `lemma-composition-finite-type`
(Tags 06FV and 06FT). The first source defines representable closed immersions,
proves the two stability statements, and states the topological conclusion.
The second supplies the final finite-type implication. Each theorem's docstring
contains the corresponding full argument of the node, with its prerequisites.

Hypotheses and clauses are rendered as follows.

- The base scheme is `{S : Scheme.{u}}`. Each of Z, X and Y is a
  `BasedCategory.{vᵢ, wᵢ} (Over S)`; its algebraic-stack hypothesis is explicitly
  `IsAlgebraicModuliStack`. The universes for their objects and morphisms are
  separate and explicitly declared. No Deligne--Mumford, representability of an
  arbitrary base-changing map, separation or quasi-compactness assumption is added.
- A stack morphism is a `BasedFunctor`. The closed immersion assumption is the
  existing `ModuliSchemeTest @IsClosedImmersion i`. Its full definition quantifies
  over every scheme `T : Over S` and map `h_T → X`, produces `R : Over S`, its
  projection `p : R ⟶ T`, and an equivalence from `h_R` to the ACTUAL
  `moduliTwoFiberProduct t i`. `IsSchemeModuliBaseChange` retains a 2-isomorphism
  identifying its projection with `p`. Finally `IsClosedImmersion p.left` is
  precisely the node's scheme closed immersion condition. Thus neither the
  representing scheme nor its projection is replaced by arbitrary data.
- `stack_closedImmersion_baseChange` takes an arbitrary `a : BasedFunctor X Y`
  and a closed immersion `i : BasedFunctor Z Y` between algebraic stacks.
  It concludes `ModuliSchemeTest @IsClosedImmersion (moduliTwoFiberFst a i)`.
  This is the actual projection `X ×_Y Z → X`, using the recorded 2-fibre product.
- `stack_closedImmersion_comp` assumes both `i : Z → X` and `j : X → Y` pass
  that same scheme test and concludes it for `i.comp j`, the composite Z → Y.
- `stack_closedImmersion_topology` assumes the same closed immersion between
  algebraic stacks and concludes
  `Topology.IsClosedEmbedding (moduliPointMap i) ∧ IsClosedMap (moduliPointMap i)`.
  The first conjunct says the induced map is a homeomorphism onto a closed subset.
  The second states exactly that every closed subset has closed image. The map
  is the existing field-object quotient map, and the topology is the existing
  `moduliPointTopologicalSpace` of the recorded flat-lfp-openness dependency.
- `stack_closedImmersion_locallyFiniteType` binds `(k : Type u) [Field k]` and
  works in `Over (Spec (.of k))`, exactly specializing S to Spec k. Z and X are
  algebraic stacks and `i : Z → X` is a closed immersion. `hXft` is the existence
  of `U : Over (Spec (.of k))` and a map `p : h_U → X` such that
  `IsSmoothModuliAtlas X U p ∧ LocallyOfFiniteType U.hom`. This is the node's
  smooth-chart test of local finite type over k. Its conclusion is the identical
  existence condition for a scheme V and a smooth surjective atlas `q : h_V → Z`,
  with `LocallyOfFiniteType V.hom`. The statement does not substitute the
  DM-specific étale atlas predicate or the representable-map finite-type test.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  and `AlgebraicGeometry.Spec` (source of the recorded scheme and affine-spectrum
  definitions); the field binder uses Mathlib's `Field`, read in
  `Mathlib/Algebra/Field/Defs.lean`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the recorded closed-immersion definition;
  also `AlgebraicGeometry.IsClosedImmersion.comp`, the exact match for the scheme
  composition proof dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the recorded affine-local finite-type
  definition, applied to the atlas's structural morphism.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` and `CategoryTheory.IsSmoothModuliAtlas`.
  Their full definitions retain étale descent, algebraic-space diagonal and
  actual smooth surjective scheme base-change projections.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.moduliTwoFiberProduct`, `CategoryTheory.moduliTwoFiberFst`,
  `CategoryTheory.discreteModuli`, `CategoryTheory.ModuliTwoIso` and the stack
  vocabulary used through the algebraic-stack definitions. The fibre product
  retains the invertible comparison morphism over the identity on the base.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliSchemeTest`, `CategoryTheory.ModuliPoints`, and
  `CategoryTheory.moduliPointMap`. Despite the module name, the scheme test and
  field-object constructions are defined for general based categories. No
  DM hypothesis is used. `IsSchemeModuliBaseChange` was read in its owning module
  `Sheaf.AlgebraicGeometry.ModuliChartNormalization`; it specifies equivalence
  and the projection comparison, not merely existence of an unrelated scheme.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliPointTopologicalSpace` and the recorded
  `CategoryTheory.stackPointTopology_flat_lfp_open`, including continuity.
- Plain proof imports:
  `Sheaf.AlgebraicGeometry.StackPointTopology` (`CategoryTheory.stack_point_topology`)
  and `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`
  (`CategoryTheory.stack_chartwise_smooth_etale_calculus` and its surjectivity
  calculus). These are proof dependencies, not new assumptions.
  `lem-sfb-algebraic-stack-fibre-products` currently has no Lean record or
  Mathlib match, so it has no import yet, as required for unstated proof
  dependencies. No object from that unstated theorem is needed to type the
  existing 2-fibre-product scheme test in this delivery.

Edge cases checked before writing:

- Empty stacks, empty test schemes and empty closed substacks are allowed; no
  nonemptiness binder appears. Empty images are closed and the empty-source
  map satisfies the claimed closed embedding conclusion.
- Identity and isomorphism closed immersions give the expected identity and
  isomorphism base changes, composites and point embeddings.
- Arbitrary base change is retained: a need not be smooth, flat, representable,
  surjective or locally of finite type.
- Nilpotent thickenings are allowed: the point map may be a homeomorphism even
  though the stack map is not an equivalence. Only the closed immersion scheme
  test, not an equivalence assumption on i, occurs.
- The field may have any characteristic, need not be algebraically closed, and
  has no perfection assumption. The atlas need not be quasi-compact.
- A closed immersion need not be finitely presented: the finite-type conclusion
  uses only the finite generation of A/I as a k-algebra from that of A. No
  finite generation condition on the defining ideal is present.
- Independent universes are retained for the three stack categories; scheme and
  test-field universes use the existing convention u. No equality of object and
  morphism universes is imposed.

Searches for existing statements and notions (2026-10-24):

- `msearch.py`, LeanFinder query:
  `Closed immersions of algebraic stacks are stable under arbitrary base change and composition and induce closed embeddings on underlying point spaces`.
  Eight hits, all scheme results: scheme multiplicativity, base-change stability,
  closed embeddings and universal closedness. No stack theorem matching the node.
- `msearch.py`, Loogle query:
  `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFiniteType`.
  One hit: `AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion`, a scheme
  result, not any of the required stack assertions.
- `msearch.py`, grep query:
  `AlgebraicStack|closedImmersion.*[Ss]tack|[Ss]tack.*closedImmersion`.
  Zero hits in Mathlib.
- `msearch.py`, LeanSearch query:
  `Closed immersions of algebraic stacks induce closed embeddings on point spaces and are stable under base change and composition`.
  Eight scheme hits, including `IsClosedImmersion.isStableUnderBaseChange`,
  `IsClosedImmersion.comp`, and `Scheme.Hom.isClosedEmbedding`; no matching stack
  theorem.
- `rg` in `lean/WeilConjectures` for the item id and for
  `closedImmersion.*[Ss]tack|[Ss]tack.*closedImmersion|IsClosedModuli` found no
  existing declaration for this statement.
- `rg` in `lean/Sheaf/AlgebraicGeometry/*Stack*.lean` for closed immersion and
  finite-type notions found scheme statements, the general `ModuliSchemeTest`
  and relative DM finite-type predicates, and an existing use of
  `ModuliSchemeTest @IsClosedImmersion` for a diagonal in
  `StackProperLocallyQuasiFiniteComposition`. That confirms reuse of the scheme
  test. The smooth atlas local-finite-type condition also already appears
  explicitly in `StackVersalFiniteResidueExtension`; it is rendered directly
  here, without introducing a second predicate for it.
- Exact-name `rg` across Mathlib, `lean/WeilConjectures` and `lean/Sheaf` for all
  four `stack_closedImmersion_*` names found no collision before writing.

Validation: the complete delivered module was compiled using the prescribed
`scompile.py Q67 lem-sfb-stack-closed-immersion-calculus` wrapper, in module mode
against the live published library. Both the sandbox and library-name checks
passed (3.5 s and 3.6 s respectively), with no errors or unexpected warnings.
Every universe and variable is explicitly bound and `autoImplicit` is false.
No line exceeds 100 characters. A node comparison confirms that only `lean`
changed; the natural-language statement and all dependency lists are verbatim.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
