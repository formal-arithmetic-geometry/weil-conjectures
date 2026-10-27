## Worker report

The module states `AlgebraicGeometry.RelativeDynamic.relative_dynamic_subgroups`, with
exactly one postponed theorem and explicit definitions for every auxiliary construction.
The original statement, proof and proof dependencies are unchanged. The statement
imports the already-landed ring multiplicative group and geometric unipotence
terminology, adding their definition nodes to `stmt_deps`. There are no new DAG nodes
and no dependency repairs. The helper declarations are parts of this one theorem's
notion, as authorized by the brief's missing-helper rule, and all appear in
`lean.declarations`. In particular `Diagram` packages existential witnesses; it does
not select any unknown group scheme. `Diagram.baseChange` explicitly pulls back all
its entries, including the product isomorphism and conjugation map.

The source was opened: Conrad, Reductive group schemes, Theorem 4.1.7, printed
pp.112--114, especially the general action formulation and the paragraph following
Example 4.1.9. It covers arbitrary rings and actions, rather than just cocharacters
or reductive groups. The local example CompactObject module is withdrawn; its node
now points to the upstream CompactObject module, which was read for the active header
and namespace convention.

Hypothesis and clause correspondence:

- A commutative ring R and X = Spec R: `(R : Type u) [CommRing R]` and the base
  `Over (Spec (.of R))`. No nonzero, Noetherian, local, field or characteristic
  restriction is imposed.
- G is a group scheme: `G : Grp (Over (Spec (.of R)))`. Its multiplication, unit,
  inverse and group diagrams are the recorded Mathlib group-object construction.
- G is smooth affine of finite presentation: `[IsAffine G.X.left]`,
  `[Smooth G.X.hom]`, `[LocallyOfFinitePresentation G.X.hom]`. Since its base and
  total scheme are affine, G is quasi-compact and separated over R, so this is
  precisely finite presentation, not merely a local substitute.
- The multiplicative group is the already-landed `RingGroupSchemes.multiplicative R`,
  whose underlying scheme is Spec R[t,t^-1] with the Laurent Hopf group operations.
- The action is `[ModObj ... G.X]`, supplying a scheme morphism and the unit and
  associativity diagrams. `hAut` says it preserves multiplication on every test
  scheme; inverse elements of G_m give inverse automorphisms. Thus it imposes no
  choice of a cocharacter or representation over R.
- The negative action is `oppositeAction`: precompose with `GrpObj.inv` in the
  first factor. This is exactly a(t^-1,g).
- `IsOrbitExtension` says the morphism W times A^1 to G restricts on W times G_m
  to the orbit morphism. `puncturedLine` is Spec of the polynomial-to-Laurent map,
  and `zeroSection` is Spec of evaluation at zero, with its canonical base map.
- `parabolicPoints` requires such an extension. `unipotentPoints` requires also
  that its zero value is the identity. `fixedPoints` tests equality after every
  further test scheme V to W and every V-point of the acting torus. In particular
  this tests every algebra extension and every unit, not merely rational points.
  For affine schemes these predicates on all schemes are the same functors as
  their restrictions to test algebras: the conditions are local on affine opens.
- The existential `Diagram` supplies P,U,Z,V (where V is U for the negative action)
  and their group homomorphisms into G. `Structural` states each inclusion is a
  closed immersion and its image on every test scheme is exactly the specified
  subfunctor. A closed immersion is a monomorphism, so the image formulation is
  representability with unique lifts, not only a surjectivity assertion.
- `Geometric` requires affine, smooth, locally finitely presented subgroup schemes.
  Their affineness over the affine base again supplies finite presentation.
- Evaluation at zero is the group homomorphism `D.q`. The clause quantifying over
  every orbit extension identifies its image with that extension's zero value.
  `D.zP ≫ D.q = 𝟙 D.Z` gives the retraction. The pointwise kernel clause identifies
  the kernel with U on every test scheme, hence scheme-theoretically. The normal
  range clause states U is normal in P on every such scheme.
- `D.productIso : D.Z.X ⊗ D.U.X ≅ D.P.X`, with its displayed composite into G,
  identifies the map with (z,u) maps to zu. `D.conjugation` is z^-1 u z, and the
  point multiplication formula is (z,u)(z',u') = (zz', z'^-1 u z' u'), the group
  law in exactly this factor order. The isomorphism is in schemes over the base;
  the formula makes it an isomorphism with the semidirect group law.
- The last clause of `Structural` is `IsOpenImmersion` for multiplication V times
  P to G; it is the actual product of the two inclusion morphisms followed by
  G's multiplication.
- `Geometric` uses Mathlib `GeometricallyConnected D.U.X.hom` for connectedness of
  every geometric fibre. For each algebraically closed field and each map from
  its spectrum to the base, it applies the existing
  `SolvableGroupStructure.IsUnipotent` to the actual pulled-back U. This means a
  faithful closed matrix representation with unipotent geometric matrices. No
  representation of G over R is hypothesized. The implication from geometric
  connectedness of G supplies the claimed connectedness of P and Z.
- `homogeneous` is the universal function equality f(a(t,g)) = t^n f(g) in the
  coordinate ring of G_m times G; it uses the entire character t^n, with no
  reduction of n modulo a residue characteristic.
- `parabolicIdeal` is the ideal generated by homogeneous negative functions;
  `fixedIdeal` uses nonzero degrees. `unipotentIdeal` adds f-epsilon(f) in degree
  zero, with epsilon composed back into R[G] along G's structure morphism.
  `CoordinatesAndTangents` identifies these ideals with the kernels of the
  actual inclusion maps on global sections. Closed immersions between affine
  schemes are the spectra of these coordinate quotient maps.
- Tangents use the existing `GrpObj.Lie`, its R-module instance and
  `GrpObj.tangentPoint`. `tangentCoefficient` extracts the epsilon coefficient of
  a function's pullback to R[epsilon]. `weightSpace n` consists of derivations
  vanishing on every homogeneous component other than n: this is precisely the
  coaction weight n, since homogeneous functions span R[G] and their action is
  t^m. It is written as a span of that linear subspace, which changes nothing.
  `tangentImage` is the span of actual dual-number compositions with an inclusion;
  composition by a group homomorphism is linear, so this is the actual image.
- `DirectSum.IsInternal (weightSpace ...)` states the integer-character internal
  decomposition. The three displayed submodule equalities in
  `CoordinatesAndTangents` state Lie(Z) = g_0, Lie(U) = supremum of positive
  weight modules, and Lie(P) = supremum of nonnegative weight modules. Internal
  directness makes these suprema exactly the indicated direct sums, with their
  actual inclusions into Lie(G).
- `StableUnderBaseChange` quantifies over every R-algebra B, including nonflat
  ones, and then every B-algebra C. `BaseChangeConclusions` states all structural,
  geometric, coordinate and tangent conclusions for the literal pullback diagram,
  pulled-back action and characters. The zero section and product maps use the
  canonical monoidal pullback comparisons. This includes all inclusions, q,
  conjugation, semidirect isomorphism and open multiplication, not just existence
  of unrelated subgroups over the new ring.
- `TangentBaseChange` gives linear equivalences B tensor Lie(H) to Lie(H_B) for
  G,P,U,Z. `IsTangentComparison` fixes each equivalence on 1 tensor v by its
  actual dual-number point over the canonical map R[epsilon] to B[epsilon].
  Linearity determines it on all elementary tensors, so it is the canonical
  comparison. Its weight-image clause identifies precisely the scalar-extended
  weight submodules. Weight modules are split summands of the internal direct
  sum, so their tensor inclusions remain injective even for nonflat B.
- Successive compatibility is encoded by taking the literal second pullback and
  repeating the same conclusions and canonical tangent normalizations. The
  comparison with direct base change is `Over.pullbackComp`. On ring functions
  and on normalized dual-number points the composites are the same pullback;
  linearity and pure tensors determine the tangent maps. Thus no arbitrary
  isomorphism or arbitrary comparison map is hidden in this assertion.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`, `Spec.map`.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, `Grp`, its internal
  multiplication and inverse. This definition applies over any base scheme,
  although def-sc-group-scheme specializes it to a field.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`; its geometric version is
  Mathlib.AlgebraicGeometry.Geometrically.Connected, `GeometricallyConnected`.
- Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing:
  `RingGroupSchemes.multiplicative` (def-sfb-split-torus-over-ring).
- Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  `SolvableGroupStructure.IsUnipotent` (def-sfb-solvable-group-structure).
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring: existing `GrpObj.Lie`
  with its ring module structure, `GrpObj.tangentPoint`, `points.map`,
  `tangentGroup`, `mem_tangentGroup`, and the dual-number bridge.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Mod: `ModObj` and its point action.
- Mathlib.Algebra.DirectSum.Internal: `DirectSum.IsInternal`.
- Proof-only imports retain the plan: AffineFormallySmooth, GmRepresentationWeightBasis,
  TransverseSubgroupProductOpen, LocallyAlgebraicGroupIdentityComponent,
  Mathlib.RingTheory.Kaehler.TensorProduct, Morphisms.RingHomProperties and
  RingTheory.Smooth.Basic. The recorded signatures/docstrings were read. Proof
  prerequisites without Lean records are not imported or assumed as hypotheses.

Edge cases checked before and during drafting: R = 0 and empty Spec R are allowed;
geometric assertions then have no field-valued base maps and are vacuous, as they
should be. The trivial action gives P = Z = G and U = V = 1. A trivial group has
zero tangent module and all weights zero. An action with all weights zero requires
no positive summands. Positive-characteristic weights p and 0 are distinguished by
the Laurent monomials, not a differentiated scalar. Nonreduced tests use scheme
morphisms and all algebra extensions. Identity base change, quotient/nonflat base
change and a successive algebra extension are explicitly included. Every universe
and variable is explicit (`autoImplicit false`); all tests lie in the ring's
universe, with no independent smaller test universe.

Searches (all returned no exact existing statement):

- `msearch.py leanfinder`, query "smooth affine group scheme multiplicative action
  dynamic parabolic unipotent centralizer subgroups": eight unrelated hits on
  2-by-2 matrix parabolics, modular subgroup regularity and Iwasawa actions.
- `msearch.py loogle`, query "GrpObj, LaurentPolynomial,
  AlgebraicGeometry.IsClosedImmersion": no hits; unknown identifier GrpObj.
- `msearch.py leansearch`, query "relative affine group scheme multiplicative action
  dynamic subgroups": eight hits on abstract pointwise subgroup actions, no
  scheme-theoretic relative dynamic theorem.
- `msearch.py grep`, query `dynamic|attracting|cocharacter|parabolic`, in
  AlgebraicGeometry: zero hits. Second grep `ModObj|tangentPoint|tangentGroup`
  also returned zero Mathlib hits; the upstream source search supplies the latter.
- `rg` of both project roots for dynamic/attracting/cocharacter/GmAction and the
  item id: no exact theorem. The cocharacter-limit theorem found in
  Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure is over an algebraically
  closed field with connected G and a conjugation action; it cannot be used as
  the arbitrary-ring, arbitrary-action statement here. Its full signature and
  helper definitions were read. StandardGroupSchemes is likewise field-only;
  the already-landed ring multiplicative group is used instead.
- Further `rg` searches found and reused Lie.Ring, Cartesian.Mod, GeneralLinear,
  geometric connectedness and the existing geometric unipotence predicate.
  No independent copy of a group scheme, Lie module, multiplicative group or
  geometric unipotence notion is introduced.
- `tools/blueprint_refs.py search 'dynamic subgroup'`: zero blueprint matches;
  DAG relative-dynamic-subgroup and relative-tangent-weight nodes were inspected.
  They are unstated theorem nodes, not alternate definitions needed to state this
  theorem. The theorem uses elementary helper predicates for its own clauses.

Validation: `scompile.py` compiled the module both as the sandbox file and under
its actual module name. A single unused-variable warning in the explicit dual-map
construction was repaired; compilation then passed with no warnings. Every
definition has real data, and the only theorem proof is `sorry`. No node fault or
STATEMENT-DISPUTED flag remains.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
