## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ChevalleyUnipotentPolynomialCoordinates`
states `AlgebraicGeometry.ChevalleyCoordinates.unipotent_polynomial_coordinates`.
Only its theorem proof is sorry. There are no statement corrections, dependency repairs,
or new independent notions. The five helper definitions are the concrete objects occurring
in this node: the weight torus, integral divided-power matrices, their finite exponentials,
ordered products, and affine coordinate points. They use existing group algebras, matrices,
linear-map restriction and affine Spec, with real data throughout.

Hypothesis and clause correspondence:

- The rational vector space is `V` with `AddCommGroup`, `Module ℚ`, and
  `FiniteDimensional`. `R`, `c`, `hfinite`, `hne`, `hspan`, `htwo`, `hint`, `hreflect`,
  `hreduced` are precisely the explicit rational root-system conventions of
  `RootDatumLattice.lattice_embedding`, also used in the admissible representation.
  `P`, `hP` specify the full integral weight lattice, not an arbitrary sublattice.
- The split semisimple Lie algebra is `g` with its Lie structures, finite dimension and
  `hsemi`. `H`, `hab`, `hmax`, `θ`, `he`, `hdecomp` give the Cartan, dual identification,
  root eigenvectors, and Cartan/root direct sum. The root eigenbasis makes the adjoint
  Cartan action simultaneously diagonalizable. `B`, `hB`, `hopposite`, `hbracket`,
  `hzero` spell out the Chevalley-basis and root-string constants of the dependency.
- The simple-root base is `simple` with `hsimple`, `hbase`: it is a rational basis,
  its members are roots, and every root has integral coefficients of one sign.
  `neg`, `hneg` merely name the uniquely determined opposite root, already guaranteed
  by the root-system axioms; they add no extra structure or root-system restriction.
- `W` with its Lie-module structures and finite dimension is the representation;
  `hfaithful` is faithful. `Λ` is an actual full lattice (`Submodule.IsLattice ℚ Λ`)
  and is free. `Ω`, `hweights`, `hweightSum`, `hgenerate`, `hlatticeSum` state exactly
  the nonzero weight spaces, their rational direct sum, generation of P, and integral
  weight decomposition. `hnil` and `hstable` give nilpotence and preservation by EVERY
  divided power, including degree zero. No special choice of the representation is made.
- `b` is any homogeneous integral lattice basis, with labels `weight` and membership
  `hhomogeneous`. This is an auxiliary coordinate choice, not a restriction: full finite
  freeness and the integral direct sum provide such a basis by choosing a basis in each
  weight intersection and concatenating them. Weight intersections are free as subgroups
  of a finite free abelian group. The conclusion holds for every such basis. `ULift (Fin d)`
  places its index in the field universe as required by the existing GL scheme API;
  it does not impose a positive dimension or equality of independent mathematical sizes.
- `β : Fin N ≃ {a : R // ∀ i, 0 ≤ simple.repr a i}` enumerates precisely the positive
  roots, so N is their cardinality. `horder` allows EVERY order refining height (the sum
  of the simple-root coefficients), with no ordering restriction at equal height.
- `F`, `Field F`, `IsAlgClosed F` give the prescribed algebraically closed field.
  `weightTorus P F` is Spec F[P] using `AddMonoidAlgebra`, with its standard Hopf
  structure (basis addition, diagonal comultiplication, counit one, antipode negation).
  `torusEmbedding` is characterized by its diagonal weight characters on every algebra;
  the weights used in `AddMonoidAlgebra.single` are placed in P using `hweights`.
  The statement also records its closedness, the embedding supplied by ZΩ=P.
- `dividedMatrix` restricts the rational divided power to Λ USING `hstable`, then takes
  its integer matrix in b. `rootMatrix` reduces these integer coefficients only after
  taking divided powers. Its sum runs through `nilpotencyClass E + 1`: the final term
  is zero; this also handles the zero endomorphism algebra without deleting the
  degree-zero term in an ordinary nonzero representation. Thus it is the node's
  finite polynomial x_alpha over every characteristic, not an exponential using
  factorial inverses in F. `orderedProduct` multiplies in `List.finRange N` order.
- The two arrows `pPlus`, `pMinus` have source Spec F[b_i] = affine N-space and target
  the actual general linear group scheme. Their displayed equalities, for every
  `A : Type u`, `[CommRing A]`, `[Algebra F A]`, and coordinate tuple a, identify the
  first with the β-root ordered product and the second with the opposite-root product.
  `parameterPoint` is Spec of `MvPolynomial.aeval a`, not an arbitrary parametrization.
  Quantification uses the SAME universe as F, so test-algebra conditions cannot become
  vacuous by placing the algebras in a universe smaller than the field.
- `IsClosedImmersion pPlus.left` and its minus counterpart are scheme-theoretic
  closed immersions. For every A the two ranges are sets underlying `Subgroup`s.
  Together these are exactly the definition of closed subgroup schemes in the node
  and in `IsClosedSubgroupScheme`'s docstring: a closed subscheme whose points over
  EVERY algebra form subgroups. This does not assert only closure of F-valued points,
  or assume a group law on affine space is componentwise addition. A closed immersion
  identifies the source with its closed image; the group law on that image is the
  uniquely induced law. It need not be included as an extra chosen structure.
- The `q` clause quantifies over every rational linear functional positive on all
  simple roots and injective on Ω. For pPlus, whenever the row's q-value is at most
  the column's, its entry equals the identity-matrix entry. In DECREASING q order
  this is exactly identity diagonal blocks and zero blocks below them. For pMinus
  the reversed inequality gives identity blocks and zeros above. Equal q-values
  mean equal weights by separation, so the whole diagonal BLOCK is the identity,
  including distinct vectors in a weight space. No total order on basis vectors
  inside an individual weight space is imposed or needed.
- The last clause explicitly says R empty implies N=0 and both products, over EVERY
  A and parameter tuple, equal the identity. Combined with closedness, this is the
  identity closed subgroup. No reductive generated group appears among hypotheses.

Dependency declarations read and used:

- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`, `RootDatumLattice.lattice_embedding`:
  explicit rational root axioms and weight-lattice convention; transitively publicly
  imported through the representation module. No private replacement of its root span
  or weight lattice is introduced; the arbitrary rational V uses the same explicit axioms.
- `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`,
  `LieAlgebra.exists_chevalley_admissible_representation`: full signature and proof plan
  read. This theorem supplies existence, while the present node concerns ANY data with
  precisely those conditions; hence its existential conclusions are unpacked as binders.
- Mathlib `Field` (`Algebra/Field/Defs.lean`) and `IsAlgClosed`
  (`FieldTheory/IsAlgClosed/Basic.lean`): the latter is polynomial splitting, equivalent
  to the node's root condition. `AlgebraicClosure` is not needed because F itself is given.
- `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`, the group-object
  interpretation in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, and that module's
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`: read their complete signatures/docstrings.
  The existing GL group object and the documented closed-subscheme/all-points criterion
  are used; no replacement definition of a subgroup scheme is introduced.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`,
  `AlgebraicGeometry.StandardGroupSchemes.affine` and `.map`: the actual relative
  spectra and Spec of algebra maps, also underlying the dependency's additive group.
  No additive group homomorphism condition is imposed on the multi-root products.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, with its exact closed embedding/stalk definition.
- `Mathlib.LinearAlgebra.RootSystem.BaseExists` supplies the stated proof dependencies:
  `RootPairing.Base.mk'`, `.toWeightBasis`, `.toCoweightBasis`, `.span_int_root_support`,
  `.span_int_coroot_support` and `.induction_reflect` in its imported Base module. Read
  their signatures and source docstrings. They are non-public proof-plan imports.
- The other proof dependency `lem-sfb-chevalley-nonopposite-exponential-commutator` has
  neither a recorded Lean module nor a Mathlib match in the read clone, so there is
  no proof-only module to import. It remains in the theorem's proof docstring and DAG.
  It is not needed to elaborate the present statement. No import cycle is introduced.

Additional existing interfaces: `GeneralLinearGroup`, `.homMulEquiv` (actual GL scheme
and all-algebra matrix interpretation); `LinearMap.restrict`, `.toMatrix`;
`nilpotencyClass`; `MvPolynomial.aeval`; `AddMonoidAlgebra` and its Hopf instances.
Their signatures were read in the pinned source. Helpers are all explicit constructions
of this node's own displayed objects, not new independent definitions requiring nodes.

Edge cases checked before writing: empty R forces V=0 and the positive-root enumeration
has N=0; d=0 uses the unique empty matrix (identity and zero coincide); a representation
with a zero-weight summand is allowed; repeated dimensions within a weight are included
by block rather than scalar triangularity; arbitrary equal-height root orders are allowed;
characteristics 2 and 3 use integral divided coefficients without inverting factorials;
A may be nonreduced or even the zero ring. No Nontrivial A is assumed. Zero parameters
and the degree-zero divided power are retained. q need not be supplied or chosen in
advance; the assertion concerns every positive separating q, as in the node.

Searches for an existing statement (all via the prescribed msearch wrapper):

- leanfinder: “Ordered Chevalley root exponentials are closed affine space coordinates
  on unipotent subgroup schemes”: eight hits, affine coordinate maps and Geck Lie
  construction; no theorem about closed ordered root-exponential subgroup charts.
- loogle: “RootPairing, GeneralLinearGroup, IsClosedImmersion”: no hits; Loogle reported
  unknown identifier GeneralLinearGroup. This did not supply an existing match.
- leansearch: “Closed immersion of affine space into general linear group from ordered
  root exponentials”: eight hits, the general closed-immersion definition and criteria,
  no exponential product statement.
- grep (Mathlib): `unipotent.*(coordinate|exponential)|chevalley.*polynomial|Chevalley.*exponential`:
  six hits, all unrelated Chevalley constructible-image polynomial complexity results.
- Direct rg in live `lean/WeilConjectures` and `lean/Sheaf` for Chevalley, root exponential,
  polynomial coordinates and the node ID found only related supporting modules or proof
  references (not this theorem). The integral root model cites this node in its proof;
  it does not prove or state its arbitrary-admissible-representation conclusion.
  The upstream names index has no entry for this node ID.

Source read: the current blueprint unit `sk-thm-sf-ctf-stability/_section.md` and Milne
PDF pp.510--511, extracted directly from the PDF, including equation (153), omitted
proof details of 23.72, 23.73, and Notes. The node is the explicit agent-expanded
supporting lemma, not the blueprint unit's own assertion. No source correction is needed.

## Second reading by O1

Dispatcher instruction requires this worker to deliver directly and forbids starting
other agents. This is therefore an in-thread second reading, not an independent-agent
review; the maintainer's independent review remains the separate check.

Re-read the node and complete module against every item above. Fixed two issues during
this reading: auxiliary unconnected group-law witnesses were removed in favour of the
node's exact closed-subscheme/all-algebras subgroup criterion, and the stated torus was
included explicitly with its canonical character formula. The lower-block inequality is
reversed relative to the upper clause, and equality fixes whole diagonal blocks. The
negative product uses the SAME β order, through `neg`, not a reversed order. The matrix
index is universe-lifted to match the existing GL API without restricting F. No axiom or
hypothesis of reductivity, invertibility of factorials, or restriction to rational points
was added. Every given representation is covered, not just the one constructed by the
admissible-representation existence theorem. All definitions have real data and all
variables/universes are explicit. The single sorry is the named node theorem with the
entire ten-step proof plan in its docstring.
