## Worker report

The module `Sheaf.RepresentationTheory.FiniteScalarCochainRetraction` states
`ContinuousCohomology.exists_finiteScalarCochainRetraction`, with its one proof
`sorry`. The helper structure `ContinuousCohomology.ScalarCochainRetraction`
packages the six prescribed maps and their properties. It is an interface belonging
to this node, not a second construction of the coefficient or cochain spaces.
No definitions have postponed data, and no other theorem is introduced.

The node's statement and all fields other than `lean` are unchanged. No new
nodes, dependency repairs, or statement correction are required.

Hypothesis-by-hypothesis correspondence:

- The fields E, F, L are independent universe types with `[Field]`. The inclusions
  are `[Algebra E F]`, `[Algebra F L]`, `[Algebra E L]` and
  `[IsScalarTower E F L]`. Field algebra maps are injective, so this encodes the
  same tower as inclusions without forcing the carrier types to be subsets.
- Each field has `[TopologicalSpace] [IsTopologicalDivisionRing]`; these are the
  topologies for continuous field operations, with inversion away from zero.
  `[ContinuousSMul E F]` and `[ContinuousSMul E L]` encode the continuous E
  inclusions. This is equivalent to continuity of the algebra maps over
  topological fields, as `continuous_algebraMap_iff_smul` in
  `Mathlib.Topology.Algebra.Algebra` says. `hFL` is precisely continuity of F to L.
  No topology is required to be induced from another field.
- `p : L →L[E] F` is precisely continuous E-linearity, and `hp` says it fixes F
  after inclusion. There is no multiplicativity hypothesis on p.
- `d : ℕ` includes dimension zero. `G` has `[Group] [TopologicalSpace]
  [IsTopologicalGroup]`, and `ρ` is a monoid homomorphism to E-linear
  automorphisms of `Fin d → E`. `hρ` is joint continuity on the product.
- Finite powers are Pi types with Mathlib's product topologies. The coefficient
  and group carrier universes remain independent. The common cochain ambient
  universe is `max v w w' t`. The `HasDerivedCategory` binder is the inherited
  size interface of the recorded coordinate structure, not a field assumption.

Clause-by-clause correspondence:

- The first two conclusion formulas prescribe `ρF` and `ρL` using exactly
  `(ρ g (Pi.single b 1)) a` as the E-valued matrix entries. Thus these are the
  specified scalar-extended actions, rather than arbitrary extensions.
  Their next two `Continuous` clauses assert joint continuity. The monoid
  homomorphism codomains assert the action laws and invertible E-linearity;
  their matrix formulas also identify the usual F- and L-linear actions.
- Existential `i`, `P`, `Q` are continuous E-linear maps, not unbundled functions.
  The coordinate formulas pin i to F-inclusion and P to coordinatewise p, while
  `Q = ContinuousLinearMap.id ... - i.comp P` is exactly Q = 1 - iP.
  The next three clauses express equivariance of all three maps for the
  prescribed actions. `P.comp i = ...id` and `Q.comp i = 0` give Pi = 1, Qi = 0.
  All these existential objects are uniquely specified by the displayed
  formulas; none is a choice from an unconstrained nonempty type.
- For any realization `DF`, `DL` of the recorded coordinate complexes, the
  structure R gives `bP`, `bI`, `bQ`, `cP`, `cI`, `cQ`. Their types are morphisms
  of E-module cochain complexes: in particular their components are E-linear
  and their `comm` fields are precisely the six differential identities.
  The six `_eval` fields prescribe postcomposition with P, i, Q in every
  nonnegative degree. The dependency's evaluation ranges identify exactly
  continuous equivariant homogeneous functions and continuous inhomogeneous
  functions, so continuity and equivariance have not been replaced by arbitrary
  abstract vector spaces. Negative degrees are the dependency's zero extension.
- `b_retract`, `c_retract` assert P_* i_* = 1 in diagrammatic composition order.
  `b_complement`, `c_complement` assert Q_* = 1 - i_* P_* in both conventions.
  Each of `phi_P`, `phi_I`, `phi_Q`, `psi_P`, `psi_I`, `psi_Q` is the relevant
  square for the dependency's actual Phi/Psi cochain isomorphism arrows.
- The final quantifier is over every `H : Subgroup G`, with its existing induced
  topology and group structure. The actions are explicitly
  `ρF.comp H.subtype` and `ρL.comp H.subtype`. Their joint continuity is asserted.
  For any coordinate realizations on H, R' specifies the subgroup coefficient
  maps; `bF`, `cF`, `bL`, `cL` have evaluation formulas exactly precomposing
  every argument with inclusion. The six final equalities express commutation
  of P, i, Q with these four restriction maps, for both cochain conventions.
- `cocycle_P` and `cocycle_Q` take an arbitrary homogeneous differential-kernel
  element and assert that its projections remain in the relevant kernels.
  By the dependency's evaluation-image characterization these are exactly the
  continuous diagonally equivariant homogeneous cocycles in the node.
  `vanishing` asserts zero on every subset S whose values lie in the image of i;
  it holds for every cochain and therefore for the cocycles specified by the node.
- Degrees are all `n : ℕ`, including zero. No completeness, local compactness,
  Hausdorffness, finite-degree field extension, or characteristic assumptions
  occur. No cochain function-space topology or exponential law is used.

Dependency declarations read and used:

- `def-weil-field` is a Mathlib leaf, `Field` in
  `Mathlib.Algebra.Field.Defs`; its full signature is `class Field (K : Type u)
  extends CommRing K, DivisionRing K`.
- The recorded module
  `Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates` is a
  public import. Its `ContinuousCohomology.JointContinuousCochainCoordinates`
  supplies the B/C complexes with injective linear evaluations, their exact
  continuous-function images, the two differential formulas, and Phi/Psi.
  I read this structure and both full theorem signatures/docstrings:
  `exists_jointContinuousCochainCoordinates` and
  `jointContinuousCochainCoordinates_naturality`. The existence theorem means
  the universal realizations used here are available. The latter theorem
  supplies the naturality argument used by this node's proof.
- The proof dependency `lem-sfb-joint-continuous-coordinate-naturality` has no
  Lean or Mathlib record at the time of reading, so no module can be imported
  for it. It remains in `proof_deps` and is named in the proof docstring. Its
  statement was read in full; the parent's already recorded naturality theorem
  gives the needed interface without duplicating that statement.
- Continuous linear maps, finite Pi modules, algebra towers, and subgroup
  topology use the four explicit Mathlib public imports. In particular the
  subgroup topological-group instance in `Topology.Algebra.Group.Basic`
  confirms that every subgroup is covered, not only open or closed ones.

Sources read: the current `literature/blueprint/latest/` direct-images proof,
paragraph (3), and `literature/stacks-project/etale-cohomology.tex`, continuous
cohomology section, lines 9007--9040 (Tag 0DVG). The scalar retraction calculation
is correctly attributed to the agent expansion, not to a theorem of Stacks.
The declaration docstring carries all six node proof steps with the relevant
matrix, naturality, splitting, restriction, cocycle, and edge-case arguments.

Edge cases checked before writing: d = 0 gives empty Pi coefficient spaces;
the matrix sums are empty and all coefficients are zero. Degree zero uses the
empty inhomogeneous tuple and one homogeneous coordinate, as in the recorded
interface; its differential is gv - v. The trivial group and every subgroup,
including the trivial subgroup, are permitted. F = E and F = L are permitted;
p = identity gives Q = 0. Characteristic two preserves the alternating-sum
conventions. Non-Hausdorff topologies are permitted. Restriction does not
require an open subgroup, a compact group, or a discrete coefficient space.

Searches for an existing declaration (2026-10-24; exact wrapper output is in
sandbox searches.jsonl):

- msearch leanfinder: `A continuous linear scalar retraction induces split
  equivariant maps on continuous homogeneous and inhomogeneous cochains`.
  Eight hits, notably discrete `groupCohomology.cochainsMap`, iterated-map
  `ContinuousCohomology.homogeneousCochains`, and abstract degreewise splitting.
  None states this finite-matrix, jointly continuous scalar-retraction result.
- msearch loogle: `ContinuousLinearMap, LinearMap.pi` returned
  `ContinuousLinearMap.coe_pi`, a useful general operation, not this theorem.
- msearch grep: `scalar.*(retract|cochain)|(retract|cochain).*scalar` returned
  `RingTheory/Smooth/Kaehler.lean`, an unrelated algebraic retraction.
- msearch leansearch: `Continuous equivariant linear scalar retraction gives a
  split projection on continuous group cochain complexes` returned abstract
  splitting identities and the iterated continuous-cochain complex; no match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for finiteScalar, scalarCochain,
  ScalarCochain, scalar/retraction, and the node id found unrelated sheaf/tensor
  scalar constructions and other scalar cochain comparisons. Restricted
  RepresentationTheory searches found no such action/retraction theorem.
  A final exact-name search of the upstream name index, Mathlib representation
  theory, upstream and project sources found no collision for either new name.
  The exact node-id search in upstream also found no declaration.

Validation: `scompile.py Q88 lem-sfb-finite-scalar-cochain-retraction` compiled
this individual file both as sandbox and as its actual library module, cleanly
with no errors or unexpected warnings. The initial invalid Subgroup import was
repaired to the actual Mathlib Group.Basic module before this clean compile.
No disputed statement or mathematical fault was found.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
