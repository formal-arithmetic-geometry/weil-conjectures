## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CentralIsogenySolvableNormalLift`
states `AlgebraicGeometry.centralIsogeny_solvableNormalLift`, with its proof
postponed by `sorry`. No definitions and no proofs are introduced. The node's
statement is unchanged. Its statement dependencies gain the already landed
`def-sfb-solvable-group-structure` and `def-weil-pbc-scheme-reduction`, whose
existing definitions are used directly. No new nodes or dependency repairs.

Clause-by-clause correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe u is explicit, and `set_option autoImplicit false` forbids
  undeclared variables throughout the module.
- E and B are F-group schemes: `E B : Grp (Over (Spec (.of F)))`.
  This is the bundled form of the dependency's `GrpObj` on an F-scheme.
- Affine, finite type, smooth, connected E and B: for each X, the binders
  `[IsAffine X.X.left] [LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]`
  `[Smooth X.X.hom] [ConnectedSpace X.X.left]`.
- Homomorphism f: `f : E ⟶ B`; bundled group-object morphisms preserve
  the multiplication and unit.
- Faithful flatness of F[B] -> F[E]:
  `hff : f.hom.hom.left.appTop.hom.FaithfullyFlat`.
  This is faithful flatness of the coordinate-ring map, as specified by the
  node, rather than mere surjectivity on rational points.
- The kernel is the actual scheme-theoretic kernel:
  `CategoryTheory.GrpObj.ker f.hom.hom`; its structure morphism is finite by
  `[IsFinite (CategoryTheory.GrpObj.ker f.hom.hom).hom]`.
  Over an affine point this is exactly a finite-dimensional coordinate algebra.
- Centrality is `hcentral`, quantified over every `R : Type u` with
  `[CommRing R] [Algebra F R]`, every kernel R-point x and every E R-point g.
  The equation says the image of x commutes with g. These algebras need not be
  reduced, fields, or finite type.
- Closed normal subgroup U: `U : Grp (Over (Spec (.of F))))`, `i : U ⟶ B`,
  `[IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom]`.
  The existing definitions include injectivity and normality over every algebra.
- Smooth and connected U: `[Smooth U.X.hom] [ConnectedSpace U.X.left]`.
  No extra affineness or finite type hypothesis is needed on U: these follow
  from its closed immersion into the given affine finite type group B.
- Solvability of U: `hsolv : SolvableGroupStructure.IsSolvable U`. The landed
  definition is precisely a finite closed subnormal series with commutative
  quotients, encoded by commutator factorization on all test algebras.
- The actual inverse image P = E x_B U: the conclusion supplies a group P,
  projections p and q, and
  `IsPullback p.hom.hom q.hom.hom f.hom.hom i.hom.hom`.
  A cartesian square identifies this presentation uniquely with the canonical
  `Limits.pullback`; it is not an arbitrary subgroup or lifting map.
- The identity-component open is `C : P.X.left.Opens` satisfying
  `(C : Set P.X.left) = connectedComponent (GrpObj.onePoint P.X)`.
- The specified reduced neutral component is V with
  `e : V.X.left ≅ C.toScheme.nilradical.subscheme` and the equation
  `v.hom.hom.left = e.hom ≫ C.toScheme.nilradical.subschemeι ≫ C.ι ≫ p.hom.hom.left`.
  This fixes its inclusion in E, including its scheme structure. The reduction
  of the identity-component open of P is canonically the identity-component
  open of P_red: reduction preserves the underlying topological space and
  restricts on every open by quotienting the structure sheaf by its nilradical.
  This is the identification in step 2 of the accepted node proof, not a
  change to the statement. No arbitrary choice of a reduced closed subgroup
  can satisfy the identification unless it is the prescribed one.
- The restricted homomorphism is h with `v ≫ f = h ≫ i`. Since i is a
  subgroup inclusion, this specifies precisely the restriction to U.
- Smooth, connected, solvable, normal closed V in E:
  `Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧`
  `SolvableGroupStructure.IsSolvable V ∧`
  `IsClosedSubgroupScheme v.hom.hom ∧ IsNormalSubgroupScheme v.hom.hom`.
- Faithful flatness of the restriction:
  `h.hom.hom.left.appTop.hom.FaithfullyFlat`.
- Its finite scheme-theoretic kernel:
  `IsFinite (CategoryTheory.GrpObj.ker h.hom.hom).hom`.
- Identification of that kernel with V intersect K: there is a map a between
  the actual kernels such that
  `IsPullback (CategoryTheory.GrpObj.kerι h.hom.hom) a v.hom.hom`
  `(CategoryTheory.GrpObj.kerι f.hom.hom)`.
  This identifies the kernel, with its inclusion in V, with V x_E K, retaining
  infinitesimal structure. It is stronger than a statement only about F-points,
  but exactly the scheme-theoretic intersection in the node.
- The node's final permissions are preserved: no condition on characteristic,
  no smoothness, reducedness, or prime-to-characteristic order assumption on K,
  and no nontriviality or positive-dimension assumption on U or V.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, available through the recorded
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure module.
- `CategoryTheory.GrpObj` and `CategoryTheory.Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp; `IsMonHom` and the bundled homomorphism
  interface from Mathlib.CategoryTheory.Monoidal.Mon.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, and
  `IsNormalSubgroupScheme` in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
  Kernel construction and inclusions are `CategoryTheory.GrpObj.ker` and `kerι`
  from WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, reexported
  by that dependency. Its docstrings explicitly identify the kernel fibre product.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `ConnectedSpace`, Mathlib.Topology.Connected.Basic;
  `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `CategoryTheory.Limits.pullback` and its cartesian square interface,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
- `AlgebraicGeometry.SolvableGroupStructure.IsSolvable`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure. This is used unchanged,
  not replaced by abstract solvability of rational points.
- `Scheme.nilradical`, Mathlib.AlgebraicGeometry.IdealSheaf.Basic, and
  `Scheme.IdealSheafData.subscheme`/`subschemeι`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme.
- `GrpObj.onePoint`, WeilConjectures.AlgebraicGeometry.GroupScheme.Basic.
  Its definition uses the identity section; the identity-component open
  in this theorem is specified directly as an open with its exact carrier,
  as in the existing identity-component dependency's statement.

The module imports the recorded proof dependencies: closed immersion base
change and affine pullbacks from Mathlib; locally algebraic identity components;
geometric normality in a smooth ambient group; rational-point criterion for
faithful flatness; neutral-component translates; affine faithfully flat image;
smooth geometric reducedness; Nullstellensatz vanishing; smooth connected derived
subgroups; and affine normal quotient geometry. The Nullstellensatz node's
incomplete attachment omits its module, but its named declarations are in
WeilConjectures.Mathlib.RingTheory.Nullstellensatz, already the import used by
the rational-point and geometric-normality dependencies. No redefinition is made.
The theorem docstring gives all eight accepted proof steps and their dependencies.

Sources checked: Milne iAG2017, printed pp.17--18 (identity components, reduction
and algebraic subgroups) and pp.131--132 (Definition 6.26, Proposition 6.27,
derived series and Corollary 6.32). Read the latest blueprint direct-image proof,
clause (3), and the node's complete accepted supporting proof. The theorem is
a supporting synthesis, not a replacement of the blueprint unit's statement.

Edge cases checked before writing:

- U = 1, including a nonreduced central kernel such as mu_p in Frobenius on G_m.
  The inverse image may be nonreduced; its reduced identity component is still
  specified by nilradical reduction. No smoothness assumption on P appears.
- The identity homomorphism: the construction recovers the given smooth
  connected U and h is an isomorphism.
- Positive characteristic Frobenius on G_m with U = G_m, and a prime-to-p
  power isogeny: both are allowed by all binders; the kernel may be infinitesimal
  or disconnected respectively.
- The trivial E, B, and U, and a solvable series of length zero: no exclusion.
- Characteristic zero and positive characteristic are both allowed.
- Empty schemes cannot accidentally count as connected: ConnectedSpace includes
  nonemptiness, and the group identity already supplies a point.
- Normality and centrality test nonreduced algebras, so the statement does not
  discard infinitesimal scheme structure. The kernel conclusion uses a
  cartesian square rather than equality of rational-point subgroups.

Searches made before writing:

- msearch.py leanfinder: "The reduced identity component of the inverse image
  of a smooth connected solvable normal subgroup under a faithfully flat central
  isogeny is solvable normal and surjects with finite kernel". Eight hits on
  abstract solvable groups and Lie algebras (solvable_of_surjective,
  solvable_of_ker_le_range, IsSolvable, etc.); none states this scheme result.
- msearch.py loogle: "IsSolvable, GrpObj.ker, pullback". Zero hits; the index
  reports GrpObj.ker unknown, so local source inspection supplied that interface.
- msearch.py grep: "solvable.*(isogen|preimage)|reduced.*identity.*component|central.*isogen"
  in Mathlib/AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for solvability, central isogenies,
  reductions and identity components found the reusable definitions and
  supporting lemmas listed above, but no statement of this result. In particular,
  SemisimpleCentralIsogenyMultiplicative concerns finite diagonalizable kernels,
  and ClosedSubgroupReducedComponent concerns a different ambient-group result.
- rg of the exact node id in lean/WeilConjectures found no match.
- rg of centralIsogeny_solvableNormalLift in Mathlib, WeilConjectures, Sheaf,
  and dag/lean_names_upstream.json found no existing declaration.

Validation: scompile.py compiled the module in both its sandbox and library
module names with no errors or warnings. All writes are in the assigned sandbox.
No statement dispute or source fault was found.

## Second reading by N0

The dispatcher explicitly prohibits starting other agents; no independent
second reader was started or claimed. I reread the node against the complete
signature after the first clean compile. The maintainer's independent review
remains the independent reading of this delivery.

The rereading checked each of the correspondences above against the actual
binders and conjunctions. In particular, hcentral quantifies over all commutative
algebras; no rational-point centrality substitutes for it. P is fixed by an
actual pullback square, not an arbitrary group with a map. V is identified with
the nilradical reduction of the exact connected-component open, including its
inclusion. The restriction equation is over B; the final kernel square is over E.
These together fix both canonical maps up to their universal isomorphisms.
The use of (P^0)_red in place of (P_red)^0 is the canonical identification
explicitly required and justified in the accepted proof step 2, and does not
lose the scheme structure. No new hypothesis or conclusion was introduced.
Added explicit public imports for the recorded smoothness, finite type,
quasi-compactness, and algebraic-closure dependency modules before final validation.
